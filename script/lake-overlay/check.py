"""Select, test and check the Lake overlay against the release toolchain it overlays.

  check.py select PREFIX BUILD OUT        copy the built Lake files that differ from PREFIX's into OUT
  check.py tests RELEASE OVERLAY LOGS     tests/lake under both toolchains: exit codes must match
  check.py sound RELEASE OVERLAY WORK LOGS
      the same edits built by both toolchains' Lake in copies of WORK (as `build.sh` left it):
      exit codes, job counts, built modules and every trace must match. A stock-vs-stock
      control must match too, or the check itself is broken.
"""

import concurrent.futures
import filecmp
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
# Every file a toolchain carries for Lake. Lake's own build also writes traces and hashes there.
LAKE_LIB = re.compile(r"lib/lean/(?:Lake(?:Main)?|Lake/.+)\.(?:olean|olean\.private|olean\.server|ilean|ir|ir\.sig)")
LAKE_BIN = {"bin/lake", "lib/lean/libLake.a", "lib/lean/libLake_shared.so"}
SKIP_TESTS = re.compile(r"lake-packages|bootstrap|toolchain|online")


def lake_files(root: Path) -> set[str]:
    found = set()
    for path in (root / "lib/lean").rglob("*"):
        rel = path.relative_to(root).as_posix()
        if path.is_file() and (LAKE_LIB.fullmatch(rel) or rel in LAKE_BIN):
            found.add(rel)
    if (root / "bin/lake").is_file():
        found.add("bin/lake")
    return found


def select(prefix: Path, build: Path, out: Path) -> None:
    release, built = lake_files(prefix), lake_files(build)
    if release - built or built - release:
        sys.exit(f"file sets differ: missing {sorted(release - built)[:20]}, extra {sorted(built - release)[:20]}")
    changed = {rel: build / rel for rel in release if not filecmp.cmp(prefix / rel, build / rel, shallow=False)}
    # The toolchain also ships Lake's sources, which its `.ilean` files point into.
    sources = REPO / "src/lake"
    shipped = {p.relative_to(prefix / "src/lean/lake").as_posix() for p in (prefix / "src/lean/lake").rglob("*.lean")}
    ours = {p.relative_to(sources).as_posix() for p in sources.rglob("*.lean")}
    if shipped != ours:
        sys.exit(f"Lake sources differ in name: {sorted(shipped ^ ours)[:20]}")
    for rel in sorted(ours):
        if not filecmp.cmp(prefix / "src/lean/lake" / rel, sources / rel, shallow=False):
            changed[f"src/lean/lake/{rel}"] = sources / rel
    for rel, source in changed.items():
        (out / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, out / rel)
    size = sum((out / rel).stat().st_size for rel in changed)
    print(f"{len(changed)} Lake files differ from the release ({size} bytes)")
    print("\n".join(sorted(changed)))


def toolchain_env(prefix: Path, home: Path) -> dict[str, str]:
    home.mkdir(parents=True, exist_ok=True)
    return dict(
        os.environ,
        PATH=f"{prefix}/bin:{os.environ['PATH']}",
        LAKE=str(prefix / "bin/lake"),
        HOME=str(home),
        XDG_CACHE_HOME=str(home / ".cache"),
        ELAN="false",
        LAKE_ARTIFACT_CACHE="false",
        GIT_AUTHOR_NAME="test",
        GIT_AUTHOR_EMAIL="test@example.invalid",
        GIT_COMMITTER_NAME="test",
        GIT_COMMITTER_EMAIL="test@example.invalid",
    )


def tests(release: Path, overlay: Path, logs: Path) -> None:
    lake_tests = REPO / "tests/lake"
    names = sorted(
        p.parent.relative_to(lake_tests).as_posix()
        for group in ("tests", "examples")
        for p in (lake_tests / group).glob("*/test.sh")
        if not SKIP_TESTS.search(p.parent.name)
    )
    scratch = Path(tempfile.mkdtemp(prefix="lake-tests-"))
    roots = {}
    for variant in ("release", "overlay"):
        root = scratch / variant
        shutil.copytree(REPO / "tests/lake", root / "tests/lake", symlinks=True)
        shutil.copytree(REPO / "src/lake", root / "src/lake", symlinks=True)
        roots[variant] = root

    def run(variant: str, name: str) -> tuple[str, str, int]:
        prefix = release if variant == "release" else overlay
        env = toolchain_env(prefix, scratch / "home" / variant / name.replace("/", "-"))
        with open(logs / f"test-{variant}-{name.replace('/', '-')}.log", "wb") as log:
            code = subprocess.run(
                ["timeout", "900", "bash", "run_test.sh", name],
                cwd=roots[variant] / "tests/lake", env=env, stdout=log, stderr=subprocess.STDOUT,
            ).returncode
        return variant, name, code

    def both(name: str) -> tuple[str, dict[str, int]]:
        # One toolchain after the other: some tests bind fixed ports.
        return name, {variant: run(variant, name)[2] for variant in roots}

    with concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count() or 2) as pool:
        codes = dict(pool.map(both, names))
    mismatch = {name: c for name, c in codes.items() if c["release"] != c["overlay"]}
    failing = sorted(name for name, c in codes.items() if c["release"] != 0)
    (logs / "tests.json").write_text(json.dumps({"codes": codes, "mismatch": mismatch}, indent=1))
    print(f"{len(names)} tests; failing under both toolchains: {failing}")
    if mismatch:
        sys.exit(f"exit codes differ: {mismatch}")


M1 = "src/lake/Lake/Load/Resolve.lean"
M2 = "src/lake/Lake/Load/Lean/Eval.lean"
STEPS = [
    ("noop", None),
    ("private-theorem", (M1, "\nprivate theorem lakeOverlayEdit1 : (1 : Nat) + 1 = 2 := rfl\n")),
    ("public-theorem", (M2, "\npublic theorem lakeOverlayEdit2 : (2 : Nat) + 2 = 4 := rfl\n")),
    ("changed-statement", (M2, "\npublic theorem lakeOverlayEdit2 : (2 : Nat) + 3 = 5 := rfl\n")),
    ("revert", None),
]


def strip_times(value):
    if isinstance(value, dict):
        return {k: strip_times(v) for k, v in value.items() if "time" not in k.lower()}
    if isinstance(value, list):
        return [strip_times(v) for v in value]
    return value


def traces(tree: Path, paths: dict[str, str]) -> dict[str, str]:
    """Each trace's hash, with `paths` (longest first) replaced and timings dropped."""
    out = {}
    for path in (tree / "pkg/.lake").rglob("*.trace"):
        data = path.read_bytes()
        for old in sorted(paths, key=len, reverse=True):
            data = data.replace(old.encode(), paths[old].encode())
        try:
            data = json.dumps(strip_times(json.loads(data)), sort_keys=True).encode()
        except ValueError:
            pass
        out[path.relative_to(tree).as_posix()] = hashlib.sha256(data).hexdigest()
    return out


def sound(release: Path, overlay: Path, work: Path, logs: Path) -> None:
    trees = {"stock": work, "control": work.with_name(f"{work.name}-control"), "overlay": work.with_name(f"{work.name}-overlay")}
    for name in ("control", "overlay"):
        shutil.copytree(work, trees[name], symlinks=True)
    # Copies keep traces that name the tree they were built in, and toolchain paths differ.
    paths = {str(t): "<TREE>" for t in trees.values()} | {str(release): "<LEAN>", str(overlay): "<LEAN>"}
    original = {f: (work / f).read_text() for f in (M1, M2)}
    results: dict[str, list[dict]] = {}
    for name, tree in trees.items():
        prefix = overlay if name == "overlay" else release
        env = toolchain_env(prefix, tree.with_name(f"{tree.name}-home"))
        rows = []
        for step, edit in STEPS:
            if edit:
                (tree / edit[0]).write_text(original[edit[0]] + edit[1])
            if step == "revert":
                for f, text in original.items():
                    (tree / f).write_text(text)
            p = subprocess.run(["lake", "build"], cwd=tree / "pkg", env=env, capture_output=True, text=True)
            output = p.stdout + p.stderr
            (logs / f"sound-{name}-{step}.log").write_text(output)
            jobs = re.findall(r"\((\d+) jobs\)", output)
            rows.append({
                "step": step, "exit": p.returncode, "jobs": jobs[-1] if jobs else None,
                "built": sorted(set(re.findall(r"\] (?:Built|Building|Replayed|Unpacked|Fetched) (\S+)", output))),
                "traces": traces(tree, paths),
            })
            print(json.dumps({"tree": name, "step": step, "exit": p.returncode, "jobs": rows[-1]["jobs"],
                              "built": len(rows[-1]["built"]), "traces": len(rows[-1]["traces"])}), flush=True)
        results[name] = rows
    stock = {row["step"]: row for row in results["stock"]}
    if stock["noop"]["built"] or not stock["public-theorem"]["built"]:
        sys.exit("the edits did not exercise the build")
    summary, failed = [], False
    for other in ("control", "overlay"):
        for a, b in zip(results["stock"], results[other]):
            diff = sorted(k for k in a["traces"].keys() | b["traces"].keys() if a["traces"].get(k) != b["traces"].get(k))
            row = {"pair": f"stock-{other}", "step": a["step"], "exit": [a["exit"], b["exit"]],
                   "jobs": [a["jobs"], b["jobs"]], "built": len(a["built"]), "built_equal": a["built"] == b["built"],
                   "traces": len(a["traces"]), "trace_diffs": diff[:20]}
            failed |= a["exit"] != b["exit"] or a["jobs"] != b["jobs"] or not row["built_equal"] or bool(diff)
            summary.append(row)
            print(json.dumps(row))
    (logs / "sound.json").write_text(json.dumps(summary, indent=1))
    if failed:
        sys.exit("stock and overlay builds differ")


if __name__ == "__main__":
    command, *args = sys.argv[1:]
    {"select": select, "tests": tests, "sound": sound}[command](*map(Path, args))
