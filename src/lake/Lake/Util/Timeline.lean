/-
Instrumentation for measuring Lake's no-op build (not for upstream).
Enabled by setting `LAKE_TIMELINE` to an output path.
-/
module

prelude
public import Init.System.IO
public import Init.Data.ToString
public import Init.Data.String
public import Init.Data.Array

namespace Lake.Timeline

public builtin_initialize enabled : Bool ← (·.isSome) <$> IO.getEnv "LAKE_TIMELINE"
public builtin_initialize marks : IO.Ref (Array (String × Nat)) ← do
  IO.mkRef #[("init", ← IO.monoNanosNow)]
public builtin_initialize regs : IO.Ref (Array (Nat × String)) ← IO.mkRef #[]
public builtin_initialize finishes : IO.Ref (Array Nat) ← IO.mkRef #[]
public builtin_initialize waits : IO.Ref (Array (UInt64 × Nat × Nat)) ← IO.mkRef #[]
public builtin_initialize fetchCount : IO.Ref Nat ← IO.mkRef 0
public builtin_initialize computes : IO.Ref Nat ← IO.mkRef 0

public def mark (name : String) : BaseIO Unit := do
  if enabled then
    let t ← IO.monoNanosNow
    marks.modify (·.push (name, t))

public def onRegister (caption : String) (task : Task α) : BaseIO Unit := do
  if enabled then
    let t ← IO.monoNanosNow
    regs.modify (·.push (t, caption))
    discard <| BaseIO.mapTask (t := task) (sync := true) fun _ => do
      let t ← IO.monoNanosNow
      finishes.modify (·.push t)

public def timedWait (t : Task α) : BaseIO α := do
  if enabled then
    if ← IO.hasFinished t then return t.get
    let s ← IO.monoNanosNow
    let r ← IO.wait t
    let e ← IO.monoNanosNow
    let tid ← IO.getTID
    waits.modify (·.push (tid, s, e - s))
    return r
  else
    IO.wait t

public def countFetch : BaseIO Unit := do
  if enabled then
    fetchCount.modify (· + 1)

public def countCompute : BaseIO Unit := do
  if enabled then
    computes.modify (· + 1)

public def dump : BaseIO Unit := do
  let some path ← IO.getEnv "LAKE_TIMELINE" | return
  let mut out := ""
  for (n, t) in ← marks.get do
    out := out ++ s!"mark {t} {n}\n"
  for (t, c) in ← regs.get do
    out := out ++ s!"reg {t} {c}\n"
  for t in ← finishes.get do
    out := out ++ s!"fin {t}\n"
  for (tid, s, d) in ← waits.get do
    out := out ++ s!"wait {tid} {s} {d}\n"
  out := out ++ s!"fetches {← fetchCount.get}\n"
  out := out ++ s!"computes {← computes.get}\n"
  (IO.FS.writeFile path out).catchExceptions fun _ => pure ()

end Lake.Timeline
