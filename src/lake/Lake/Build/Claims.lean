/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

prelude
public import Lake.Build.Key
public import Std.Data.HashMap.Basic
public import Std.Data.TreeMap.Basic
public import Init.System.Promise
public import Init.Data.Hashable

/-! # Build Key Claims

Bookkeeping that lets several threads fetch from one build store at once while computing
each build key exactly once (see `fetchOrCreateOnce`).
-/

namespace Lake

/-- The computation of a build key that some thread has started. -/
public structure Claim where
  /-- The thread computing the key. -/
  owner : UInt64
  /-- Resolved with `true` once the key's job is in the store, or `false` if computing it threw. -/
  done : IO.Promise Bool

/-- Which thread computes each claimed build key, and which key each blocked thread waits for. -/
public structure ClaimTable where
  claims : Std.TreeMap BuildKey Claim BuildKey.quickCmp := {}
  waiting : Std.HashMap UInt64 BuildKey := {}

/--
Follows the waits-for chain that starts at the thread computing `key`. Returns the keys along
the chain if it leads back to the thread `me` (so `me` waiting for `key` would deadlock), or
`none` if the chain ends at a thread that is still running.
-/
public def ClaimTable.cycle? (t : ClaimTable) (me : UInt64) (key : BuildKey) : Option (List BuildKey) :=
  go key [key] (t.waiting.size + 1)
where
  go (key : BuildKey) (path : List BuildKey) : Nat → Option (List BuildKey)
    | 0 => none
    | fuel + 1 =>
      match t.claims.get? key with
      | none => none
      | some c =>
        if c.owner == me then
          some path.reverse
        else
          match t.waiting[c.owner]? with
          | none => none
          | some next => go next (next :: path) fuel

end Lake
