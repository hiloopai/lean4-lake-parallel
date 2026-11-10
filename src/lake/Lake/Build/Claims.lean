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

/--
Which thread computes each claimed build key, and, for each blocked thread, the key it waits for
and its call stack at the time.
-/
public structure ClaimTable where
  claims : Std.TreeMap BuildKey Claim BuildKey.quickCmp := {}
  waiting : Std.HashMap UInt64 (BuildKey × List BuildKey) := {}
  /-- How many more fetches `prefetchConcurrently` may run in tasks of their own. -/
  slots : Nat

/--
Whether the thread `me`, with call stack `stack`, waiting for `key` would deadlock: that is,
whether the waits-for chain that starts at the thread computing `key` leads back to `me`.
If so, returns the cycle as a call stack (most recent call first), like `guardCycle`.
-/
public def ClaimTable.cycle? (t : ClaimTable) (me : UInt64) (stack : List BuildKey)
  (key : BuildKey) : Option (List BuildKey)
:= go key [] (t.waiting.size + 1)
where
  /-- The calls of `stack` from its most recent one down to `key`. -/
  segment (stack : List BuildKey) (key : BuildKey) : List BuildKey :=
    stack.takeWhile (· != key) ++ [key]
  /-- `segs` holds the stack segments of the threads passed so far, the most recent first. -/
  go (key : BuildKey) (segs : List (List BuildKey)) : Nat → Option (List BuildKey)
    | 0 => none
    | fuel + 1 =>
      match t.claims.get? key with
      | none => none
      | some c =>
        if c.owner == me then
          -- `me` waits for the first key `k₁`, whose owner waits for `k₂`, ..., whose owner is `me`.
          -- Each key is needed by the call after it: the first owner's segment ends at `k₁`,
          -- which `me` needs; `me`'s segment ends at the last key, which the last owner needs.
          let first := segs.getLast?.getD []
          let cycle := first ++ segment stack key ++ segs.dropLast.flatten
          some (cycle ++ cycle.take 1)
        else
          match t.waiting[c.owner]? with
          | none => none
          | some (next, ownerStack) => go next (segment ownerStack key :: segs) fuel

end Lake
