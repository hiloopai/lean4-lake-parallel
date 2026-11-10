/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Info
public import Lake.Build.Store
public import Lake.Build.Context
public import Lake.Config.Module
public import Lake.Util.EquipT
public import Lake.Util.Cycle
import Lake.Build.Infos

/-! # Recursive Building

This module defines Lake's top-level build monad, `FetchM`, used
for performing recursive builds. A recursive build is a build function
which can fetch the results of other (recursive) builds. This is done
using the `fetch` function defined in this module.
-/

namespace Lake

/-- A type alias for `Option Package` that assists monad type class synthesis. -/
public abbrev CurrPackage := Option Package

/-- Run the action `x` with `pkg?` as the current package or no package if `none`. -/
@[inline] public def withCurrPackage? [MonadWithReader CurrPackage m] (pkg? : Option Package) (x : m α): m α :=
  withReader (fun _ => pkg?) x

/-- Run the action `x` with `pkg` as the current package. -/
@[inline] public def withCurrPackage [MonadWithReader CurrPackage m] (pkg : Package) (x : m α): m α :=
  withCurrPackage? pkg x

/-- Get the package of the context (if any). -/
@[inline] public def getCurrPackage? [MonadReaderOf CurrPackage m] : m (Option Package) := read

/--
A recursive build of a Lake build store that may encounter a cycle.

An internal monad. **Not intended for user use.**
-/
public abbrev RecBuildT (m : Type → Type) :=
  ReaderT CurrPackage <| CallStackT BuildKey <| StateRefT' IO.RealWorld BuildStore <| BuildT m

/-- Build cycle error message. -/
public def buildCycleError (cycle : Cycle BuildKey) : String :=
  s!"build cycle detected:\n{formatCycle cycle}"

public instance [Monad m] [MonadError m] : MonadCycleOf BuildKey (RecBuildT m) where
  throwCycle cycle := error (buildCycleError cycle)

/--
A recursive build of a Lake build store that may encounter a cycle.

An internal monad. **Not intended for user use.**
-/
public abbrev RecBuildM := RecBuildT LogIO

/-- Run a recursive build. -/
@[inline] public def RecBuildT.run
  [Monad m] [MonadLiftT (ST IO.RealWorld) m]
  (stack : CallStack BuildKey) (store : BuildStore) (build : RecBuildT m α)
: BuildT m (α × BuildStore) := build none stack |>.run store

/-- Run a recursive build in a fresh build store. -/
@[inline] public def RecBuildT.run'
  [Monad m] [MonadLiftT (ST IO.RealWorld) m] (build : RecBuildT m α)
: BuildT m α := (·.1) <$> build.run {} {}

/-- A build function for any element of the Lake build index. -/
public abbrev IndexBuildFn (m : Type → Type v) :=
  -- `DFetchFn BuildInfo (Job <| BuildData ·.key) m` with less imports
  (info : BuildInfo) → m (Job (BuildData info.key))

/-- A transformer to equip a monad with a build function for the Lake index. -/
public abbrev IndexT (m : Type → Type v) := EquipT (IndexBuildFn RecBuildM) m

/-- The top-level monad transformer for Lake build functions. -/
public abbrev FetchT (m : Type → Type) := IndexT <| RecBuildT m

/-- The top-level monad for Lake build functions. -/
public abbrev FetchM := FetchT LogIO

/-- Construct a `FetchM` monad from its full functional representation. -/
@[inline] public def FetchM.ofFn
  (f : IndexBuildFn RecBuildM → Option Package → CallStack BuildKey →
    IO.Ref BuildStore → BuildContext → Log → BaseIO (EResult Log.Pos Log α))
: FetchM α := .mk fun fetch => fun pkg? stack store ctx => .mk fun log =>
  f fetch pkg? stack store ctx log

/-- Convert a `FetchM` monad to its full functional representation. -/
@[inline] public def FetchM.toFn (self : FetchM α) :
  IndexBuildFn RecBuildM → Option Package → CallStack BuildKey →
    IO.Ref BuildStore → BuildContext → Log → BaseIO (EResult Log.Pos Log α)
:= fun fetch pkg? stack store ctx log => self.run fetch pkg? stack store ctx |>.run log

/--
Returns the job of `key` from the build store, computing it with `compute` if absent.

Safe under concurrent fetches: the first fetcher claims `key` and computes it, while concurrent
fetchers of `key` wait for that computation, so each key is computed exactly once. A wait that
would close a cycle through concurrent fetches fails with a build cycle error instead.
If `compute` throws, the claim is released, so a later fetch computes `key` again
(as a sequential fetch would).
-/
public partial def fetchOrCreateOnce
  (key : BuildKey) (compute : FetchM (Job (BuildData key)))
: FetchM (Job (BuildData key)) := .ofFn fun fetch pkg? stack store ctx log => do
  if let some job := (← store.get).get? key then
    return .ok job log
  let me ← IO.getTID
  let done ← IO.Promise.new
  let prior? ← ctx.claims.modifyGet fun t =>
    match t.claims.get? key with
    | some c => (some c, t)
    | none => (none, {t with claims := t.claims.insert key {owner := me, done}})
  match prior? with
  | none =>
    match (← compute.toFn fetch pkg? stack store ctx log) with
    | .ok job log =>
      store.modify (·.insert key job)
      done.resolve true
      return .ok job log
    | .error e log =>
      ctx.claims.modify fun t => {t with claims := t.claims.erase key}
      done.resolve false
      return .error e log
  | some c =>
    unless (← IO.hasFinished c.done.result?) do
      let cycle? ← ctx.claims.modifyGet fun t =>
        match t.cycle? me stack key with
        | some cycle => (some cycle, t)
        | none => (none, {t with waiting := t.waiting.insert me (key, stack)})
      if let some cycle := cycle? then
        return .error log.endPos (log.push (.error (buildCycleError cycle)))
      discard <| IO.wait c.done.result?
      ctx.claims.modify fun t => {t with waiting := t.waiting.erase me}
    if let some job := (← store.get).get? key then
      return .ok job log
    else
      (fetchOrCreateOnce key compute).toFn fetch pkg? stack store ctx log

/--
Runs the fetches of `xs` concurrently and waits for them, so that the same fetches made afterwards
in order find their results in the build store. Each fetch is paired with the build key it
produces (see `fetchOrCreateOnce`); one whose key is already in the store is skipped.
The logs of fetches that succeed are kept in order. A fetch that fails leaves nothing behind:
its key is released, so the ordered fetch computes it again and reports the failure in place.
-/
public def prefetchConcurrently (xs : Array (BuildKey × FetchM α)) : FetchM Unit :=
  .ofFn fun fetch pkg? stack store ctx log => do
  let snap ← store.get
  let claimed := (← ctx.claims.get).claims
  let xs := xs.filter fun (key, _) => !snap.contains key && !claimed.contains key
  if xs.size ≤ 1 then
    return .ok () log
  let tasks ← xs.mapM fun (key, x) => do
    return (key, ← BaseIO.asTask (x.toFn fetch pkg? stack store ctx {}))
  let me ← IO.getTID
  let mut log := log
  for (key, task) in tasks do
    unless (← IO.hasFinished task) do
      let cycle? ← ctx.claims.modifyGet fun t =>
        match t.cycle? me stack key with
        | some cycle => (some cycle, t)
        | none => (none, {t with waiting := t.waiting.insert me (key, stack)})
      if let some cycle := cycle? then
        return .error log.endPos (log.push (.error (buildCycleError cycle)))
      discard <| IO.wait task
      ctx.claims.modify fun t => {t with waiting := t.waiting.erase me}
    if let .ok _ l := task.get then
      log := log ++ l
  return .ok () log

/-- Fetch the result associated with the info using the Lake build index. -/
@[inline] public def BuildInfo.fetch (self : BuildInfo) [FamilyOut BuildData self.key α] : FetchM (Job α) :=
  .mk fun build => cast (by simp) <| build self

export BuildInfo (fetch)

/-- Fetch the result of this facet of a module. -/
public protected def ModuleFacet.fetch (self : ModuleFacet α) (mod : Module) : FetchM (Job α) :=
  fetch <| mod.facetCore self.name
