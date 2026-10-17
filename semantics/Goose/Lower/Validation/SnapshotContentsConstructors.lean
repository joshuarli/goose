import Goose.Lower.Validation.SnapshotContentsCapture

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SnapshotSourceTrace.snapshot_after_place
    {env : Core.TEnv} {results : List Ty} {place : Place} {info : PlaceInfo}
    {start finish first : Nat} {before ownerState after : LS} {owner snapshot : ValueId}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (generated : GeneratedBuilderState before)
    (placeRun : lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, ownerState))
    (trace : SnapshotSourceTrace (lowerEnv env.mod env.vars results) first ownerState ownerState)
    (fresh : first ≤ before.vals.size) (mode : SnapshotMode)
    (run : Goose.Lower.emitDef (.snapshot mode owner) (lowerEnv env.mod env.vars results) ownerState = (snapshot, after)) :
    SnapshotSourceTrace (lowerEnv env.mod env.vars results) first after after := by
  cases current : ownerState.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact trace
  | some block =>
    let site : SnapshotSourceSite (lowerEnv env.mod env.vars results) snapshot mode owner :=
      { typingEnv := env, results := results, place := place, info := info,
        start := start, finish := finish, beforePlace := before, ownerState := ownerState,
        emittedState := after, aligned := rfl, typed := source, generated := generated,
        lowered := placeRun, live := by simp [current], emitted := run }
    exact trace.capture site fresh

theorem SnapshotSourceTrace.lowerView_of
    {env : Core.TEnv} {results : List Ty} {place : Place} {info : PlaceInfo}
    {start finish first : Nat} {before ownerState after : LS} {owner snapshot : ValueId}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (generated : GeneratedBuilderState before)
    (placeRun : lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, ownerState))
    (trace : SnapshotSourceTrace (lowerEnv env.mod env.vars results) first ownerState ownerState)
    (fresh : first ≤ before.vals.size)
    (run : lowerView (.of place) (lowerEnv env.mod env.vars results) before = (snapshot, after)) :
    SnapshotSourceTrace (lowerEnv env.mod env.vars results) first after after := by
  apply trace.snapshot_after_place (snapshot := snapshot) source generated placeRun fresh
    ((fun p : Place => match p with | .var _ | .global _ => SnapshotMode.owner | _ => .borrowed) place)
  cases place <;> simpa only [lowerView, bind, placeRun] using run

theorem SnapshotSourceTrace.lowerEachSource_of
    {env : Core.TEnv} {results : List Ty} {place : Place} {info : PlaceInfo}
    {start finish first : Nat} {before ownerState after : LS} {owner : ValueId}
    {result : Option ValueId × ValueId}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (generated : GeneratedBuilderState before)
    (placeRun : lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, ownerState))
    (trace : SnapshotSourceTrace (lowerEnv env.mod env.vars results) first ownerState ownerState)
    (fresh : first ≤ before.vals.size)
    (run : lowerEachSource (.of place) (lowerEnv env.mod env.vars results) before = (result, after)) :
    SnapshotSourceTrace (lowerEnv env.mod env.vars results) first after after := by
  let mode := match place with | .var _ | .global _ => SnapshotMode.owner | _ => .borrowed
  generalize emission : Goose.Lower.emitDef (.snapshot mode owner)
    (lowerEnv env.mod env.vars results) ownerState = emitted at *
  obtain ⟨snapshot, state⟩ := emitted
  have outcome : ((some owner, snapshot), state) = (result, after) := by
    simp only [lowerEachSource, bind, placeRun, pure] at run
    change ((some owner, (Goose.Lower.emitDef (.snapshot mode owner)
      (lowerEnv env.mod env.vars results) ownerState).1),
      (Goose.Lower.emitDef (.snapshot mode owner)
      (lowerEnv env.mod env.vars results) ownerState).2) = (result, after) at run
    rw [emission] at run
    exact run
  obtain ⟨_, rfl⟩ := Prod.mk.inj outcome
  exact trace.snapshot_after_place source generated placeRun fresh mode emission

end Goose.Lower.Validation
