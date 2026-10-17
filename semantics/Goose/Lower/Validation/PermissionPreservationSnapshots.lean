import Goose.Lower.Validation.PermissionPreservationNewEmit
import Goose.Lower.Validation.SnapshotContentsFinal

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SnapshotSourceSite.freshSnapshotContents {le : LEnv} {snapshot owner : ValueId} {mode : SnapshotMode}
    {after : LS} {element : Ty} (site : SnapshotSourceSite le snapshot mode owner)
    (types : TypePrefix site.emittedState after)
    (recorded : after.vals[snapshot]? = some (some (.view .mutable element))) :
    FreshContentsEvidence le site.beforePlace.vals.size site.emittedState snapshot := by
  have evidence := site.freshContents types recorded
  have ownerLive := site.live
  cases live : site.ownerState.cur with
  | none => simp [live] at ownerLive
  | some current =>
    exact evidence.emitDef_dependency site.ownerGenerated.dense site.ownerGenerated.live live site.emitted
      (fun _ permitted => permitted)

theorem SnapshotSourceSite.permissionInstruction {le : LEnv} {snapshot owner : ValueId} {mode : SnapshotMode}
    {module : GIR.Module} {func : Func} (site : SnapshotSourceSite le snapshot mode owner) :
    FreshPermissionInstruction module func le site.beforePlace.vals.size site.emittedState
      (.def snapshot (.snapshot mode owner)) := by
  constructor
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a mutation; cases mutation
    · intro a b impossible; cases impossible
    · intro a b c impossible; cases impossible
    · intro value actualMode actualOwner element shape typed
      cases shape
      exact site.freshSnapshotContents (fun _ _ row => row) typed
    · intro a b c d e impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b impossible; cases impossible
  · constructor
    · intro a b c impossible; cases impossible
    · intro value actualMode actualOwner shape
      cases shape
      exact ⟨_, snapshot_emit_recorded site.live site.emitted⟩

theorem SnapshotSourceSite.newPermissionInstructions {le : LEnv}
    {snapshot owner : ValueId} {mode : SnapshotMode} {module : GIR.Module} {func : Func} {first : Nat}
    (site : SnapshotSourceSite le snapshot mode owner)
    (prior : NewPermissionInstructions module func le first site.beforePlace site.ownerState)
    (firstBound : first ≤ site.beforePlace.vals.size) :
    NewPermissionInstructions module func le first site.beforePlace site.emittedState := by
  have issued := NewPermissionInstructions.emitDef (module := module) (func := func) site.emitted
    (fun _ => site.permissionInstruction.weaken firstBound)
  apply prior.compose issued
  intro instruction member permitted
  have generated := site.ownerGenerated
  have advanced := advB_emitDef (.snapshot mode owner) le _ _ _ site.emitted
  have framed := (generatedTargetFrame_emitDef none (.snapshot mode owner)
    site.ownerState le site.ownerState snapshot site.emittedState (.refl _) trivial
    (.refl none site.ownerState) site.emitted).1
  exact permitted.retained (loop := none) generated.dense (generated.emitDef _ site.emitted).dense
    advanced.ext advanced.vals (types_emitDef _ le _ _ _ site.emitted) trivial framed

theorem lowerView_of_newPermissionInstructions (place : Place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    {module : GIR.Module} {func : Func}
    (run : lowerView (.of place) (lowerEnv env.mod env.vars results) before = (value, after))
    (generated : GeneratedBuilderState before)
    (child : ∀ owner middle,
      lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, middle) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results)
        before.vals.size before middle) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results)
      before.vals.size before after := by
  have lowering := run
  simp only [lowerView] at lowering
  obtain ⟨owner, middle, placeRun, emitted⟩ := bind_eq.mp lowering
  have prior := child owner middle placeRun
  have middleGenerated := generated.lowerPlace place placeRun
  have issued := NewPermissionInstructions.emitDef (module := module) (func := func)
    (first := before.vals.size) emitted (fun live => by
      let site : SnapshotSourceSite (lowerEnv env.mod env.vars results) value _ owner :=
        { typingEnv := env, results := results, place := place, info := info, start := start, finish := finish,
          beforePlace := before, ownerState := middle, emittedState := after, aligned := rfl,
          typed := source, generated := generated, lowered := placeRun, live := live, emitted := emitted }
      exact site.permissionInstruction)
  apply prior.compose issued
  intro instruction member permitted
  have advanced := advB_emitDef _ _ _ _ _ emitted
  have framed := (generatedTargetFrame_emitDef none _
    middle _ middle value after (.refl _) trivial (.refl none middle) emitted).1
  exact permitted.retained (loop := none) middleGenerated.dense
    (middleGenerated.emitDef _ emitted).dense advanced.ext advanced.vals
    (types_emitDef _ _ _ _ _ emitted) trivial framed

#print axioms lowerView_of_newPermissionInstructions

#print axioms SnapshotSourceSite.newPermissionInstructions

#print axioms SnapshotSourceSite.permissionInstruction

#print axioms SnapshotSourceSite.freshSnapshotContents

end Goose.Lower.Validation
