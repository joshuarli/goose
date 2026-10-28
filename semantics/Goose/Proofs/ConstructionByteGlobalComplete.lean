import Goose.Proofs.ConstructionByteGlobalInitialStopped
import Goose.Proofs.ConstructionByteGlobalLocal

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem initGlobals_byteOwners_positive_complete (fuel initialized count : Nat) (config : EvalConfig)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (bound : initialized + count ≤ config.module.globals.size)
    (declarations : ∀ id, initialized ≤ id → id < initialized + count →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before) :
    ∃ completed nextLive regions,
      let outcome := initGlobals (fuel + 1) config (List.range' initialized count) before
      let after := Goose.Proofs.Exit.stepState outcome
      initialized ≤ completed ∧ completed ≤ initialized + count ∧
      AcceptedWorld config completed after ambient types nextLive regions [] ∧
      (match outcome with
       | .ok _ _ => completed = initialized + count ∧ regions = [] ∧ FutureGlobalsClear config completed after
       | .stop _ _ => completed < initialized + count
       | .escape .. | .jump .. => False) := by
  have localAction := initGlobals_byteOwners_local count fuel initialized config declarations before
  cases outcome : initGlobals (fuel + 1) config (List.range' initialized count) before with
  | ok value after =>
    cases value
    obtain ⟨nextLive, finalWorld, finalClear⟩ :=
      initGlobals_byteOwners count fuel initialized config before after ambient types live bound declarations world clear outcome
    simp only [Goose.Proofs.Exit.stepState]
    exact ⟨initialized + count, nextLive, [], by omega, by omega, finalWorld, rfl, rfl, finalClear⟩
  | stop stop after =>
    obtain ⟨completed, nextLive, regions, lower, upper, finalWorld⟩ :=
      initGlobals_byteOwners_stopped_world count fuel initialized config before after stop ambient types live world clear declarations outcome
    simp only [Goose.Proofs.Exit.stepState]
    exact ⟨completed, nextLive, regions, lower, by omega, finalWorld, upper⟩
  | escape target carriers after | jump target kind after =>
    rw [outcome] at localAction
    cases localAction

#print axioms initGlobals_byteOwners_positive_complete

end Goose.Proofs.ConstructionAcceptedExecution
