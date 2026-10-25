import Goose.Proofs.ConstructionExecutionProtocolLandingAnchor
import Goose.Proofs.ConstructionExecutionProtocolExitLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem commitExitReplacement_destination_lifecycle_invariant (receiving : Option DestinationId)
    (id : DestinationId) (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (commitExitReplacement receiving id state).finalState := by
  simp only [commitExitReplacement, lookupDestination_result, bind]
  cases present : state.destinations[id]? with
  | none => exact valid
  | some replacement =>
      simp only [present]
      cases progress : replacement.progress <;> try simp only [progress] <;> try exact valid
      case built count =>
        simp only [pure, bind, ConstructionM.get]
        cases anchored : exitLandingAnchor (state.destinations.size + 1) id replacement.storage receiving state with
        | fault reason after =>
            have same := exitLandingAnchor_finalState (state.destinations.size + 1) id replacement.storage receiving state
            simp only [anchored, ConstructionResult.finalState] at same
            subst after
            exact valid
        | ok value after =>
            rcases value with ⟨old, superseded, chain⟩
            obtain ⟨same, earlier, oldPresent⟩ := exitLandingAnchor_success
              (state.destinations.size + 1) id replacement.storage receiving state after old superseded chain anchored
            subst after
            simp only [bind]
            have owner : match superseded.use with
                | .receiver => True
                | .child parent | .replacement parent => parent < id := by
              have prior := valid.2.2.2 old superseded oldPresent
              cases oldUse : superseded.use with
              | receiver => trivial
              | child parent | replacement parent =>
                  exact Nat.lt_trans (by simpa only [oldUse] using prior) earlier
            have finish (update : Option (DestinationId × PendingDestination))
                (parentValid : ∀ parentId parent, update = some (parentId, parent) →
                  ∃ before, state.destinations[parentId]? = some before ∧
                    parent.capability.id = before.capability.id ∧ parent.backing = before.backing ∧
                    parent.use = before.use ∧
                    (∀ (phase : DestinationTracePhase), phase.matchesDestination before → phase.matchesDestination parent) ∧
                    parentId < old) :
                DestinationLifecycleInvariant (((do
                  completedStep id old count replacement superseded update
                  let final ← ConstructionM.get
                  ConstructionM.set { final with destinationSuccessors := chain.map (fun previous => (previous, id)) ++ final.destinationSuccessors }) : ConstructionM Unit) state).finalState := by
              have preserved := completedStep_preserves state id old count replacement superseded update
                present progress owner parentValid earlier valid
              cases completed : completedStep id old count replacement superseded update state <;>
                simpa only [completed, bind, ConstructionM.get, ConstructionM.set, ConstructionResult.finalState,
                  DestinationLifecycleInvariant, DestinationTraceProtocol, DestinationCapabilitiesIndexed,
                  DestinationStorageReferencesValid, DestinationOwnersOrdered] using preserved
            cases oldUse : superseded.use with
            | receiver => exact finish none (by intro parentId parent impossible; cases impossible)
            | child parentId | replacement parentId =>
                simp only [lookupDestination_result, bind]
                cases parentPresent : state.destinations[parentId]? with
                | none => exact valid
                | some parent =>
                    simp only [parentPresent]
                    cases parentProgress : parent.progress <;> try simp only [parentProgress] <;> try exact valid
                    all_goals
                      split
                      · exact valid
                      · apply finish
                        intro index updated selected
                        cases selected
                        refine ⟨parent, parentPresent, rfl, rfl, rfl, ?_, ?_⟩
                        · intro phase matched
                          cases phase <;> simp_all [DestinationTracePhase.matchesDestination, DestinationTracePhase.matchesProgress]
                        · simpa only [oldUse] using valid.2.2.2 old superseded oldPresent

theorem landExitReplacementChain_destination_lifecycle_invariant (id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (landExitReplacementChain id state).finalState :=
  commitExitReplacement_destination_lifecycle_invariant none id state valid

theorem landExitReplacementInto_destination_lifecycle_invariant (receiving id : DestinationId)
    (state : ConstructionState) (valid : DestinationLifecycleInvariant state) :
    DestinationLifecycleInvariant (landExitReplacementInto receiving id state).finalState :=
  commitExitReplacement_destination_lifecycle_invariant (some receiving) id state valid

end Goose.Proofs.ConstructionExecutionProtocol
