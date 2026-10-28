import Goose.Proofs.ConstructionActivationCounter

namespace Goose.Proofs.ConstructionActivationCounterOwner
open Goose.Construct Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ExitExecution

theorem counter_restoreCompletedOwner (snapshot : PendingDestination) (incoming : Goose.Core.DestinationId)
    (carried : List Goose.Core.DestinationId) :
    PreservesActivationCounter (restoreCompletedOwner snapshot incoming carried) := by
  unfold restoreCompletedOwner
  cases snapshot.progress with
  | built originalCount =>
      apply counter_bind
      · exact counter_lift 0 _
      · intro current
        apply counter_bind
        · exact counter_get
        · intro state
          cases retained : carried.any (fun id =>
              (state.construction.destinations[id]?).any fun row =>
                (match row.progress with | .built _ => true | _ => false) &&
                  descendsFrom state.construction id current) with
          | true => dsimp only; exact counter_pure _
          | false =>
            dsimp only
            apply counter_bind
            · exact counter_stateQuery _ (stateQuery_getDestination current)
            · intro child
              apply counter_bind
              · exact counter_stateQuery _ (stateQuery_getDestination snapshot.capability.id)
              · intro parent
                cases parent.progress with
                | suspended count expected =>
                    cases child.progress with
                    | abandoned | cancelled =>
                        cases countInvalid : (count != originalCount) with
                        | true => simp [countInvalid]; exact counter_fault .flow
                        | false =>
                          cases ownerInvalid : (expected != current) with
                          | true => simp [countInvalid, ownerInvalid]; exact counter_fault .flow
                          | false =>
                            cases childInvalid : (child.use != .child snapshot.capability.id) with
                            | true => simp [countInvalid, ownerInvalid]; exact counter_fault .flow
                            | false =>
                              cases parentInvalid : ({ parent with progress := .built originalCount } != snapshot) with
                              | true => simp [countInvalid, ownerInvalid]; exact counter_fault .flow
                              | false =>
                                simp [countInvalid, ownerInvalid]
                                intro currentState
                                simp [EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState]
                    | _ => exact counter_pure _
                | _ => exact counter_pure _
  | _ => exact counter_stop _

private def completedCarrierIds (carriers : List Carrier) : List Goose.Core.DestinationId :=
  carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none

private theorem counter_ownerExtensionGuarded (snapshot : Option PendingDestination)
    (destination : Goose.Core.DestinationId) (action : Goose.Core.DestinationId → EvalM α)
    (preserved : PreservesActivationCounter (action destination)) :
    PreservesActivationCounter (fun state =>
      let finish := fun (carriers : List Carrier) (result : ExecutionState → ExecutionStep α) (state' : ExecutionState) =>
        match snapshot with
        | none => result state'
        | some parent =>
            match restoreCompletedOwner parent destination (completedCarrierIds carriers) state' with
            | .ok () final => result final
            | .stop reason final => .stop reason final
            | .escape target carriers final => .escape target carriers final
            | .jump target kind final => .jump target kind final
      match action destination state with
      | .escape target carriers state' => finish carriers (.escape target carriers) state'
      | .jump target kind state' =>
          finish (match kind with | .breakValue carriers => carriers | .continueLoop => []) (.jump target kind) state'
      | result => result) := by
  intro state
  have prior := preserved state
  cases result : action destination state with
  | ok value final | stop value final => simpa [result, Goose.Proofs.Exit.stepState] using prior
  | escape target carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    cases snapshot with
    | none => simpa [result, Goose.Proofs.Exit.stepState] using prior
    | some parent =>
      have after := counter_restoreCompletedOwner parent destination (completedCarrierIds carriers) final
      cases restored : restoreCompletedOwner parent destination (completedCarrierIds carriers) final <;>
        simp only [restored, Goose.Proofs.Exit.stepState] at after <;>
        simpa [result, restored, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
  | jump target kind final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    cases snapshot with
    | none => simpa [result, Goose.Proofs.Exit.stepState] using prior
    | some parent =>
      cases kind with
      | breakValue carriers =>
        have after := counter_restoreCompletedOwner parent destination (completedCarrierIds carriers) final
        cases restored : restoreCompletedOwner parent destination (completedCarrierIds carriers) final <;>
          simp only [restored, Goose.Proofs.Exit.stepState] at after <;>
          simpa [result, restored, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
      | continueLoop =>
        have after := counter_restoreCompletedOwner parent destination (completedCarrierIds []) final
        cases restored : restoreCompletedOwner parent destination (completedCarrierIds []) final <;>
          simp only [restored, Goose.Proofs.Exit.stepState] at after <;>
          simpa [result, restored, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after

theorem counter_withOwnerExtension (stored : StoredValue) (allocate : EvalM Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → EvalM α) (allocated : PreservesActivationCounter allocate)
    (preserved : ∀ destination, PreservesActivationCounter (action destination)) :
    PreservesActivationCounter (withOwnerExtension stored allocate action) := by
  unfold withOwnerExtension
  cases stored.destination with
  | none =>
    simp only [bind, pure]
    apply counter_bind
    · exact allocated
    · intro destination
      exact counter_ownerExtensionGuarded none destination action (preserved destination)
  | some id =>
    simp only [bind, pure]
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_getDestination id)
    · intro parent
      apply counter_bind
      · exact allocated
      · intro destination
        exact counter_ownerExtensionGuarded
          (match parent.progress with | .built _ => some parent | _ => none) destination action (preserved destination)

theorem pushValue_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  repeat' first
    | with_reducible exact counter_pure _
    | with_reducible exact counter_stop _
    | with_reducible exact counter_fault _
    | with_reducible exact counter_stateQuery _ (stateQuery_readLoc _ _ _)
    | with_reducible exact counter_stateQuery _ (stateQuery_sampledStored _)
    | with_reducible exact counter_stateQuery _ (stateQuery_arrayLength _)
    | with_reducible exact counter_completedReceivingDestination _
    | with_reducible exact counter_openElementReceiving _ _ _ _ _ _ _
    | with_reducible exact counter_publishElementReceiving _ _ _ _ _ _
    | with_reducible exact counter_appendFixedValues _ _ _ _ _
    | with_reducible exact previous.value _ _
    | with_reducible exact previous.place _ _
    | with_reducible exact previous.build _ _ _
    | with_reducible apply counter_withOwnerExtension
    | with_reducible apply counter_bind
    | with_reducible split
    | with_reducible rfl
    | with_reducible intro

#print axioms pushValue_counter_succ
#print axioms counter_withOwnerExtension
#print axioms counter_restoreCompletedOwner
end Goose.Proofs.ConstructionActivationCounterOwner
