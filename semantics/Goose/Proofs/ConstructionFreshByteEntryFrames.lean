import Goose.Proofs.ConstructionFreshByteLocalSequenceEvents
import Goose.Proofs.ConstructionByteGlobalEntryComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem withScope_events (environment : RuntimeActivation) (scope scopeInst : Nat) (action : EvalM α) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (withScope environment scope scopeInst action state)).construction.events =
      (Goose.Proofs.Exit.stepState (action state)).construction.events := by
  unfold withScope
  cases evaluated : action state with
  | ok value after => simp [evaluated, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState]
  | stop reason after => simp [evaluated, Goose.Proofs.Exit.stepState]
  | escape target carriers after => simp [evaluated, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState]
  | jump target kind after => simp [evaluated, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState]

theorem finishActivation_empty_events (layout : LayoutEnv) (activation : RuntimeActivation)
    (empty : activation.channels = []) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier)) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (finishActivation layout activation [] origin action state)).construction.events =
      (Goose.Proofs.Exit.stepState (action state)).construction.events := by
  unfold finishActivation
  cases executed : action state with
  | ok carriers after =>
    cases carriers <;> simp [executed, empty, finishChannels, landCarriersInto, bind, pure, fault, EvalM.stop,
      Goose.Proofs.Exit.stepState]
  | stop reason after => simp [executed, Goose.Proofs.Exit.stepState]
  | escape target carriers after =>
    by_cases same : target.activation = activation.act <;> cases carriers <;>
      simp [executed, same, empty, finishChannels, landCarriersInto, bind, pure, fault, EvalM.stop,
        Goose.Proofs.Exit.stepState]
  | jump target kind after => simp [executed, Goose.Proofs.Exit.stepState]

theorem deliverPublish_empty_events (fuel : Nat) (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carriers : List Carrier) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState ((deliverCarriers fuel layout [] carriers origin >>= publishCarriers origin) state)).construction.events =
      state.construction.events := by
  cases carriers <;> simp [deliverCarriers, publishCarriers, landCarriersInto, publishOperation,
    preflightPublication, ConstructionM.get, liftConstruction, bind, pure, fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  rfl

theorem execResultScope_byte_events (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (execResultScope activation [] [] (.mk scope statements none)
      (fun environment statements => execStmts fuel config environment statements)
      (fun environment expression => withCompletionChannels [] (expressionOrigin expression)
        (fun channels => evalProduce fuel config environment channels expression)) state)).construction.events =
    (Goose.Proofs.Exit.stepState (execStmts fuel config
      { activation with scopes := (scope, state.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope state))).construction.events := by
  rw [execResultScope_ownership_continuation]
  rw [withScope_events]
  simp only [bindAll, List.forIn_nil, pure, bind]
  cases executed : execStmts fuel config
      { activation with scopes := (scope, state.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope state) with
  | ok flow after =>
    cases flow <;> simp [executed, pure, Goose.Proofs.Exit.stepState]
  | stop reason after => simp [executed, Goose.Proofs.Exit.stepState]
  | escape target carriers after => simp [executed, Goose.Proofs.Exit.stepState]
  | jump target kind after => simp [executed, Goose.Proofs.Exit.stepState]

theorem execActivationBody_byte_events (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (empty : activation.channels = []) (scope : Nat) (statements : List Stmt) (state : ExecutionState) :
    (Goose.Proofs.Exit.stepState (execActivationBody (fuel + 1) config activation [] (.mk scope statements none) state)).construction.events =
    (Goose.Proofs.Exit.stepState (execStmts fuel config
      { activation with scopes := (scope, state.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope state))).construction.events := by
  simp only [execActivationBody, empty]
  rw [bind_events_frame]
  · simpa only [empty] using execResultScope_byte_events fuel config activation scope statements state
  · intro result after
    cases result with
    | mk flow carriers => cases flow <;> simp [pure, fault, EvalM.stop, Goose.Proofs.Exit.stepState]

#print axioms execResultScope_byte_events
#print axioms execActivationBody_byte_events
#print axioms withScope_events
#print axioms finishActivation_empty_events
#print axioms deliverPublish_empty_events

end Goose.Proofs.ConstructionAcceptedExecution
