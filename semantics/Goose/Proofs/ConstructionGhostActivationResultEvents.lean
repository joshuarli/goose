import Goose.Proofs.ConstructionGhostProtectedSourceEvents
import Goose.Proofs.ConstructionGhostActivationEvents

namespace Goose.Proofs.ConstructionGhostActivationResultEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostActivationEvents

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem withScope_resultPrefix (environment : RuntimeActivation) (scope scopeInst : Nat) (action : EvalM α) (before : ExecutionState) :
    EventPrefix (Goose.Proofs.Exit.stepState (action before)).construction.events
      (Goose.Proofs.Exit.stepState (withScope environment scope scopeInst action before)).construction.events := by
  apply (eventPrefix_iff_isPrefix _ _).mpr
  let result := action before
  have constant : PreservesConstructionInvariant (PrefixInvariant (Goose.Proofs.Exit.stepState result).construction.events)
      (fun _ => result) := by
    intro state valid
    exact List.prefix_rfl
  have preserved := preservesConstructionInvariant_withScope environment scope scopeInst (fun _ => result) constant
    (Goose.Proofs.Exit.stepState result) List.prefix_rfl
  cases actionResult : action before <;>
    simpa [withScope, result, actionResult, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using preserved

theorem finishActivation_resultPrefix (layout : LayoutEnv) (activation : RuntimeActivation) (types : List Ty)
    (origin : Goose.Core.OriginId) (action : EvalM (List Carrier)) (before : ExecutionState) :
    EventPrefix (Goose.Proofs.Exit.stepState (action before)).construction.events
      (Goose.Proofs.Exit.stepState (finishActivation layout activation types origin action before)).construction.events := by
  apply (eventPrefix_iff_isPrefix _ _).mpr
  let result := action before
  have constant : PreservesConstructionInvariant (PrefixInvariant (Goose.Proofs.Exit.stepState result).construction.events)
      (fun _ => result) := by
    intro state valid
    exact List.prefix_rfl
  have preserved := preservesConstructionInvariant_finishActivation layout activation types origin (fun _ => result) constant
    (Goose.Proofs.Exit.stepState result) List.prefix_rfl
  cases actionResult : action before <;>
    simpa [finishActivation, result, actionResult, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using preserved

theorem resultScope_noTail_events (channels : List Channel) (tailAction : Expr → EvalM (List Carrier))
    (outcome : ExecutionStep Flow) :
    (Goose.Proofs.Exit.stepState (resultScopeContinuation channels none tailAction outcome)).construction.events =
      (Goose.Proofs.Exit.stepState outcome).construction.events := by
  cases outcome with
  | ok flow state =>
      cases flow <;> cases channels with
      | nil => simp [resultScopeContinuation, pure, Goose.Proofs.Exit.stepState]
      | cons channel rest =>
          cases rest <;> cases channel <;> simp [resultScopeContinuation, pure, fault, EvalM.stop, Goose.Proofs.Exit.stepState]
          all_goals rename_i ty
          all_goals cases ty <;> simp [resultScopeContinuation, pure, fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | stop | escape | jump => rfl

theorem activationBodyFinish_events (outcome : ExecutionStep (Flow × List Carrier)) :
    (Goose.Proofs.Exit.stepState (activationBodyFinish outcome)).construction.events =
      (Goose.Proofs.Exit.stepState outcome).construction.events := by
  cases outcome with
  | ok pair state => cases pair with | mk flow carriers => cases flow <;> rfl
  | stop | escape | jump => rfl

theorem activationBody_noTail_resultPrefix (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (scope : Nat) (statements : List Stmt)
    (before : ExecutionState) (outcome : ExecutionStep Flow)
    (execution : execActivationBody (fuel + 1) config activation pre (.mk scope statements none) before =
      activationBodyFinish (withScope activation scope before.nextScope (fun _ =>
        resultScopeContinuation activation.channels none
          (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
            (fun channels => evalProduce fuel config
              { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression)) outcome)
        (resultScopeStart activation scope before))) :
    EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (execActivationBody (fuel + 1) config activation pre
        (.mk scope statements none) before)).construction.events := by
  rw [execution, activationBodyFinish_events]
  have kept := withScope_resultPrefix activation scope before.nextScope (fun _ =>
    resultScopeContinuation activation.channels none
      (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config
          { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression)) outcome)
    (resultScopeStart activation scope before)
  simpa only [resultScope_noTail_events] using kept

#print axioms activationBody_noTail_resultPrefix
#print axioms resultScope_noTail_events
#print axioms activationBodyFinish_events
#print axioms withScope_resultPrefix
#print axioms finishActivation_resultPrefix
end Goose.Proofs.ConstructionGhostActivationResultEvents
