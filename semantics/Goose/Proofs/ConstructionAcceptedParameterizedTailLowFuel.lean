import Goose.Proofs.ConstructionAcceptedRegisterCallTail
import Goose.Proofs.ConstructionAcceptedParameterObservation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_boundCall_lowFuel (config : EvalConfig) (activation : RuntimeActivation)
    (scope : Nat) (pre : List (Nat × Value)) (target origin : Nat) (arguments : List Arg) (ty : Ty)
    (before after : ExecutionState) (channels : activation.channels = [.register ty])
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () after) :
    execActivationBody 0 config activation pre ⟨scope, [], some (.call target arguments origin)⟩ before = .stop .timeout before ∧
    execActivationBody 1 config activation pre ⟨scope, [], some (.call target arguments origin)⟩ before = .stop .timeout after ∧
    execActivationBody 2 config activation pre ⟨scope, [], some (.call target arguments origin)⟩ before = .stop .timeout after := by
  have bound' := bound
  simp [ownershipResultScopeState] at bound'
  have step1 : execActivationBody 1 config activation pre ⟨scope, [], some (.call target arguments origin)⟩ before = .stop .timeout after := by
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      channels, beq_iff_eq, bound', execStmts, timeout, EvalM.stop]
  have step2 := execActivationBody_register_call_tail_withBindings 0 config activation scope pre [] before after after ty target origin arguments
    channels bound (by simp [execStmts, pure])
  exact ⟨by simp [execActivationBody, timeout, EvalM.stop], step1, by simpa [invokeCall, timeout, EvalM.stop] using step2⟩

#print axioms execActivationBody_boundCall_lowFuel
end Goose.Proofs.ConstructionAcceptedExecution
