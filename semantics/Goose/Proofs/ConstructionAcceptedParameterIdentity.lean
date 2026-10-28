import Goose.Proofs.ConstructionAcceptedParameterValueObservation
import Goose.Proofs.ConstructionAcceptedRegisterTail
import Goose.Proofs.ConstructionAcceptedScalarPrint
import Goose.Proofs.ConstructionRootCorrespondenceScopes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem evalValue_boundParameter (fuel : Nat) (config : EvalConfig) (implementationId : Nat)
    (implementation : Impl) (parameter : Param) (descriptor : LocalVar) (activation : RuntimeActivation)
    (before after : ExecutionState) (value : Value)
    (accepted : validate config.module = .ok ())
    (present : config.module.impls[implementationId]? = some implementation)
    (parameterAt : implementation.params[0]? = some parameter)
    (descriptorAt : implementation.vars[0]? = some descriptor)
    (variables : activation.vars = implementation.vars)
    (bound : bindAll activation.act before.nextScope [(parameter.var, value)]
      (ownershipResultScopeState activation implementation.body.scope
        { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }) = .ok () after) :
    evalValue (fuel + 2) config
      { activation with scopes := (implementation.body.scope, before.nextScope) :: activation.scopes }
      (.read (.var 0)) after = .ok value after := by
  have parameterId := validated_parameter_variable config.module implementationId implementation 0 parameter accepted present parameterAt
  have scope := validated_parameter_scope config.module implementationId implementation 0 parameter descriptor accepted present parameterAt descriptorAt
  have bodyScope := validated_body_scope config.module implementationId implementation accepted present
  have declared : activation.vars[0]? = some descriptor := by simpa [variables] using descriptorAt
  have resolved : rootOf { activation with scopes := (implementation.body.scope, before.nextScope) :: activation.scopes } 0 after =
      .ok (.local activation.act before.nextScope 0) after := by
    simp [rootOf, declared, scope, bodyScope, pure]
  have found := bindAll_single_lookup activation implementation.body.scope parameter.var value before after bound
  exact evalValue_visibleLocal fuel config _ 0 _ value after resolved (by simpa [parameterId] using found)

theorem execActivationBody_identityParameter (fuel : Nat) (config : EvalConfig) (implementationId : Nat)
    (implementation : Impl) (parameter : Param) (descriptor : LocalVar) (activation : RuntimeActivation)
    (before after : ExecutionState) (value : Value) (ty : Ty)
    (accepted : validate config.module = .ok ())
    (present : config.module.impls[implementationId]? = some implementation)
    (parameterAt : implementation.params[0]? = some parameter)
    (descriptorAt : implementation.vars[0]? = some descriptor)
    (variables : activation.vars = implementation.vars) (channels : activation.channels = [.register ty])
    (bound : bindAll activation.act before.nextScope [(parameter.var, value)]
      (ownershipResultScopeState activation implementation.body.scope
        { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }) = .ok () after) :
    execActivationBody (fuel + 4) config activation [(parameter.var, value)]
      ⟨implementation.body.scope, [], some (.read (.var 0))⟩
      { before with nextAct := before.nextAct + 1, activations := activation :: before.activations } =
      .ok [.register value] (releaseScopeState activation implementation.body.scope before.nextScope after) := by
  have form : AcceptedBinaryExpression (.read (.var 0)) := .numeric (.scalar (.scalar (.localRead 0)))
  have executed := execActivationBody_register_scalar_tail_withBindings form (fuel + 2) config activation
    implementation.body.scope [(parameter.var, value)] []
    { before with nextAct := before.nextAct + 1, activations := activation :: before.activations } after after ty channels
    (by simpa using bound) (by simp [execStmts, pure])
  have read := evalValue_boundParameter fuel config implementationId implementation parameter descriptor activation before after value
    accepted present parameterAt descriptorAt variables bound
  simpa [read] using executed

#print axioms evalValue_boundParameter
#print axioms execActivationBody_identityParameter
end Goose.Proofs.ConstructionAcceptedExecution
