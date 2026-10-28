import Goose.Proofs.ConstructionAcceptedParameterChecked
import Goose.Proofs.ConstructionAcceptedParameterInvoke

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocalScalarParameter_position_call_world {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[]) (mode : parameter.mode = .byValue)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (bounded : GlobalEffectTargetsBounded caller.rootCursor.eff config.module.globals.size)
    (nesting : caller.typingFuel = checkFuel + 2)
    (position : SourcePosition accepted caller (.expression (.call contextId [.byVal expression] origin)))
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = none)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient) :
    match invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => carriers = [] ∧ ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False := by
  have parameterAt : helper.params[0]? = some parameter := by simp [parameters]
  have parameterId := validated_parameter_variable config.module context.impl helper 0 parameter
    accepted.accepted helperAt parameterAt
  have descriptorAt : helper.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
  obtain ⟨roots, typingAfter, rootsAfter, checked⟩ := checkedScalarCallArgument caller contextId context helper
    parameter descriptor expression origin checkFuel callerSource.compatible contextAt helperAt parameters mode descriptorAt
    scalar shape callerInitialized bounded nesting position
  let child := ordinaryOperandFrame caller checkFuel
  have childWorld : AcceptedWorld config child.initialized state ambient types live regions pending := world
  have childSource := ordinaryOperandFrame_accepted accepted caller checkFuel state types callerSource
  have childInitialized : child.initialized = config.module.globals.size := callerInitialized
  exact mixedLocalScalarParameter_call_world shape fuel config accepted child state ambient types live regions pending
    contextId origin context helper parameter descriptor contextAt helperAt parameters results declared scalar childInitialized
    childWorld childSource roots typingAfter rootsAfter checked form tail owners scalarOwners depth outer

#print axioms mixedLocalScalarParameter_position_call_world
end Goose.Proofs.ConstructionAcceptedExecution
