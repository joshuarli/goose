import Goose.Proofs.ConstructionAcceptedNestedArgumentAnyUse
import Goose.Proofs.ConstructionAcceptedEmptyParameterInvoke
import Goose.Proofs.ConstructionAcceptedNestedEmptyMixedAssignInvoke
import Goose.Proofs.ConstructionAcceptedMixedLocalAsAssign

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem nestedArgumentList_emptyCall_worldAnyUse {config : EvalConfig} (accepted : AcceptedModule config)
    (fuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
        (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (forms : NestedEffectfulArguments expressions)
    (results : callee.results = #[])
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = none)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ localId value statementOrigin, .letS localId value statementOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ descriptor, callee.vars[localId]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (blocks : ∀ expression ∈ expressions, NestedArgumentSafe config frame expression)
    (position : SourcePosition accepted frame (.expression (.call contextId (expressions.map Arg.byVal) origin))) :
    match invokeCall fuel config frame.interpretation.environment contextId (expressions.map Arg.byVal) [] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => carriers = [] ∧ ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False := by
  have localTargets : ∀ id expression statementOrigin, .assign (.var id) expression statementOrigin ∈ callee.body.stmts →
      ∀ descriptor, callee.vars[id]? = some descriptor → (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool := by
    intro id expression statementOrigin member descriptor declared
    exact (bodyForm.noAssignment (.var id) expression statementOrigin member).elim
  have globalTargets : ∀ id expression statementOrigin, .assign (.global id) expression statementOrigin ∈ callee.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool := by
    intro id expression statementOrigin member descriptor declared
    exact (bodyForm.noAssignment (.global id) expression statementOrigin member).elim
  have result := nestedArgumentList_emptyMixedAssignCall_world accepted fuel frame state ambient types live regions pending
    contextId origin context callee expressions parameterTypes contextAt calleeAt descriptors forms results bodyForm.asAssign tail
    owners scalarOwners localTargets globalTargets world source initialized bounded blocks position
  cases step : invokeCall fuel config frame.interpretation.environment contextId (expressions.map Arg.byVal) [] origin state <;>
    simpa [step] using result

#print axioms nestedArgumentList_emptyCall_worldAnyUse
end Goose.Proofs.ConstructionAcceptedExecution
