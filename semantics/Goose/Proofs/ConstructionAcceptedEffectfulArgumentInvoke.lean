import Goose.Proofs.ConstructionAcceptedNestedArgumentFlat
import Goose.Proofs.ConstructionAcceptedNestedArgumentInvoke

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem effectfulArgumentList_call_worldWithCallerFrame {config : EvalConfig} (accepted : AcceptedModule config)
    (fuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (forms : EffectfulScalarArguments expressions)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = some resultExpression)
    (resultForm : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ localId value statementOrigin, .letS localId value statementOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ descriptor, callee.vars[localId]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (initialized : frame.initialized = config.module.globals.size)
    (ordinary : frame.typing.use = .ordinary) (request : frame.typing.request = .value) (requests : frame.typing.resultRequests = [])
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (blocks : ∀ expression ∈ expressions, ArgumentBlockSafe config frame expression)
    (position : SourcePosition accepted frame (.expression (.call contextId (expressions.map Arg.byVal) origin))) :
    match invokeCall fuel config frame.interpretation.environment contextId (expressions.map Arg.byVal) [.register resultTy] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted frame after nextTypes
    | _ => False := by
  have nestedBlocks : ∀ expression ∈ expressions, NestedArgumentSafe config frame expression := by
    intro expression member
    exact (forms.member member).nestedSafe (blocks expression member)
  have outcome := nestedArgumentList_call_worldWithCallerFrame accepted fuel frame state ambient types live regions pending
    contextId origin context callee expressions parameterTypes resultTy resultExpression contextAt calleeAt descriptors forms.nested
    results resultScalar bodyForm tail resultForm owners scalarOwners world source initialized ordinary request requests bounded nestedBlocks position
  cases step : invokeCall fuel config frame.interpretation.environment contextId (expressions.map Arg.byVal) [.register resultTy] origin state <;>
    simpa [step] using outcome

#print axioms effectfulArgumentList_call_worldWithCallerFrame
end Goose.Proofs.ConstructionAcceptedExecution
