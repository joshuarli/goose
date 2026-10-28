import Goose.Proofs.ConstructionAcceptedNestedArgumentFlat
import Goose.Proofs.ConstructionAcceptedEffectfulArgumentInitializer
import Goose.Proofs.ConstructionAcceptedTerminalSequence
import Goose.Proofs.ConstructionAcceptedNestedArgumentTerminal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem effectfulArgumentList_terminalWorld {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel : Nat) (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr) (forms : EffectfulScalarArguments expressions)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[contextId]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = some resultExpression)
    (resultForm : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ localId value localOrigin, .letS localId value localOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, callee.vars[localId]? = some localDesc →
        (∃ t, localDesc.ty = .int t) ∨ localDesc.ty = .bool)
    (initialized : caller.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded caller.rootCursor.eff config.module.globals.size)
    (blocks : ∀ expression ∈ expressions, ArgumentBlockSafe config caller expression)
    (localId localScope statementOrigin : Nat) (outerScopes : List (Nat × Nat))
    (scopes : caller.interpretation.environment.scopes = (caller.typing.scope, localScope) :: outerScopes)
    (position : SourcePosition accepted caller (.statement (.letS localId (.call contextId (expressions.map Arg.byVal) callOrigin) statementOrigin)))
    (targetScalar : ∀ descriptor, caller.typing.variables[localId]? = some descriptor →
      (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool) :
    StatementWorldOutcome config accepted caller.initialized ambient pending
      (execStmt fuel config caller.interpretation.environment (.letS localId (.call contextId
        (expressions.map Arg.byVal) callOrigin) statementOrigin) state) := by
  have nestedBlocks : ∀ expression ∈ expressions, NestedArgumentSafe config caller expression := by
    intro expression member
    exact (forms.member member).nestedSafe (blocks expression member)
  exact nestedArgumentList_terminalWorld fuel caller state ambient types live regions pending contextId callOrigin
    context callee expressions parameterTypes resultTy resultExpression forms.nested world source contextAt calleeAt descriptors
    results resultScalar bodyForm tail resultForm owners scalarOwners initialized bounded nestedBlocks localId localScope statementOrigin
    outerScopes scopes position targetScalar

#print axioms effectfulArgumentList_terminalWorld
end Goose.Proofs.ConstructionAcceptedExecution
