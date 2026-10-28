import Goose.Proofs.ConstructionAcceptedNestedScalarGlobalsTerminal
import Goose.Proofs.ConstructionAcceptedNestedSingleGlobalInitializer
import Goose.Proofs.ConstructionAcceptedTerminalSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem nestedArgumentList_singleGlobalTerminal_world {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel : Nat) (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr) (forms : NestedEffectfulArguments expressions)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[contextId]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (tail : callee.body.value = some resultExpression) (resultForm : AcceptedBinaryExpression resultExpression)
    (globalId globalOrigin : Nat) (assigned : Expr) (assignedForm : AcceptedBinaryExpression assigned)
    (statements : callee.body.stmts = [.assign (.global globalId) assigned globalOrigin])
    (globalScalar : ∀ descriptor, config.module.globals[globalId]? = some descriptor →
      (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (initialized : caller.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded caller.rootCursor.eff config.module.globals.size)
    (blocks : ∀ expression ∈ expressions, NestedArgumentSafe config caller expression)
    (localId localScope statementOrigin : Nat) (outerScopes : List (Nat × Nat))
    (scopes : caller.interpretation.environment.scopes = (caller.typing.scope, localScope) :: outerScopes)
    (position : SourcePosition accepted caller (.statement (.letS localId (.call contextId (expressions.map Arg.byVal) callOrigin) statementOrigin)))
    (targetScalar : ∀ descriptor, caller.typing.variables[localId]? = some descriptor →
      (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool) :
    StatementWorldOutcome config accepted caller.initialized ambient pending
      (execStmt fuel config caller.interpretation.environment (.letS localId (.call contextId
        (expressions.map Arg.byVal) callOrigin) statementOrigin) state) := by
  apply nestedArgumentList_scalarGlobalsTerminal_world (localScope := localScope) (outerScopes := outerScopes) fuel caller state ambient types live regions pending contextId callOrigin context callee expressions parameterTypes resultTy resultExpression forms world source contextAt calleeAt descriptors results resultScalar tail resultForm
  · rw [statements]
    exact .cons globalId assigned globalOrigin [] assignedForm .nil
  · intro id expression origin member descriptor declared
    simp [statements] at member
    obtain ⟨rfl, rfl, rfl⟩ := member
    exact globalScalar descriptor declared
  · exact initialized
  · exact bounded
  · exact blocks
  · exact scopes
  · exact position
  · exact targetScalar

#print axioms nestedArgumentList_singleGlobalTerminal_world
end Goose.Proofs.ConstructionAcceptedExecution
