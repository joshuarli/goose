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
  let arguments := expressions.map Arg.byVal
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted caller _
  cases nesting : caller.typingFuel with
  | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
  | succ checkFuel =>
    have typedContext : caller.typing.module.contexts[contextId]? = some context := by simpa [source.compatible.module] using contextAt
    have typedCallee : caller.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
    obtain ⟨descriptor, declared, order, resultType⟩ := typeStatement_registerCall_result checkFuel caller.typing next
      localId contextId callOrigin statementOrigin arguments caller.typingCounter typingAfter context callee resultTy
      typedContext typedCallee results resultScalar targetScalar (by simpa [arguments, nesting] using typed)
    obtain ⟨scopeDescriptor, scopeDeclared, localScopeEq, _⟩ := typeStatement_let_descriptor checkFuel caller.typing next localId
      (.call contextId arguments callOrigin) statementOrigin caller.typingCounter typingAfter (by simpa [arguments, nesting] using typed)
    have same : scopeDescriptor = descriptor := Option.some.inj (scopeDeclared.symm.trans declared)
    subst scopeDescriptor
    have runtimeDeclared : caller.interpretation.environment.vars[localId]? = some descriptor := by rw [source.compatible.variables]; exact declared
    have resolved : rootOf caller.interpretation.environment localId state = .ok (.local caller.interpretation.environment.act localScope localId) state := by
      simp [rootOf, runtimeDeclared, scopes, localScopeEq, pure]
    cases fuel with
    | zero => simp only [execStmt, timeout, EvalM.stop, StatementWorldOutcome]; exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      cases fuel with
      | zero =>
        have fixed : descriptor.ty.nonfixed = false := by
          rcases resultScalar with ⟨ty, same⟩ | same <;> simp [resultType, same, Ty.nonfixed]
        simp [execStmt, runtimeDeclared, fixed, rootOf, scopes, localScopeEq, evalValue, bind, pure,
          timeout, EvalM.stop, StatementWorldOutcome]
        exact ⟨ambient, types, live, regions, world⟩
      | succ fuel =>
        have outcome := nestedArgumentList_singleGlobalInitializer_world fuel caller state ambient types live regions pending
          contextId callOrigin context callee expressions parameterTypes resultTy resultExpression forms world source contextAt calleeAt descriptors
          results resultScalar tail resultForm globalId globalOrigin assigned assignedForm statements globalScalar initialized bounded blocks localId localScope statementOrigin position targetScalar resolved
        cases executed : execStmt (fuel + 2) config caller.interpretation.environment (.letS localId (.call contextId arguments callOrigin) statementOrigin) state with
        | stop reason after =>
          simp only [arguments, executed] at outcome
          obtain ⟨nextAmbient, nextTypes, nextLive, nextRegions, finalWorld⟩ := outcome
          simp only [StatementWorldOutcome, arguments, executed]
          exact ⟨nextAmbient, nextTypes, nextLive, nextRegions, initialized.symm ▸ finalWorld⟩
        | escape address carriers after | jump target kind after => simp [arguments, executed] at outcome
        | ok flow after =>
          simp only [arguments, executed] at outcome
          obtain ⟨normal, nextTypes, nextLive, nextRegions, finalWorld, finalSource⟩ := outcome
          simp only [StatementWorldOutcome, arguments, executed]
          exact ⟨normal, advanceLocalFrame caller localId, _, _, _, rfl, finalWorld, finalSource⟩

#print axioms nestedArgumentList_singleGlobalTerminal_world
end Goose.Proofs.ConstructionAcceptedExecution
