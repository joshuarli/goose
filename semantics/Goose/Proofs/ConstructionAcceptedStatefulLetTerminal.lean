import Goose.Proofs.ConstructionAcceptedStatefulCallFuel
import Goose.Proofs.ConstructionAcceptedTerminalSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem statefulTwoParameter_terminalWorld {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel : Nat) (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (first second : Param)
    (firstDescriptor secondDescriptor : LocalVar) (scope id origin blockOrigin : Nat) (expression : Expr)
    (intTy : Goose.Core.IntTy) (literal : Int) (right : Expr) (resultTy : Ty) (resultExpression : Expr)
    (form : AcceptedBinaryExpression expression) (rightForm : AcceptedBinaryExpression right)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[contextId]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second]) (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[0]? = some firstDescriptor) (secondDeclared : callee.vars[1]? = some secondDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ t, secondDescriptor.ty = .int t) ∨ secondDescriptor.ty = .bool)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = some resultExpression)
    (resultForm : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ localId value localOrigin, .letS localId value localOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, callee.vars[localId]? = some localDesc →
        (∃ t, localDesc.ty = .int t) ∨ localDesc.ty = .bool)
    (initialized : caller.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ caller.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ caller.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (localId localScope statementOrigin : Nat) (outerScopes : List (Nat × Nat))
    (scopes : caller.interpretation.environment.scopes = (caller.typing.scope, localScope) :: outerScopes)
    (position : SourcePosition accepted caller (.statement (.letS localId (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin) statementOrigin)))
    (targetScalar : ∀ descriptor, caller.typing.variables[localId]? = some descriptor →
      (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (globalScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    StatementWorldOutcome config accepted caller.initialized ambient pending
      (execStmt fuel config caller.interpretation.environment (.letS localId (.call contextId
        [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin) statementOrigin) state) := by
  have firstAt : callee.params[0]? = some first := by simp [parameters]
  have firstId := validated_parameter_variable config.module context.impl callee 0 first accepted.accepted calleeAt firstAt
  have firstDeclared' : callee.vars[first.var]? = some firstDescriptor := by simpa [firstId] using firstDeclared
  obtain ⟨checkFuel, nesting⟩ := position.statefulCallInitializer_fuel caller localId statementOrigin contextId callOrigin
    scope id origin blockOrigin expression intTy literal right context callee first second firstDescriptor
    source.compatible contextAt calleeAt parameters firstMode firstDeclared'
  let arguments : List Arg := [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right]
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted caller _
  have typedContext : caller.typing.module.contexts[contextId]? = some context := by simpa [source.compatible.module] using contextAt
  have typedCallee : caller.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
  obtain ⟨descriptor, declared, order, resultType⟩ := typeStatement_registerCall_result (checkFuel + 6) caller.typing next
    localId contextId callOrigin statementOrigin arguments caller.typingCounter typingAfter context callee resultTy
    typedContext typedCallee results resultScalar targetScalar (by simpa [arguments, nesting, Nat.add_assoc] using typed)
  obtain ⟨scopeDescriptor, scopeDeclared, localScopeEq, _⟩ := typeStatement_let_descriptor (checkFuel + 6) caller.typing next localId
    (.call contextId arguments callOrigin) statementOrigin caller.typingCounter typingAfter (by simpa [arguments, nesting, Nat.add_assoc] using typed)
  have same : scopeDescriptor = descriptor := Option.some.inj (scopeDeclared.symm.trans declared)
  subst scopeDescriptor
  have runtimeDeclared : caller.interpretation.environment.vars[localId]? = some descriptor := by rw [source.compatible.variables]; exact declared
  have resolved : rootOf caller.interpretation.environment localId state =
      .ok (.local caller.interpretation.environment.act localScope localId) state := by
    simp [rootOf, runtimeDeclared, scopes, localScopeEq, pure]
  cases fuel with
  | zero =>
    simp only [execStmt, timeout, EvalM.stop, StatementWorldOutcome]
    exact ⟨ambient, types, live, regions, world⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      have fixed : descriptor.ty.nonfixed = false := by
        rcases resultScalar with ⟨ty, same⟩ | same <;> simp [resultType, same, Ty.nonfixed]
      simp [execStmt, runtimeDeclared, fixed, rootOf, scopes, localScopeEq, evalValue, bind, pure,
        timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      have outcome := statefulTwoParameter_initializer_world fuel checkFuel caller state ambient types live regions pending
        contextId callOrigin context callee first second firstDescriptor secondDescriptor scope id origin blockOrigin expression
        intTy literal right resultTy resultExpression form rightForm world source contextAt calleeAt parameters firstMode secondMode
        firstDeclared secondDeclared firstScalar secondScalar results resultScalar bodyForm tail resultForm owners scalarOwners initialized
        fresh absent localId localScope statementOrigin nesting position targetScalar resolved globalScalar
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

#print axioms statefulTwoParameter_terminalWorld
end Goose.Proofs.ConstructionAcceptedExecution
