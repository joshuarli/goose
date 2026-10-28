import Goose.Proofs.ConstructionAcceptedStatefulTwoParameterInvoke
import Goose.Proofs.ConstructionAcceptedInitializerReturnFrame
import Goose.Proofs.ConstructionAcceptedRegisterCallTyping
import Goose.Proofs.ConstructionAcceptedReturnedScalarBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem statefulTwoParameter_initializer_world {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel checkFuel : Nat) (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
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
    (localId localScope statementOrigin : Nat)
    (nesting : caller.typingFuel = checkFuel + 7)
    (position : SourcePosition accepted caller (.statement (.letS localId (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin) statementOrigin)))
    (targetScalar : ∀ descriptor, caller.typing.variables[localId]? = some descriptor →
      (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (resolved : rootOf caller.interpretation.environment localId state =
      .ok (.local caller.interpretation.environment.act localScope localId) state)
    (globalScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    match execStmt (fuel + 2) config caller.interpretation.environment (.letS localId (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin) statementOrigin) state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok flow after => flow = .normal .unit ∧ ∃ (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextRegions : List ReceivingRegion),
        AcceptedWorld config caller.initialized after ambient
          (registerRootType nextTypes (.local caller.interpretation.environment.act localScope localId) resultTy)
          (fun other => other = .local caller.interpretation.environment.act localScope localId ∨ nextLive other) nextRegions pending ∧
        AcceptedFrame config accepted (advanceLocalFrame caller localId) after
          (registerRootType nextTypes (.local caller.interpretation.environment.act localScope localId) resultTy)
    | _ => False := by
  let arguments : List Arg := [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right]
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted caller _
  have typedContext : caller.typing.module.contexts[contextId]? = some context := by simpa [source.compatible.module] using contextAt
  have typedCallee : caller.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
  obtain ⟨descriptor, declared, typingOrder, resultType⟩ := typeStatement_registerCall_result (checkFuel + 6) caller.typing next
    localId contextId callOrigin statementOrigin arguments caller.typingCounter typingAfter context callee resultTy
    typedContext typedCallee results resultScalar targetScalar (by simpa [arguments, nesting, Nat.add_assoc] using typed)
  obtain ⟨selected, selectedDeclared, selectedOrder, rootOrder, callPosition⟩ :=
    position.callInitializer caller localId statementOrigin contextId callOrigin (checkFuel + 6) arguments
      (by simpa [nesting, Nat.add_assoc])
  have selectedEq : selected = descriptor := Option.some.inj (selectedDeclared.symm.trans declared)
  subst selected
  let initializer := letInitializerFrame caller localId (checkFuel + 6)
  have initialSource : AcceptedFrame config accepted initializer state types :=
    source.letInitializer localId (checkFuel + 6) descriptor rootOrder typingOrder declared
  have outcome := statefulTwoParameter_call_worldWithCallerFrame fuel checkFuel initializer state ambient types live regions pending
    contextId callOrigin context callee first second firstDescriptor secondDescriptor scope id origin blockOrigin expression intTy literal right
    resultTy resultExpression form rightForm world initialSource contextAt calleeAt parameters firstMode secondMode firstDeclared secondDeclared
    firstScalar secondScalar results resultScalar bodyForm tail resultForm owners scalarOwners initialized fresh absent rfl callPosition globalScalar
  have runtimeDeclared : caller.interpretation.environment.vars[localId]? = some descriptor := by
    rw [source.compatible.variables]; exact declared
  have fixed : descriptor.ty.nonfixed = false := by
    rcases resultScalar with ⟨ty, same⟩ | same <;> simp [resultType, same, Ty.nonfixed]
  have action := execStmt_scalarLocal_afterRoot (fuel + 1) config caller.interpretation.environment localId descriptor
    (.call contextId arguments callOrigin) statementOrigin state _ runtimeDeclared fixed resolved
  cases invoked : invokeCall fuel config caller.interpretation.environment contextId arguments [.register resultTy] callOrigin state with
  | escape address carriers after | jump target kind after =>
    simp [initializer, letInitializerFrame, ordinaryOperandFrame, arguments, invoked] at outcome
  | stop reason after =>
    simp only [initializer, letInitializerFrame, ordinaryOperandFrame, arguments, invoked] at outcome
    obtain ⟨nextAmbient, nextTypes, nextLive, nextRegions, extended, finalWorld⟩ := outcome
    have evaluated := evalValue_call_register fuel config caller.interpretation.environment contextId callOrigin context callee resultTy
      arguments state contextAt calleeAt results
    rw [action]
    simp only [bind, evaluated, invoked]
    exact ⟨nextAmbient, nextTypes, nextLive, nextRegions, finalWorld⟩
  | ok carriers after =>
    simp only [initializer, letInitializerFrame, ordinaryOperandFrame, arguments, invoked] at outcome
    obtain ⟨value, nextTypes, nextLive, nextRegions, same, represented, extended, finalWorld, initialAfter⟩ := outcome
    subst carriers
    have finalSource := source.leaveLetInitializer localId (checkFuel + 6) rootOrder initialAfter
    have afterWorld : AcceptedWorld config caller.initialized after ambient nextTypes nextLive nextRegions pending := initialized.symm ▸ finalWorld
    have afterResolved := rootOf_transfer caller.interpretation localId state after _ resolved
    have scalarLocal : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by simpa [resultType] using resultScalar
    have representedLocal : ValueRepresentation descriptor.ty value := by simpa [resultType] using represented
    obtain ⟨final, bound, extended', boundWorld, boundSource⟩ := finalSource.bindReturnedScalar afterWorld localId localScope descriptor value
      rootOrder typingOrder declared afterResolved scalarLocal representedLocal
    have evaluated := evalValue_call_register_success fuel config caller.interpretation.environment contextId callOrigin context callee resultTy
      arguments state after value contextAt calleeAt results invoked
    rw [action]
    simp [bind, evaluated, bound, pure, resultType]
    exact ⟨nextTypes, ⟨nextLive, nextRegions, by simpa [resultType] using boundWorld⟩, by simpa [resultType] using boundSource⟩

#print axioms statefulTwoParameter_initializer_world
end Goose.Proofs.ConstructionAcceptedExecution
