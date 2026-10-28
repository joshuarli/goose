import Goose.Proofs.ConstructionAcceptedNestedScalarGlobalsInvoke
import Goose.Proofs.ConstructionAcceptedInitializerReturnFrame
import Goose.Proofs.ConstructionAcceptedRegisterCallTyping
import Goose.Proofs.ConstructionAcceptedReturnedScalarBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem nestedArgumentList_scalarGlobalsInitializer_world {config : EvalConfig} {accepted : AcceptedModule config}
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
    (statements : ScalarGlobalAssignments callee.body.stmts)
    (globalScalar : ∀ id expression origin, .assign (.global id) expression origin ∈ callee.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (initialized : caller.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded caller.rootCursor.eff config.module.globals.size)
    (blocks : ∀ expression ∈ expressions, NestedArgumentSafe config caller expression)
    (localId localScope statementOrigin : Nat)
    (position : SourcePosition accepted caller (.statement (.letS localId (.call contextId (expressions.map Arg.byVal) callOrigin) statementOrigin)))
    (targetScalar : ∀ descriptor, caller.typing.variables[localId]? = some descriptor →
      (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (resolved : rootOf caller.interpretation.environment localId state =
      .ok (.local caller.interpretation.environment.act localScope localId) state) :
    match execStmt (fuel + 2) config caller.interpretation.environment (.letS localId (.call contextId
      (expressions.map Arg.byVal) callOrigin) statementOrigin) state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok flow after => flow = .normal .unit ∧ ∃ (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextRegions : List ReceivingRegion),
        AcceptedWorld config caller.initialized after ambient
          (registerRootType nextTypes (.local caller.interpretation.environment.act localScope localId) resultTy)
          (fun other => other = .local caller.interpretation.environment.act localScope localId ∨ nextLive other) nextRegions pending ∧
        AcceptedFrame config accepted (advanceLocalFrame caller localId) after
          (registerRootType nextTypes (.local caller.interpretation.environment.act localScope localId) resultTy)
    | _ => False := by
  let arguments := expressions.map Arg.byVal
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted caller _
  cases nesting : caller.typingFuel with
  | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
  | succ checkFuel =>
    have typedContext : caller.typing.module.contexts[contextId]? = some context := by simpa [source.compatible.module] using contextAt
    have typedCallee : caller.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
    obtain ⟨descriptor, declared, typingOrder, resultType⟩ := typeStatement_registerCall_result checkFuel caller.typing next
      localId contextId callOrigin statementOrigin arguments caller.typingCounter typingAfter context callee resultTy
      typedContext typedCallee results resultScalar targetScalar (by simpa [arguments, nesting] using typed)
    obtain ⟨selected, selectedDeclared, selectedOrder, rootOrder, callPosition⟩ :=
      position.callInitializer caller localId statementOrigin contextId callOrigin checkFuel arguments nesting
    have selectedEq : selected = descriptor := Option.some.inj (selectedDeclared.symm.trans declared)
    subst selected
    let initializer := letInitializerFrame caller localId checkFuel
    have initialSource : AcceptedFrame config accepted initializer state types := source.letInitializer localId checkFuel descriptor rootOrder typingOrder declared
    have initialBounded : GlobalEffectTargetsBounded initializer.rootCursor.eff config.module.globals.size := by
      simpa [initializer, letInitializerFrame, ordinaryOperandFrame] using bounded
    have initialBlocks : ∀ expression ∈ expressions, NestedArgumentSafe config initializer expression := by
      intro expression member
      simpa [NestedArgumentSafe, ArgumentBlockSafe, initializer, letInitializerFrame, ordinaryOperandFrame] using blocks expression member
    have outcome := nestedArgumentList_scalarGlobalsRegisterCall_world accepted fuel initializer state ambient types live regions pending
      contextId callOrigin context callee expressions parameterTypes resultTy resultExpression contextAt calleeAt descriptors forms results resultScalar
      tail resultForm statements globalScalar world initialSource initialized initialBounded initialBlocks callPosition
    have runtimeDeclared : caller.interpretation.environment.vars[localId]? = some descriptor := by rw [source.compatible.variables]; exact declared
    have fixed : descriptor.ty.nonfixed = false := by
      rcases resultScalar with ⟨ty, same⟩ | same <;> simp [resultType, same, Ty.nonfixed]
    have action := execStmt_scalarLocal_afterRoot (fuel + 1) config caller.interpretation.environment localId descriptor
      (.call contextId arguments callOrigin) statementOrigin state _ runtimeDeclared fixed resolved
    cases invoked : invokeCall fuel config caller.interpretation.environment contextId arguments [.register resultTy] callOrigin state with
    | escape address carriers after | jump target kind after => simp [initializer, letInitializerFrame, ordinaryOperandFrame, arguments, invoked] at outcome
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
      have finalSource := source.leaveLetInitializer localId checkFuel rootOrder initialAfter
      have afterWorld : AcceptedWorld config caller.initialized after ambient nextTypes nextLive nextRegions pending := initialized.symm ▸ finalWorld
      have afterResolved := rootOf_transfer caller.interpretation localId state after _ resolved
      have scalarLocal : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by simpa [resultType] using resultScalar
      have representedLocal : ValueRepresentation descriptor.ty value := by simpa [resultType] using represented
      obtain ⟨final, bound, extended', boundWorld, boundSource⟩ := finalSource.bindReturnedScalar afterWorld localId localScope descriptor value
        rootOrder typingOrder declared afterResolved scalarLocal representedLocal
      have evaluated := evalValue_call_register_success fuel config caller.interpretation.environment contextId callOrigin context callee resultTy
        arguments state after value contextAt calleeAt results invoked
      rw [action]
      simp [bind, evaluated, bound, pure]
      exact ⟨nextTypes, ⟨nextLive, nextRegions, by simpa [resultType] using boundWorld⟩, by simpa [resultType] using boundSource⟩

#print axioms nestedArgumentList_scalarGlobalsInitializer_world
end Goose.Proofs.ConstructionAcceptedExecution
