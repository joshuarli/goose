import Goose.Proofs.ConstructionAcceptedReturnedScalarBinding
import Goose.Proofs.ConstructionAcceptedRegisterInitializerFrame
import Goose.Proofs.ConstructionAcceptedRegisterCaller

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocalRegisterParameter_initializer_bindResult {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (checkFuel localId : Nat) (localDescriptor : LocalVar)
    (rootOrder : localId = caller.rootCursor.nextVar) (typingOrder : localId = caller.typingCounter)
    (localDeclared : caller.typing.variables[localId]? = some localDescriptor)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (letInitializerFrame caller localId checkFuel) expression descriptor.ty roots typingAfter rootsAfter)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient)
    (localScope : Nat) (statementOrigin : Goose.Core.OriginId)
    (resultType : localDescriptor.ty = resultTy)
    (resolved : rootOf caller.interpretation.environment localId state =
      .ok (.local caller.interpretation.environment.act localScope localId) state)
    (carriers : List Carrier) (after : ExecutionState)
    (executed : invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [.register resultTy] origin state =
      .ok carriers after) :
    ∃ (final : ExecutionState) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextRegions : List ReceivingRegion), execStmt (fuel + 2) config caller.interpretation.environment
      (.letS localId (.call contextId [.byVal expression] origin) statementOrigin) state = .ok (.normal .unit) final ∧
      AcceptedWorld config caller.initialized final ambient
        (registerRootType nextTypes (.local caller.interpretation.environment.act localScope localId) resultTy)
        (fun other => other = .local caller.interpretation.environment.act localScope localId ∨ nextLive other) nextRegions pending ∧
      AcceptedFrame config accepted (advanceLocalFrame caller localId) final
        (registerRootType nextTypes (.local caller.interpretation.environment.act localScope localId) resultTy) := by
  obtain ⟨value, nextTypes, nextLive, nextRegions, same, represented, extended, finalWorld, finalSource⟩ :=
    mixedLocalRegisterParameter_initializer_callerFrame shape fuel config accepted caller checkFuel localId localDescriptor rootOrder typingOrder localDeclared state ambient types live regions pending
      contextId origin context helper parameter descriptor resultTy resultExpression contextAt helperAt parameters results resultScalar declared
      scalar callerInitialized world callerSource roots typingAfter rootsAfter checked form tail resultShape owners scalarOwners depth outer
      carriers after executed
  subst carriers
  have scalarLocal : (∃ intTy, localDescriptor.ty = .int intTy) ∨ localDescriptor.ty = .bool := by simpa [resultType] using resultScalar
  have representedLocal : ValueRepresentation localDescriptor.ty value := by simpa [resultType] using represented
  have afterWorld : AcceptedWorld config caller.initialized after ambient nextTypes nextLive nextRegions pending := callerInitialized.symm ▸ finalWorld
  have afterResolved := rootOf_transfer caller.interpretation localId state after _ resolved
  obtain ⟨final, bound, extended', boundWorld, boundSource⟩ := finalSource.bindReturnedScalar afterWorld localId localScope localDescriptor value
    rootOrder typingOrder localDeclared afterResolved scalarLocal representedLocal
  have runtimeDeclared : caller.interpretation.environment.vars[localId]? = some localDescriptor := by
    rw [callerSource.compatible.variables]; exact localDeclared
  have fixed : localDescriptor.ty.nonfixed = false := by
    rcases scalarLocal with ⟨intTy, same⟩ | same <;> simp [same, Ty.nonfixed]
  have evaluated := evalValue_call_register_success fuel config caller.interpretation.environment contextId origin context helper resultTy
    [.byVal expression] state after value contextAt helperAt results executed
  have action := execStmt_scalarLocal_afterRoot (fuel + 1) config caller.interpretation.environment localId localDescriptor
    (.call contextId [.byVal expression] origin) statementOrigin state _ runtimeDeclared fixed resolved
  refine ⟨final, nextTypes, nextLive, nextRegions, ?_, ?_, ?_⟩
  · rw [action]
    simp [bind, evaluated, bound, pure]
  · simpa [resultType] using boundWorld
  · simpa [resultType] using boundSource

theorem mixedLocalRegisterParameter_initializer_bindOutcome {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (checkFuel localId : Nat) (localDescriptor : LocalVar)
    (rootOrder : localId = caller.rootCursor.nextVar) (typingOrder : localId = caller.typingCounter)
    (localDeclared : caller.typing.variables[localId]? = some localDescriptor)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (letInitializerFrame caller localId checkFuel) expression descriptor.ty roots typingAfter rootsAfter)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient)
    (localScope : Nat) (statementOrigin : Goose.Core.OriginId)
    (resultType : localDescriptor.ty = resultTy)
    (resolved : rootOf caller.interpretation.environment localId state =
      .ok (.local caller.interpretation.environment.act localScope localId) state)
    : match execStmt (fuel + 2) config caller.interpretation.environment
        (.letS localId (.call contextId [.byVal expression] origin) statementOrigin) state with
      | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
          AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
      | .ok flow after => flow = .normal .unit ∧ ∃ (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextRegions : List ReceivingRegion),
          AcceptedWorld config caller.initialized after ambient
            (registerRootType nextTypes (.local caller.interpretation.environment.act localScope localId) resultTy)
            (fun other => other = .local caller.interpretation.environment.act localScope localId ∨ nextLive other) nextRegions pending ∧
          AcceptedFrame config accepted (advanceLocalFrame caller localId) after
            (registerRootType nextTypes (.local caller.interpretation.environment.act localScope localId) resultTy)
      | _ => False := by
  let initializer := letInitializerFrame caller localId checkFuel
  have initialSource : AcceptedFrame config accepted initializer state types :=
    callerSource.letInitializer localId checkFuel localDescriptor rootOrder typingOrder localDeclared
  have initialWorld : AcceptedWorld config initializer.initialized state ambient types live regions pending := world
  have outcome := mixedLocalRegisterParameter_call_world shape fuel config accepted initializer state ambient types live regions pending
    contextId origin context helper parameter descriptor resultTy resultExpression contextAt helperAt parameters results resultScalar declared
    scalar callerInitialized initialWorld initialSource roots typingAfter rootsAfter checked form tail resultShape owners scalarOwners depth outer
  change (match invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [.register resultTy] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False) at outcome
  cases invoked : invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [.register resultTy] origin state with
  | escape target carriers after | jump target kind after => simp only [invoked] at outcome
  | stop reason after =>
    simp only [invoked] at outcome
    obtain ⟨nextAmbient, nextTypes, nextLive, nextRegions, extended, protectedTypes, finalWorld⟩ := outcome
    have runtimeDeclared : caller.interpretation.environment.vars[localId]? = some localDescriptor := by
      rw [callerSource.compatible.variables]; exact localDeclared
    have fixed : localDescriptor.ty.nonfixed = false := by
      rcases resultScalar with ⟨intTy, same⟩ | same <;> simp [resultType, same, Ty.nonfixed]
    have action := execStmt_scalarLocal_afterRoot (fuel + 1) config caller.interpretation.environment localId localDescriptor
      (.call contextId [.byVal expression] origin) statementOrigin state _ runtimeDeclared fixed resolved
    have evaluated := evalValue_call_register fuel config caller.interpretation.environment contextId origin context helper resultTy
      [.byVal expression] state contextAt helperAt results
    rw [action]
    simp only [bind, evaluated, invoked]
    exact ⟨nextAmbient, nextTypes, nextLive, nextRegions, finalWorld⟩
  | ok carriers after =>
    obtain ⟨final, nextTypes, nextLive, nextRegions, statement, finalWorld, finalSource⟩ :=
      mixedLocalRegisterParameter_initializer_bindResult shape fuel config accepted caller checkFuel localId localDescriptor rootOrder typingOrder localDeclared state ambient types live regions pending
        contextId origin context helper parameter descriptor resultTy resultExpression contextAt helperAt parameters results resultScalar declared
        scalar callerInitialized world callerSource roots typingAfter rootsAfter checked form tail resultShape owners scalarOwners depth outer
        localScope statementOrigin resultType resolved carriers after invoked
    rw [statement]
    exact ⟨rfl, nextTypes, nextLive, nextRegions, finalWorld, finalSource⟩

#print axioms mixedLocalRegisterParameter_initializer_bindOutcome
#print axioms mixedLocalRegisterParameter_initializer_bindResult
end Goose.Proofs.ConstructionAcceptedExecution
