import Goose.Proofs.ConstructionAcceptedRegisterCallTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocalRegisterParameter_position_letOutcome {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin localId statementOrigin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr) (scope scopeInst : Nat) (outerScopes : List (Nat × Nat))
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (mode : parameter.mode = .byValue) (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (bounded : GlobalEffectTargetsBounded caller.rootCursor.eff config.module.globals.size)
    (nesting : caller.typingFuel = checkFuel + 3)
    (position : SourcePosition accepted caller (.statement (.letS localId (.call contextId [.byVal expression] origin) statementOrigin)))
    (localScalar : ∀ localDescriptor, caller.typing.variables[localId]? = some localDescriptor →
      (∃ intTy, localDescriptor.ty = .int intTy) ∨ localDescriptor.ty = .bool)
    (scopes : caller.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient) :
    match execStmt (fuel + 2) config caller.interpretation.environment
        (.letS localId (.call contextId [.byVal expression] origin) statementOrigin) state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok flow after => flow = .normal .unit ∧ ∃ (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop)
        (nextRegions : List ReceivingRegion),
        AcceptedWorld config caller.initialized after ambient
          (registerRootType nextTypes (.local caller.interpretation.environment.act scopeInst localId) resultTy)
          (fun other => other = .local caller.interpretation.environment.act scopeInst localId ∨ nextLive other) nextRegions pending ∧
        AcceptedFrame config accepted (advanceLocalFrame caller localId) after
          (registerRootType nextTypes (.local caller.interpretation.environment.act scopeInst localId) resultTy)
    | _ => False := by
  have parameterAt : helper.params[0]? = some parameter := by simp [parameters]
  have parameterId := validated_parameter_variable config.module context.impl helper 0 parameter accepted.accepted helperAt parameterAt
  have descriptorAt : helper.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
  obtain ⟨localDescriptor, roots, typingAfter, rootsAfter, localDeclared, typingOrder, rootOrder, checked⟩ :=
    checkedRegisterCallInitializerArgument caller state types localId statementOrigin contextId origin checkFuel expression context helper
      parameter descriptor callerSource contextAt helperAt parameters mode descriptorAt scalar shape callerInitialized bounded nesting position
  obtain ⟨typingNext, typingAfterStmt, rootAfter, typed, rooted⟩ := position.checked accepted caller _
  have contextAt' : caller.typing.module.contexts[contextId]? = some context := by simpa [callerSource.compatible.module] using contextAt
  have helperAt' : caller.typing.module.impls[context.impl]? = some helper := by simpa [callerSource.compatible.module] using helperAt
  obtain ⟨otherDescriptor, otherDeclared, _, resultType⟩ := typeStatement_registerCall_result (checkFuel + 2) caller.typing typingNext
    localId contextId origin statementOrigin [.byVal expression] caller.typingCounter typingAfterStmt context helper resultTy
    contextAt' helperAt' results resultScalar localScalar (by simpa [nesting] using typed)
  have same : otherDescriptor = localDescriptor := Option.some.inj (otherDeclared.symm.trans localDeclared)
  subst otherDescriptor
  obtain ⟨scopeDescriptor, scopeDeclared, localScope, _⟩ := typeStatement_let_descriptor (checkFuel + 2) caller.typing typingNext localId
    (.call contextId [.byVal expression] origin) statementOrigin caller.typingCounter typingAfterStmt (by simpa [nesting] using typed)
  have sameScope : scopeDescriptor = localDescriptor := Option.some.inj (scopeDeclared.symm.trans localDeclared)
  subst scopeDescriptor
  have sourceScopes : caller.source.scopes = scope :: outerScopes.map Prod.fst := by rw [callerSource.compatible.scopes, scopes]; rfl
  have localScope' := localScope.trans (callerSource.compatible.currentScope scope (outerScopes.map Prod.fst) sourceScopes)
  have runtimeDeclared : caller.interpretation.environment.vars[localId]? = some localDescriptor := by
    rw [callerSource.compatible.variables]; exact localDeclared
  have resolved : rootOf caller.interpretation.environment localId state =
      .ok (.local caller.interpretation.environment.act scopeInst localId) state := by
    simp [rootOf, runtimeDeclared, scopes, localScope', pure]
  exact mixedLocalRegisterParameter_initializer_bindOutcome shape fuel config accepted caller checkFuel localId localDescriptor
    rootOrder typingOrder localDeclared state ambient types live regions pending contextId origin context helper parameter descriptor
    resultTy resultExpression contextAt helperAt parameters results resultScalar declared scalar callerInitialized world callerSource
    roots typingAfter rootsAfter checked form tail resultShape owners scalarOwners depth outer scopeInst statementOrigin resultType resolved

#print axioms mixedLocalRegisterParameter_position_letOutcome
end Goose.Proofs.ConstructionAcceptedExecution
