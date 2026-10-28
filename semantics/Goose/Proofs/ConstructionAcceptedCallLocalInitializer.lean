import Goose.Proofs.ConstructionAcceptedReturnedScalarBinding
import Goose.Proofs.ConstructionAcceptedInvocationValue
import Goose.Proofs.ConstructionAcceptedBindingCounters
import Goose.Proofs.ConstructionAcceptedRegisterCallTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem checked_recursiveRegisterCall_initializer {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (id statementOrigin target callOrigin checkFuel : Nat) (context : Context) (callee : Impl) (ty : Ty)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[target]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (nesting : frame.typingFuel = (checkFuel + 1) + 1)
    (position : SourcePosition accepted frame (.statement (.letS id (.call target [] callOrigin) statementOrigin)))
    (available : ∀ rootsAfter, rpStmt frame.source (.letS id (.call target [] callOrigin) statementOrigin) frame.rootCursor =
      .ok ((), rootsAfter) → GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) :
    ∃ descriptor roots typingAfter rootsAfter,
      frame.typing.variables[id]? = some descriptor ∧ id = frame.typingCounter ∧ id = frame.rootCursor.nextVar ∧ descriptor.ty = ty ∧
      AcceptedFrame config accepted (letInitializerFrame frame id (checkFuel + 1)) state types ∧
      CheckedValue (letInitializerFrame frame id (checkFuel + 1)) (.call target [] callOrigin) ty roots typingAfter rootsAfter := by
  obtain ⟨descriptor, declared, typingOrder, rootOrder, callPosition⟩ :=
    position.callInitializer frame id statementOrigin target callOrigin (checkFuel + 1) [] nesting
  obtain ⟨next, statementAfter, statementRoots, statementTyped, statementRooted⟩ := position.checked accepted frame _
  have typed' : typeStatement ((checkFuel + 1) + 1) frame.typing (.letS id (.call target [] callOrigin) statementOrigin)
      frame.typingCounter = .ok (next, statementAfter) := by simpa [nesting] using statementTyped
  have contextAt' : frame.typing.module.contexts[target]? = some context := by simpa [source.compatible.module] using contextAt
  have calleeAt' : frame.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
  obtain ⟨other, otherDeclared, _, sameType⟩ := typeStatement_registerCall_result (checkFuel + 1) frame.typing next id target callOrigin
    statementOrigin [] frame.typingCounter statementAfter context callee ty contextAt' calleeAt' results scalarTy localScalar typed'
  have sameDescriptor : other = descriptor := Option.some.inj (otherDeclared.symm.trans declared)
  subst other
  have initialSource := source.letInitializer id (checkFuel + 1) descriptor rootOrder typingOrder declared
  obtain ⟨resultTypes, typingAfter, roots, rootsAfter, callTyped, callRooted⟩ := callPosition.checked accepted _ _
  have singleton := typeExpr_registerCall_result checkFuel (letInitializerFrame frame id (checkFuel + 1)).typing target callOrigin
    context callee [] ty (letInitializerFrame frame id (checkFuel + 1)).typingCounter typingAfter resultTypes
    (by simpa [letInitializerFrame, ordinaryOperandFrame] using contextAt')
    (by simpa [letInitializerFrame, ordinaryOperandFrame] using calleeAt') results scalarTy rfl callTyped
  subst resultTypes
  have descriptorSource : frame.source.impl.vars[id]? = some descriptor := by rw [source.compatible.sourceVariables]; exact declared
  have rooted' : rpExpr { frame.source with initializing := id :: frame.source.initializing } (.call target [] callOrigin)
      { frame.rootCursor with nextVar := frame.rootCursor.nextVar + 1 } = .ok (roots, rootsAfter) := by
    simpa [letInitializerFrame, ordinaryOperandFrame] using callRooted
  have sameRoots := rpStmt_scalarLocal_cursor frame.source id (.call target [] callOrigin) statementOrigin frame.rootCursor
    statementRoots rootsAfter descriptor roots descriptorSource (localScalar descriptor declared) rooted' statementRooted
  refine ⟨descriptor, roots, typingAfter, rootsAfter, declared, typingOrder, rootOrder, sameType, initialSource, callTyped, callRooted, ?_⟩
  change GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff
  rw [← sameRoots]
  exact available statementRoots statementRooted

theorem execStmt_recursiveRegisterCall_initializer_fromInvocation_observed (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id statementOrigin target callOrigin : Nat) (context : Context) (callee : Impl) (ty : Ty) (scope scopeInst : Nat)
    (outerScopes : List (Nat × Nat))
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (nesting : frame.typingFuel = (checkFuel + 1) + 1)
    (position : SourcePosition accepted frame (.statement (.letS id (.call target [] callOrigin) statementOrigin)))
    (available : ∀ rootsAfter, rpStmt frame.source (.letS id (.call target [] callOrigin) statementOrigin) frame.rootCursor =
      .ok ((), rootsAfter) → GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes)
    (frontier : Nat) (frontierClock : frontier ≤ state.nextAct)
    (frontierAct : frontier ≤ frame.interpretation.environment.act)
    (invoked : ∀ evalFuel callFuel, fuel = evalFuel + 1 → evalFuel = callFuel + 1 →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall callFuel config frame.interpretation.environment target [] [.register ty] callOrigin state
        RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted (letInitializerFrame frame id (checkFuel + 1)) (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    match execStmt fuel config frame.interpretation.environment (.letS id (.call target [] callOrigin) statementOrigin) state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive,
        RootTypesExtend types nextTypes ∧ AcceptedWorld config frame.initialized after nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted frame after nextTypes ∧ state.nextAct ≤ after.nextAct ∧
        state.nextScope ≤ after.nextScope ∧ EarlierCallerObservations frontier state after types nextTypes
    | .ok flow after => flow = .normal .unit ∧ ∃ nextTypes nextLive,
        RootTypesExtend types nextTypes ∧
        AcceptedWorld config frame.initialized after ambient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted (advanceLocalFrame frame id) after nextTypes ∧ state.nextAct ≤ after.nextAct ∧
        state.nextScope ≤ after.nextScope ∧ EarlierCallerObservations frontier state after types nextTypes
    | .escape .. | .jump .. => False := by
  obtain ⟨descriptor, roots, typingAfter, rootsAfter, declared, typingOrder, rootOrder, sameTy, initialSource, checked⟩ :=
    checked_recursiveRegisterCall_initializer frame state types id statementOrigin target callOrigin checkFuel context callee ty
      source contextAt calleeAt results scalarTy localScalar nesting position available
  obtain ⟨next, statementAfter, statementRoots, typed, rooted⟩ := position.checked accepted frame _
  have typed' : typeStatement ((checkFuel + 1) + 1) frame.typing (.letS id (.call target [] callOrigin) statementOrigin)
      frame.typingCounter = .ok (next, statementAfter) := by simpa [nesting] using typed
  obtain ⟨scopeDescriptor, scopeDeclared, localScope, _⟩ := typeStatement_let_descriptor (checkFuel + 1) frame.typing next id
    (.call target [] callOrigin) statementOrigin frame.typingCounter statementAfter typed'
  have sameDescriptor : scopeDescriptor = descriptor := Option.some.inj (scopeDeclared.symm.trans declared)
  subst scopeDescriptor
  have sourceScopes : frame.source.scopes = scope :: outerScopes.map Prod.fst := by rw [source.compatible.scopes, scopes]; rfl
  have localScope' := localScope.trans (source.compatible.currentScope scope (outerScopes.map Prod.fst) sourceScopes)
  have runtimeDeclared : frame.interpretation.environment.vars[id]? = some descriptor := by
    rw [source.compatible.variables]; exact declared
  have resolved : rootOf frame.interpretation.environment id state =
      .ok (.local frame.interpretation.environment.act scopeInst id) state := by
    simp [rootOf, runtimeDeclared, scopes, localScope', pure]
  have fixed : descriptor.ty.nonfixed = false := by
    rcases localScalar descriptor declared with ⟨intTy, same⟩ | same <;> simp [same, Ty.nonfixed]
  cases fuel with
  | zero =>
    simp only [execStmt, timeout, EvalM.stop]
    exact ⟨ambient, types, live, (fun _ _ found => found), world, source, Nat.le_refl _, Nat.le_refl _,
      EarlierCallerObservations.refl frontier state types⟩
  | succ fuel =>
    have action := execStmt_scalarLocal_afterRoot fuel config frame.interpretation.environment id descriptor
      (.call target [] callOrigin) statementOrigin state _ runtimeDeclared fixed resolved
    have initialWorld : AcceptedWorld config (letInitializerFrame frame id (checkFuel + 1)).initialized state ambient types live regions pending := world
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopeClocks, finalWorld, finalInitialSource, clear, observed, result⟩ :=
      evalValue_register_earlier_fromInvocation fuel config accepted (letInitializerFrame frame id (checkFuel + 1)) state ambient types live
        regions pending target context callee ty callOrigin initialWorld initialSource contextAt calleeAt results
        (fun callFuel equal => invoked fuel callFuel rfl equal)
    have finalSource := source.afterEarlierObservations acts scopeClocks observed
    change state.nextAct ≤ (Goose.Proofs.Exit.stepState
      (evalValue fuel config frame.interpretation.environment (.call target [] callOrigin) state)).nextAct at acts
    change state.nextScope ≤ (Goose.Proofs.Exit.stepState
      (evalValue fuel config frame.interpretation.environment (.call target [] callOrigin) state)).nextScope at scopeClocks
    change EarlierCallerObservations state.nextAct state
      (Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment (.call target [] callOrigin) state)) types nextTypes at observed
    change AcceptedWorld config frame.initialized
      (Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment (.call target [] callOrigin) state))
      nextAmbient nextTypes nextLive regions pending at finalWorld
    change AcceptedFrame config accepted frame
      (Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment (.call target [] callOrigin) state)) nextTypes at finalSource
    change (match evalValue fuel config frame.interpretation.environment (.call target [] callOrigin) state with
      | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation ty value
      | .stop .. => True | .escape .. | .jump .. => False) at result
    rw [action]
    cases evaluated : evalValue fuel config frame.interpretation.environment (.call target [] callOrigin) state with
    | escape address carriers after | jump destination kind after => simp [evaluated] at result
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at finalWorld finalSource result acts scopeClocks observed
      simp only [bind, evaluated]
      exact ⟨nextAmbient, nextTypes, nextLive, extend, finalWorld, finalSource, acts, scopeClocks, observed.restrict frontierClock⟩
    | ok value after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at finalWorld finalSource result acts scopeClocks observed
      obtain ⟨ambientEq, represented⟩ := result
      subst nextAmbient
      have afterResolved := rootOf_transfer frame.interpretation id state after _ resolved
      have representedLocal : ValueRepresentation descriptor.ty value := by simpa [sameTy] using represented
      obtain ⟨final, bound, boundExtend, boundWorld, boundSource⟩ := finalSource.bindReturnedScalar finalWorld id scopeInst descriptor value
        rootOrder typingOrder declared afterResolved (localScalar descriptor declared) representedLocal
      have counters := bindRoot_counters _ value after final bound
      have boundObserved := EarlierCallerObservations.bindFreshLocal frontier frame.interpretation.environment.act scopeInst id
        descriptor.ty value after final nextTypes frontierAct bound
      have finalObserved := (observed.restrict frontierClock).trans (Nat.le_refl frontier) boundObserved
      simp only [bind, evaluated, bound, pure]
      exact ⟨trivial, _, _, (fun root rootTy found => boundExtend root rootTy (extend root rootTy found)), boundWorld, boundSource,
        counters.1 ▸ acts, counters.2 ▸ scopeClocks, finalObserved⟩

theorem execStmt_recursiveRegisterCall_initializer_fromInvocation (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id statementOrigin target callOrigin : Nat) (context : Context) (callee : Impl) (ty : Ty) (scope scopeInst : Nat)
    (outerScopes : List (Nat × Nat))
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (nesting : frame.typingFuel = (checkFuel + 1) + 1)
    (position : SourcePosition accepted frame (.statement (.letS id (.call target [] callOrigin) statementOrigin)))
    (available : ∀ rootsAfter, rpStmt frame.source (.letS id (.call target [] callOrigin) statementOrigin) frame.rootCursor =
      .ok ((), rootsAfter) → GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes)
    (invoked : ∀ evalFuel callFuel, fuel = evalFuel + 1 → evalFuel = callFuel + 1 →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall callFuel config frame.interpretation.environment target [] [.register ty] callOrigin state
        RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted (letInitializerFrame frame id (checkFuel + 1)) (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    match execStmt fuel config frame.interpretation.environment (.letS id (.call target [] callOrigin) statementOrigin) state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive,
        RootTypesExtend types nextTypes ∧ AcceptedWorld config frame.initialized after nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted frame after nextTypes
    | .ok flow after => flow = .normal .unit ∧ ∃ nextTypes nextLive,
        RootTypesExtend types nextTypes ∧
        AcceptedWorld config frame.initialized after ambient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted (advanceLocalFrame frame id) after nextTypes
    | .escape .. | .jump .. => False := by
  have observed := execStmt_recursiveRegisterCall_initializer_fromInvocation_observed fuel checkFuel config accepted frame state ambient types
    live regions pending id statementOrigin target callOrigin context callee ty scope scopeInst outerScopes world source contextAt calleeAt
    results scalarTy localScalar nesting position available scopes 0 (Nat.zero_le _) (Nat.zero_le _) invoked
  cases execution : execStmt fuel config frame.interpretation.environment (.letS id (.call target [] callOrigin) statementOrigin) state with
  | stop reason after =>
    simp only [execution] at observed ⊢
    obtain ⟨nextAmbient, nextTypes, nextLive, extend, world, source, _, _, _⟩ := observed
    exact ⟨nextAmbient, nextTypes, nextLive, extend, world, source⟩
  | ok flow after =>
    simp only [execution] at observed ⊢
    obtain ⟨normal, nextTypes, nextLive, extend, world, source, _, _, _⟩ := observed
    exact ⟨normal, nextTypes, nextLive, extend, world, source⟩
  | escape address carriers after | jump destination kind after => simpa only [execution] using observed


#print axioms execStmt_recursiveRegisterCall_initializer_fromInvocation_observed
#print axioms execStmt_recursiveRegisterCall_initializer_fromInvocation
#print axioms checked_recursiveRegisterCall_initializer
end Goose.Proofs.ConstructionAcceptedExecution
