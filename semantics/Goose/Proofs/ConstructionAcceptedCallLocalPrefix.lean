import Goose.Proofs.ConstructionAcceptedCallLocalInitializer
import Goose.Proofs.ConstructionAcceptedCallLocalCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem execStmt_recursiveRegisterCallLocal_prefix (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id statementOrigin target callOrigin : Nat) (rest : List Stmt) (context : Context) (callee : Impl) (ty : Ty) (scope scopeInst : Nat)
    (outerScopes : List (Nat × Nat))
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (nesting : frame.typingFuel = (checkFuel + 1) + 2)
    (position : SourcePosition accepted frame (.statements (.letS id (.call target [] callOrigin) statementOrigin :: rest)))
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
        (∃ rootsAfter, rpStmt frame.source (.letS id (.call target [] callOrigin) statementOrigin) frame.rootCursor = .ok ((), rootsAfter) ∧
          typeStatement (checkFuel + 2) frame.typing (.letS id (.call target [] callOrigin) statementOrigin) frame.typingCounter =
            .ok ((advanceLocalFrame frame id).typing, (advanceLocalFrame frame id).typingCounter) ∧
          rootsAfter.nextVar = frame.rootCursor.nextVar + 1 ∧
          AcceptedFrame config accepted { advanceLocalFrame { frame with typingFuel := checkFuel + 2 } id with rootCursor := rootsAfter } after nextTypes ∧
          SourcePosition accepted { advanceLocalFrame { frame with typingFuel := checkFuel + 2 } id with rootCursor := rootsAfter } (.statements rest)) ∧ state.nextAct ≤ after.nextAct ∧
        state.nextScope ≤ after.nextScope ∧ EarlierCallerObservations frontier state after types nextTypes
    | .escape .. | .jump .. => False := by
  have head := position.statements_head accepted frame (.letS id (.call target [] callOrigin) statementOrigin) rest
    (checkFuel + 2) (by omega)
  obtain ⟨next, typingAfter, rootResult, typed, _⟩ := head.checked accepted _ _
  have typingContext : frame.typing.module.contexts[target]? = some context := by simpa [source.compatible.module] using contextAt
  have typingCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
  have typing := typeStatement_let_environment (checkFuel + 1) frame.typing next id (.call target [] callOrigin)
    statementOrigin frame.typingCounter typingAfter typed
  have counter := typeStatement_zeroArgumentRegisterCall_cursor (checkFuel + 1) frame.typing next id target callOrigin statementOrigin
    frame.typingCounter typingAfter context callee ty typingContext typingCallee parameters results scalarTy typed
  have typed' : typeStatement (checkFuel + 2) frame.typing (.letS id (.call target [] callOrigin) statementOrigin) frame.typingCounter =
      .ok ((advanceLocalFrame frame id).typing, (advanceLocalFrame frame id).typingCounter) := by
    simpa [advanceLocalFrame, typing, counter] using typed
  have headSource := source.withTypingFuel (checkFuel + 2)
  have tail := position.zeroArgumentCallLocal_tail frame state types id target callOrigin statementOrigin (checkFuel + 1) rest
    context callee ty source (by omega) contextAt calleeAt parameters results scalarTy localScalar
  obtain ⟨rootsAfter, rooted, cursor, tailPosition⟩ := tail
  have execution := execStmt_recursiveRegisterCall_initializer_fromInvocation_observed fuel checkFuel config accepted
    { frame with typingFuel := checkFuel + 2 } state ambient types live regions pending id statementOrigin target callOrigin
    context callee ty scope scopeInst outerScopes world headSource contextAt calleeAt results scalarTy localScalar
    rfl head available scopes frontier frontierClock frontierAct invoked
  cases result : execStmt fuel config frame.interpretation.environment (.letS id (.call target [] callOrigin) statementOrigin) state with
  | stop reason after =>
    simp only [result] at execution ⊢
    obtain ⟨nextAmbient, nextTypes, nextLive, extend, world, source, acts, scopeClocks, observed⟩ := execution
    exact ⟨nextAmbient, nextTypes, nextLive, extend, world, source.withTypingFuel frame.typingFuel, acts, scopeClocks, observed⟩
  | ok flow after =>
    simp only [result] at execution ⊢
    obtain ⟨normal, nextTypes, nextLive, extend, world, source, acts, scopeClocks, observed⟩ := execution
    have nextSource := source.withRootCursor rootsAfter (by simpa [advanceLocalFrame] using cursor)
    exact ⟨normal, nextTypes, nextLive, extend, world, ⟨rootsAfter, rooted, typed', cursor, nextSource, by simpa using tailPosition⟩,
      acts, scopeClocks, observed⟩
  | escape address carriers after | jump destination kind after => simpa only [result] using execution

#print axioms execStmt_recursiveRegisterCallLocal_prefix
end Goose.Proofs.ConstructionAcceptedExecution
