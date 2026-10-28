import Goose.Proofs.ConstructionAcceptedCallLocalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem execStmts_callLocal_scalarTail (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
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
    (contextId : Nat) (phase : frame.phase = .implementation contextId)
    (tailForm : ScalarLocalStatements rest)
    (tailScalar : ∀ localId expression origin, .letS localId expression origin ∈ rest → ∀ descriptor,
      frame.source.impl.vars[localId]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (nesting : frame.typingFuel = (checkFuel + 1) + 2)
    (position : SourcePosition accepted frame (.statements (.letS id (.call target [] callOrigin) statementOrigin :: rest)))
    (available : ∀ rootsAfter, rpStmts frame.source (.letS id (.call target [] callOrigin) statementOrigin :: rest) frame.rootCursor =
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
    ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextAmbient : OwnershipAmbient),
      let outcome := execStmts (fuel + 1) config frame.interpretation.environment
        (.letS id (.call target [] callOrigin) statementOrigin :: rest) state
      let after := Goose.Proofs.Exit.stepState outcome
      next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧ state.nextAct ≤ after.nextAct ∧
      state.nextScope ≤ after.nextScope ∧ AcceptedWorld config next.initialized after nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted next after nextTypes ∧ EarlierCallerObservations frontier state after types nextTypes ∧
      (match outcome with
       | .ok flow _ => nextAmbient = ambient ∧ flow = .normal .unit ∧ SourcePosition accepted next (.statements []) ∧
           ScalarLocalReplay frame next (.letS id (.call target [] callOrigin) statementOrigin :: rest)
       | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨_, _, allRoots, _, rootedAll⟩ := position.checked accepted frame _
  obtain ⟨middleRoots, headRooted, tailRooted⟩ := rpStmts_cons rootedAll
  have headAvailable : ∀ after, rpStmt frame.source (.letS id (.call target [] callOrigin) statementOrigin) frame.rootCursor = .ok ((), after) →
      GlobalEffectsAvailable frame.interpretation frame.initialized after.eff := by
    intro after rooted
    have same : after = middleRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans headRooted))).2
    subst after
    have included := rpStmts_effectTargetsIncluded tailRooted
    intro target member global rooted
    exact available allRoots rootedAll target (included member) global rooted
  have headOutcome := execStmt_recursiveRegisterCallLocal_prefix fuel checkFuel config accepted frame state ambient types live regions pending
    id statementOrigin target callOrigin rest context callee ty scope scopeInst outerScopes world source contextAt calleeAt parameters results
    scalarTy localScalar nesting position headAvailable scopes frontier frontierClock frontierAct invoked
  cases head : execStmt fuel config frame.interpretation.environment (.letS id (.call target [] callOrigin) statementOrigin) state with
  | stop reason after =>
    simp only [head] at headOutcome
    obtain ⟨nextAmbient, nextTypes, nextLive, extend, finalWorld, finalSource, acts, scopeClocks, observed⟩ := headOutcome
    simp only [execStmts, bind, head, Goose.Proofs.Exit.stepState]
    exact ⟨frame, nextTypes, nextLive, nextAmbient, rfl, extend, acts, scopeClocks, finalWorld, finalSource, observed, trivial⟩
  | escape address carriers after | jump destination kind after => simp only [head] at headOutcome
  | ok flow middle =>
    simp only [head] at headOutcome
    obtain ⟨normal, nextTypes, nextLive, extend, middleWorld, ⟨rootsAfter, middleRooted, middleTyped, cursor,
      middleSource, middlePosition⟩, acts, scopeClocks, observed⟩ := headOutcome
    subst flow
    have sameRoots : rootsAfter = middleRoots := (Prod.mk.inj (Except.ok.inj (middleRooted.symm.trans headRooted))).2
    let nextFrame := { advanceLocalFrame { frame with typingFuel := checkFuel + 2 } id with rootCursor := rootsAfter }
    have remainingAvailable : ∀ final, rpStmts nextFrame.source rest nextFrame.rootCursor = .ok ((), final) →
        GlobalEffectsAvailable nextFrame.interpretation nextFrame.initialized final.eff := by
      intro final checked
      have equal : final = allRoots := by
        have checked' : rpStmts frame.source rest middleRoots = .ok ((), final) := by
          simpa [nextFrame, advanceLocalFrame, sameRoots] using checked
        exact (Prod.mk.inj (Except.ok.inj (checked'.symm.trans tailRooted))).2
      subst final
      simpa [nextFrame, advanceLocalFrame] using available allRoots rootedAll
    have remainingScalar : ∀ id expression origin, .letS id expression origin ∈ rest →
        ∀ descriptor, nextFrame.source.impl.vars[id]? = some descriptor →
          (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
      intro id expression origin member descriptor found
      exact tailScalar id expression origin member descriptor found
    obtain ⟨finalFrame, finalTypes, finalLive, initializedEq, finalExtended, finalActs, finalScopes, finalWorld, finalSource, finalObserved, finalFlow⟩ :=
      execStmts_scalarLocal_prefix_observed tailForm frontier fuel config accepted nextFrame contextId middle ambient nextTypes nextLive regions pending
        (by simpa [nextFrame, advanceLocalFrame] using frontierAct) middleWorld middleSource
        (by simpa [nextFrame, advanceLocalFrame] using phase) middlePosition remainingAvailable remainingScalar
    simp only [execStmts, bind, head] at finalFlow finalActs finalScopes finalWorld finalSource finalObserved ⊢
    cases tailRun : execStmts fuel config nextFrame.interpretation.environment rest middle with
    | stop reason after =>
      have tailRun' : execStmts fuel config frame.interpretation.environment rest middle = .stop reason after := by
        simpa [nextFrame, advanceLocalFrame] using tailRun
      simp only [tailRun, tailRun'] at finalFlow finalActs finalScopes finalWorld finalSource finalObserved ⊢
      exact ⟨finalFrame, finalTypes, finalLive, ambient, initializedEq,
        (fun root ty found => finalExtended root ty (extend root ty found)), finalActs ▸ acts, finalScopes ▸ scopeClocks,
        finalWorld, finalSource, observed.trans (Nat.le_refl _) finalObserved, trivial⟩
    | escape address carriers after | jump target kind after => simp [tailRun] at finalFlow
    | ok result after =>
      have tailRun' : execStmts fuel config frame.interpretation.environment rest middle = .ok result after := by
        simpa [nextFrame, advanceLocalFrame] using tailRun
      simp only [tailRun, tailRun'] at finalFlow finalActs finalScopes finalWorld finalSource finalObserved ⊢
      obtain ⟨normal, finalPosition, replay⟩ := finalFlow
      refine ⟨finalFrame, finalTypes, finalLive, ambient, initializedEq,
        (fun root ty found => finalExtended root ty (extend root ty found)), finalActs ▸ acts, finalScopes ▸ scopeClocks,
        finalWorld, finalSource, observed.trans (Nat.le_refl _) finalObserved, rfl, normal, finalPosition, ?_⟩
      obtain ⟨typedRest, rootedRest, sourceSame, interpretationSame⟩ := replay
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [nesting]
        simp only [typeStatements, bind, StateT.bind, middleTyped, Except.bind]
        simpa [nextFrame, advanceLocalFrame] using typedRest
      · simp only [rpStmts, bind, StateT.bind, middleRooted, Except.bind]
        simpa [nextFrame, advanceLocalFrame] using rootedRest
      · simpa [nextFrame, advanceLocalFrame] using sourceSame
      · simpa [nextFrame, advanceLocalFrame] using interpretationSame

#print axioms execStmts_callLocal_scalarTail
end Goose.Proofs.ConstructionAcceptedExecution
