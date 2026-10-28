import Goose.Proofs.ConstructionAcceptedScalarLocalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmts_scalarPrefix_fromSuffix {leading : List Stmt} (form : ScalarLocalStatements leading) (suffix : List Stmt)
    (config : EvalConfig) (accepted : AcceptedModule config) (context frontier budget : Nat)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (suffixOutcome : ∀ fuel, fuel ≤ budget → ∀ (frame : ConstructionSourceFrame) (before : ExecutionState)
        (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      frontier ≤ frame.interpretation.environment.act → frontier ≤ before.nextAct →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements suffix) →
      (∀ rootsAfter, rpStmts frame.source suffix frame.rootCursor = .ok ((), rootsAfter) →
        GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextAmbient : OwnershipAmbient),
        let outcome := execStmts fuel config frame.interpretation.environment suffix before
        let after := Goose.Proofs.Exit.stepState outcome
        next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧ before.nextAct ≤ after.nextAct ∧
        before.nextScope ≤ after.nextScope ∧ AcceptedWorld config next.initialized after nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted next after nextTypes ∧ EarlierCallerObservations frontier before after types nextTypes ∧
        (match outcome with
         | .ok flow _ => nextAmbient = ambient ∧ flow = .normal .unit ∧ SourcePosition accepted next (.statements []) ∧ ScalarLocalReplay frame next suffix
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∀ fuel, fuel ≤ budget → ∀ (frame : ConstructionSourceFrame) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      frontier ≤ frame.interpretation.environment.act → frontier ≤ before.nextAct →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements (leading ++ suffix)) →
      (∀ rootsAfter, rpStmts frame.source (leading ++ suffix) frame.rootCursor = .ok ((), rootsAfter) →
        GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) →
      (∀ id expression origin, .letS id expression origin ∈ leading → ∀ descriptor,
        frame.source.impl.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextAmbient : OwnershipAmbient),
        let outcome := execStmts fuel config frame.interpretation.environment (leading ++ suffix) before
        let after := Goose.Proofs.Exit.stepState outcome
        next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧ before.nextAct ≤ after.nextAct ∧
        before.nextScope ≤ after.nextScope ∧ AcceptedWorld config next.initialized after nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted next after nextTypes ∧ EarlierCallerObservations frontier before after types nextTypes ∧
        (match outcome with
         | .ok flow _ => nextAmbient = ambient ∧ flow = .normal .unit ∧ SourcePosition accepted next (.statements []) ∧ ScalarLocalReplay frame next (leading ++ suffix)
         | .stop .. => True | .escape .. | .jump .. => False) := by
  induction form with
  | nil =>
    intro fuel bound frame before ambient types live frontierAct frontierClock world source phase position available scalar
    exact suffixOutcome fuel bound frame before ambient types live frontierAct frontierClock world source phase position available
  | cons id expression origin rest expressionForm tail ih =>
    intro fuel bound frame before ambient types live frontierAct frontierClock world source phase position available scalar
    cases fuel with
    | zero =>
      simp only [List.cons_append, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, ambient, rfl, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
        EarlierCallerObservations.refl frontier before types, trivial⟩
    | succ fuel =>
      obtain ⟨_, _, allRoots, typedAll, rootedAll⟩ := position.checked accepted frame _
      obtain ⟨middleRoots, headRooted, tailRooted⟩ := rpStmts_cons rootedAll
      have headAvailable : ∀ after, rpStmt frame.source (.letS id expression origin) frame.rootCursor = .ok ((), after) →
          GlobalEffectsAvailable frame.interpretation frame.initialized after.eff := by
        intro after rooted
        have equal : after = middleRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans headRooted))).2
        subst after
        have included := rpStmts_effectTargetsIncluded tailRooted
        intro target member global rooted
        exact available allRoots rootedAll target (included member) global rooted
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
              (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
            intro descriptor declared
            apply scalar id expression origin (by simp) descriptor
            rw [source.compatible.sourceVariables]; exact declared
          have headOutcome := execStmt_acceptedScalarLocal_prefix_observed fuel checkFuel config accepted frame context id expression origin
            (rest ++ suffix) before ambient types live regions pending expressionForm world source phase position nesting headAvailable localScalar
          cases head : execStmt fuel config frame.interpretation.environment (.letS id expression origin) before with
          | stop reason after =>
            simp only [head] at headOutcome
            obtain ⟨finalWorld, finalSource, actClock, scopeClock, sameState⟩ := headOutcome
            simp only [List.cons_append, execStmts, bind, head, Goose.Proofs.Exit.stepState]
            subst after
            exact ⟨frame, types, live, ambient, rfl, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, finalWorld, finalSource,
              EarlierCallerObservations.refl frontier before types, trivial⟩
          | escape address carriers after | jump target kind after => simp only [head] at headOutcome
          | ok flow middle =>
            simp only [head] at headOutcome
            obtain ⟨normal, scopeInst, descriptor, rootsAfter, extended, middleWorld, middleSource, middlePosition, actClock, scopeClock, middleTyped, middleRooted, middleAvailable, headObserved⟩ := headOutcome
            subst flow
            have sameRoots : rootsAfter = middleRoots := (Prod.mk.inj (Except.ok.inj (middleRooted.symm.trans headRooted))).2
            let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
            let nextTypes := registerRootType types root descriptor.ty
            let nextFrame := { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } id with rootCursor := rootsAfter }
            let nextLive := fun other => other = root ∨ live other
            have headEarlier : EarlierCallerObservations frontier before middle types nextTypes := by
              intro other earlier
              have different : other ≠ root := by
                intro same
                subst other
                exact (Nat.not_lt_of_ge frontierAct) earlier
              obtain ⟨objects, ordinals⟩ := headObserved other different
              exact ⟨objects, ordinals, by simp [nextTypes, root, registerRootType, different]⟩
            have remainingAvailable : ∀ final, rpStmts nextFrame.source (rest ++ suffix) nextFrame.rootCursor = .ok ((), final) →
                GlobalEffectsAvailable nextFrame.interpretation nextFrame.initialized final.eff := by
              intro final checked
              have equal : final = allRoots := by
                have checked' : rpStmts frame.source (rest ++ suffix) middleRoots = .ok ((), final) := by
                  simpa [nextFrame, advanceLocalFrame, sameRoots] using checked
                exact (Prod.mk.inj (Except.ok.inj (checked'.symm.trans tailRooted))).2
              subst final
              simpa [nextFrame, advanceLocalFrame] using available allRoots rootedAll
            have remainingScalar : ∀ id expression origin, .letS id expression origin ∈ rest →
                ∀ descriptor, nextFrame.source.impl.vars[id]? = some descriptor →
                  (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
              intro id expression origin member descriptor found
              exact scalar id expression origin (List.mem_cons_of_mem _ member) descriptor found
            obtain ⟨finalFrame, finalTypes, finalLive, finalAmbient, initializedEq, finalExtended, finalActClock, finalScopeClock,
              finalWorld, finalSource, finalObserved, finalFlow⟩ :=
              ih fuel (by omega) nextFrame middle ambient nextTypes nextLive
                (by simpa [nextFrame, advanceLocalFrame] using frontierAct) (by omega) middleWorld middleSource
                (by simpa [nextFrame, advanceLocalFrame] using phase) middlePosition remainingAvailable remainingScalar
            simp only [List.cons_append, execStmts, bind, head] at finalFlow finalActClock finalScopeClock finalWorld finalSource finalObserved ⊢
            cases tailRun : execStmts fuel config nextFrame.interpretation.environment (rest ++ suffix) middle with
            | stop reason after =>
              have tailRun' : execStmts fuel config frame.interpretation.environment (rest ++ suffix) middle = .stop reason after := by
                simpa [nextFrame, advanceLocalFrame] using tailRun
              simp only [tailRun, tailRun'] at finalFlow finalActClock finalScopeClock finalWorld finalSource finalObserved ⊢
              exact ⟨finalFrame, finalTypes, finalLive, finalAmbient, initializedEq,
                (fun oldRoot ty found => finalExtended oldRoot ty (extended oldRoot ty found)), actClock ▸ finalActClock,
                scopeClock ▸ finalScopeClock, finalWorld, finalSource, headEarlier.trans (Nat.le_refl _) finalObserved, trivial⟩
            | escape address carriers after | jump target kind after => simp [tailRun] at finalFlow
            | ok result after =>
              have tailRun' : execStmts fuel config frame.interpretation.environment (rest ++ suffix) middle = .ok result after := by
                simpa [nextFrame, advanceLocalFrame] using tailRun
              simp only [tailRun, tailRun'] at finalFlow finalActClock finalScopeClock finalWorld finalSource finalObserved ⊢
              obtain ⟨sameAmbient, normal, finalPosition, replay⟩ := finalFlow
              refine ⟨finalFrame, finalTypes, finalLive, finalAmbient, initializedEq,
                (fun oldRoot ty found => finalExtended oldRoot ty (extended oldRoot ty found)), actClock ▸ finalActClock,
                scopeClock ▸ finalScopeClock, finalWorld, finalSource, headEarlier.trans (Nat.le_refl _) finalObserved,
                sameAmbient, normal, finalPosition, ?_⟩
              obtain ⟨typedRest, rootedRest, sourceSame, interpretationSame⟩ := replay
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [nesting]
                simp only [typeStatements, bind, StateT.bind, middleTyped, Except.bind]
                simpa [nextFrame, advanceLocalFrame] using typedRest
              · simp only [rpStmts, bind, StateT.bind, middleRooted, Except.bind]
                simpa [nextFrame, advanceLocalFrame] using rootedRest
              · simpa [nextFrame, advanceLocalFrame] using sourceSame
              · simpa [nextFrame, advanceLocalFrame] using interpretationSame

#print axioms execStmts_scalarPrefix_fromSuffix
end Goose.Proofs.ConstructionAcceptedExecution
