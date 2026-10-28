import Goose.Proofs.ConstructionAcceptedEarlierScalarTail
import Goose.Proofs.ConstructionAcceptedCalleeBody
import Goose.Proofs.ConstructionAcceptedRegisterTail
import Goose.Proofs.ConstructionAcceptedScalarLocalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_checkedSequence_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier scope : Nat) (statements : List Stmt) (expression : Expr) (ty : Ty)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, statements, some expression⟩)
    (frontierBound : frontier ≤ frame.interpretation.environment.act)
    (channels : frame.interpretation.environment.channels = [.register ty])
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (tailForm : AcceptedBinaryExpression expression)
    (bodyType : ∃ declared, typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter =
      .ok ([ty], declared))
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, statements, some expression⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff)
    (ambientAllowed : OwnershipAmbient → Prop) (ambientInitial : ambientAllowed ambient)
    (sequence : ∀ n, n < fuel →
      let child := entryStatementsFrame config frame state.nextScope
      let before := ownershipResultScopeState frame.interpretation.environment scope state
      AcceptedWorld config child.initialized before ambient types live regions pending →
      AcceptedFrame config accepted child before types → child.phase = .implementation context →
      SourcePosition accepted child (.statements statements) →
      (∀ rootsAfter, rpStmts child.source statements child.rootCursor = .ok ((), rootsAfter) →
        GlobalEffectsAvailable child.interpretation child.initialized rootsAfter.eff) →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextAmbient : OwnershipAmbient),
        let outcome := execStmts n config child.interpretation.environment statements before
        let after := Goose.Proofs.Exit.stepState outcome
        next.initialized = child.initialized ∧ ambientAllowed nextAmbient ∧ RootTypesExtend types nextTypes ∧ before.nextAct ≤ after.nextAct ∧
        before.nextScope ≤ after.nextScope ∧ AcceptedWorld config next.initialized after nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted next after nextTypes ∧ EarlierCallerObservations frontier before after types nextTypes ∧
        (match outcome with
         | .ok flow _ => nextAmbient = ambient ∧ flow = .normal .unit ∧ SourcePosition accepted next (.statements []) ∧ ScalarLocalReplay child next statements
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      ambientAllowed nextAmbient ∧
      let outcome := execActivationBody fuel config frame.interpretation.environment [] ⟨scope, statements, some expression⟩ state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  let activation := frame.interpretation.environment
  let child := entryStatementsFrame config frame state.nextScope
  have bodyScope : frame.source.impl.body.scope = scope := by simp [body, Block.scope]
  have bodyStatements : frame.source.impl.body.stmts = statements := by simp [body, Block.stmts]
  obtain ⟨scopeWorld, scopeSource, scopePosition⟩ := acceptedCalleeBodyScope config accepted frame context state ambient types live
    regions pending world source phase parameters scopes cursor
  rw [bodyScope] at scopeWorld scopeSource
  rw [bodyStatements] at scopePosition
  change AcceptedWorld config child.initialized (ownershipResultScopeState activation scope state) ambient types live regions pending at scopeWorld
  change AcceptedFrame config accepted child (ownershipResultScopeState activation scope state) types at scopeSource
  change SourcePosition accepted child (.statements statements) at scopePosition
  have childInterpretation : child.interpretation = frame.interpretation.enterScope scope state.nextScope := by
    simp [child, entryStatementsFrame, bodyScope]
  have childInitialized : child.initialized = frame.initialized := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame]
  have childPhase : child.phase = .implementation context := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, phase]
  have childTyping : child.typing = { frame.typing with scope := scope } := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, bodyScope]
  have childFuel : child.typingFuel = frame.typingFuel - 1 := by
    have fixed := congrArg (fun f : ConstructionSourceFrame => f.typingFuel) bodyFrame
    simp only [implementationBodyFrame] at fixed
    simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, ← fixed]
  have depth : frame.typingFuel = 4096 := by
    have fixed := congrArg (fun f : ConstructionSourceFrame => f.typingFuel) bodyFrame
    simpa [implementationBodyFrame] using fixed.symm
  have childFuel' : child.typingFuel = 4095 := by simp [childFuel, depth]
  have childCounter : child.typingCounter = frame.typingCounter := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame]
  have childSource : child.source = { frame.source with scopes := scope :: frame.source.scopes } := by
    simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, bodyScope]
  have childCursor : child.rootCursor = frame.rootCursor := by simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame]
  have childEnvironment : child.interpretation.environment =
      { activation with scopes := (scope, state.nextScope) :: activation.scopes } := by
    simp [childInterpretation, RootInterpretation.enterScope, activation]
  obtain ⟨middleRoots, tailRoots, lastRoots, rootedStatements, rootedTail, middleAvailable, tailAvailable⟩ :=
    position.blockTail_effects accepted frame scope statements expression available
  have seqAvailable : ∀ rootsAfter, rpStmts child.source statements child.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable child.interpretation child.initialized rootsAfter.eff := by
    intro rootsAfter rooted
    have same : rootsAfter = middleRoots := by
      rw [childSource, childCursor] at rooted
      exact (Prod.mk.inj (Except.ok.inj (rooted.symm.trans rootedStatements))).2
    subst rootsAfter
    simpa [childInterpretation, RootInterpretation.enterScope, childInitialized, GlobalEffectsAvailable] using middleAvailable
  cases fuel with
  | zero =>
    simp only [execActivationBody, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, ambient, ambientInitial, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals, EarlierCallerObservations.refl frontier state types, trivial⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      have clear : FutureGlobalsClear config frame.initialized (ownershipResultScopeState activation scope state) := by
        exact scopeSource.futureGlobals
      simp only [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll,
        List.forIn_nil, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨types, live, ambient, ambientInitial, (fun _ _ found => found), Nat.le_refl _, Nat.le_succ _, scopeWorld, clear,
        EarlierCallerObservations.enterScope frontier activation scope state types, trivial⟩
    | succ fuel =>
      obtain ⟨final, finalTypes, finalLive, finalAmbient, sameInitialized, allowed, extend, finalActClock, finalScopeClock, finalWorld, finalSource, finalObserved, finalFlow⟩ :=
        sequence (fuel + 1) (by omega) scopeWorld scopeSource childPhase scopePosition seqAvailable
      change final.initialized = child.initialized at sameInitialized
      cases execution : execStmts (fuel + 1) config (entryStatementsFrame config frame state.nextScope).interpretation.environment statements
          (ownershipResultScopeState frame.interpretation.environment scope state) with
      | stop reason after =>
        simp only [execution, Goose.Proofs.Exit.stepState] at finalActClock finalScopeClock finalWorld finalSource finalObserved finalFlow
        have stopped : execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ state = .stop reason after := by
          apply execActivationBody_register_statements_stopped
          have execution' : execStmts (fuel + 1) config child.interpretation.environment statements
              (ownershipResultScopeState activation scope state) = .stop reason after := execution
          simpa [childEnvironment] using execution'
        rw [stopped]
        have actBound : state.nextAct ≤ after.nextAct := by simpa [ownershipResultScopeState] using finalActClock
        have scopeBound : state.nextScope ≤ after.nextScope := by
          exact Nat.le_trans (Nat.le_succ _) (by simpa [ownershipResultScopeState] using finalScopeClock)
        exact ⟨finalTypes, finalLive, finalAmbient, allowed, extend, actBound, scopeBound, sameInitialized ▸ finalWorld,
          sameInitialized ▸ finalSource.futureGlobals,
          (EarlierCallerObservations.enterScope frontier activation scope state types).trans (Nat.le_refl _) finalObserved, trivial⟩
      | escape address carriers after | jump target kind after => simp [execution] at finalFlow
      | ok flow after =>
        simp only [execution, Goose.Proofs.Exit.stepState] at finalActClock finalScopeClock finalWorld finalSource finalObserved finalFlow
        obtain ⟨sameAmbient, normal, _, replay⟩ := finalFlow
        subst finalAmbient
        subst flow
        have finalAvailable : ∀ roots afterRoots, rpExpr final.source expression final.rootCursor = .ok (roots, afterRoots) →
            GlobalEffectsAvailable final.interpretation final.initialized afterRoots.eff := by
          intro roots afterRoots rooted
          obtain ⟨_, rootedReplay, sourceSame, interpretationSame⟩ := replay
          change final.interpretation = child.interpretation at interpretationSame
          rw [sourceSame, childSource] at rooted
          have sameMiddle : final.rootCursor = middleRoots := by
            rw [childSource, childCursor] at rootedReplay
            exact (Prod.mk.inj (Except.ok.inj (rootedReplay.symm.trans rootedStatements))).2
          rw [sameMiddle] at rooted
          have sameAfter : afterRoots = lastRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans rootedTail))).2
          subst afterRoots
          simpa [interpretationSame, childInterpretation, RootInterpretation.enterScope, childInitialized, sameInitialized, GlobalEffectsAvailable] using tailAvailable
        obtain ⟨tailTy, roots, typingAfter, rootsAfter, checked⟩ := replay.blockTail_checked accepted frame child final scope 4095 statements expression
          position (by simp [depth]) childTyping childFuel' childCounter childSource childCursor tailForm finalAvailable
        have sameTy : tailTy = ty := by
          obtain ⟨declared, expected⟩ := bodyType
          obtain ⟨next, middleTyping, middleRoots', actualTypes, actualAfter, actualRoots, actualRootsAfter,
            blockTyped, typedStatements, rootedStatements', typedTail, rootedTail'⟩ :=
            position.blockTail_checks accepted frame scope 4095 statements expression (by simp [depth])
          have typesEqual : actualTypes = [ty] := (Prod.mk.inj (Except.ok.inj (blockTyped.symm.trans expected))).1
          obtain ⟨typedReplay, rootedReplay, _, _⟩ := replay
          rw [childTyping, childFuel', childCounter] at typedReplay
          have typingSame := Prod.mk.inj (Except.ok.inj (typedReplay.symm.trans typedStatements))
          have tailTyped := checked.typing
          rw [typingSame.1, typingSame.2] at tailTyped
          rw [typesEqual] at typedTail
          exact List.cons.inj (Prod.mk.inj (Except.ok.inj (tailTyped.symm.trans typedTail))).1 |>.1
        subst tailTy
        have tailSource := finalSource.withTypingFuel 4095
        have finalEnvironment : final.interpretation.environment =
            { activation with scopes := (scope, state.nextScope) :: activation.scopes } := by
          exact congrArg RootInterpretation.environment replay.2.2.2 |>.trans childEnvironment
        have normal : execStmts (fuel + 1) config final.interpretation.environment statements
            (ownershipResultScopeState activation scope state) = .ok (.normal .unit) after := by
          simpa [← replay.2.2.2] using execution
        have tailClocks := checkedRegisterTail_activation_clocks tailForm fuel config accepted { final with typingFuel := 4095 }
          activation scope statements state after ambient finalTypes finalLive regions pending ty channels finalEnvironment normal
          finalWorld tailSource roots typingAfter rootsAfter checked
        have tailObserved := execActivationBody_scalarTail_earlierObservations tailForm fuel config accepted { final with typingFuel := 4095 }
          activation scope statements state after ambient finalTypes finalLive regions pending ty frontier frontierBound channels finalEnvironment normal
          finalWorld tailSource roots typingAfter rootsAfter checked
        have tailResult := checkedRegisterTail_activation_world tailForm fuel config accepted { final with typingFuel := 4095 }
          activation scope statements state after ambient finalTypes finalLive regions pending ty channels finalEnvironment normal
          finalWorld tailSource roots typingAfter rootsAfter checked
        cases result : execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ state with
        | stop reason stopped =>
          simp only [result, Goose.Proofs.Exit.stepState] at tailResult tailClocks tailObserved
          have actBound : state.nextAct ≤ stopped.nextAct := by rw [tailClocks.1]; simpa [ownershipResultScopeState] using finalActClock
          have scopeBound : state.nextScope ≤ stopped.nextScope := by rw [tailClocks.2]; exact Nat.le_trans (Nat.le_succ _) (by simpa [ownershipResultScopeState] using finalScopeClock)
          exact ⟨finalTypes, finalLive, ambient, ambientInitial, extend, actBound, scopeBound, sameInitialized ▸ tailResult.1, sameInitialized ▸ tailResult.2,
            ((EarlierCallerObservations.enterScope frontier activation scope state types).trans (Nat.le_refl _) finalObserved).trans (Nat.le_refl _) tailObserved, trivial⟩
        | escape address carriers after | jump target kind after => simp [result] at tailResult
        | ok carriers done =>
          simp only [result, Goose.Proofs.Exit.stepState] at tailResult tailClocks tailObserved
          obtain ⟨value, same, acceptedValue, tailWorld, tailClear⟩ := tailResult
          have actBound : state.nextAct ≤ done.nextAct := by rw [tailClocks.1]; simpa [ownershipResultScopeState] using finalActClock
          have scopeBound : state.nextScope ≤ done.nextScope := by rw [tailClocks.2]; exact Nat.le_trans (Nat.le_succ _) (by simpa [ownershipResultScopeState] using finalScopeClock)
          exact ⟨finalTypes, _, ambient, ambientInitial, extend, actBound, scopeBound, sameInitialized ▸ tailWorld, sameInitialized ▸ tailClear,
            ((EarlierCallerObservations.enterScope frontier activation scope state types).trans (Nat.le_refl _) finalObserved).trans (Nat.le_refl _) tailObserved,
            rfl, value, same, acceptedValue.represented⟩


#print axioms execActivationBody_checkedSequence_earlier
end Goose.Proofs.ConstructionAcceptedExecution
