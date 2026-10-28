import Goose.Proofs.ConstructionAcceptedScalarEffectSequence
import Goose.Proofs.ConstructionAcceptedEntryInvocation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedZeroGlobalScalarRun (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (noGlobals : config.module.globals.size = 0) (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : ScalarExpressionStatements implementation.body.stmts) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let initial := ExecutionState.initial
      let activated := { initial with nextAct := initial.nextAct + 1, activations := activation :: initial.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config next.interpretation.environment frame.source.impl.body.stmts after
      Goose.Proofs.Exit.stepState outcome = after ∧
      AcceptedWorld config next.initialized (Goose.Proofs.Exit.stepState outcome) [.callChannels activation []]
        (declaredRootTypes config.module) (fun _ => False) [] [] ∧
      AcceptedFrame config accepted next (Goose.Proofs.Exit.stepState outcome) (declaredRootTypes config.module) ∧
      (∀ reason final, outcome = .stop reason final → runModule (fuel + 3) config initial = .stop reason final) := by
  obtain ⟨frame, activation, moduleStep, callStep, environmentEq, world, source, position, phase, results⟩ :=
    acceptedZeroGlobalRunEntry fuel config accepted noGlobals
  let initial := ExecutionState.initial
  let activated := { initial with nextAct := initial.nextAct + 1, activations := activation :: initial.activations }
  let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let next := entryStatementsFrame config frame activated.nextScope
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
    RootInterpretation.enterScope, phase] at originFact
  obtain ⟨entry, calls, entryAt, implAt, originRest⟩ := originFact
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  have form' : ScalarExpressionStatements frame.source.impl.body.stmts := by rw [implementationEq]; exact form
  have limit : next.typing.globalLimit ≤ 0 := by simp [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, noGlobals]
  have initialBound : GlobalEffectTargetsBounded next.rootCursor.eff 0 := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have count : next.interpretation.globalCount = 0 := by rw [source.compatible.globalCount, noGlobals]
  have initialized : next.initialized = 0 := by have bound : next.initialized ≤ config.module.globals.size := source.compatible.initialized; rw [noGlobals] at bound; omega
  have available : ∀ final, rpStmts next.source frame.source.impl.body.stmts next.rootCursor = .ok ((), final) →
      GlobalEffectsAvailable next.interpretation next.initialized final.eff := by
    intro final rooted
    have bound := form'.effects_bounded config accepted next 0 position limit initialBound final rooted
    rw [initialized, ← count]
    exact (globalEffectsAvailable_iff_bounded next.interpretation final.eff).2 (by simpa only [count] using bound)
  have result := position.scalarStatements_complete accepted next frame.source.impl.body.stmts form' available fuel after
    [.callChannels activation []] (declaredRootTypes config.module) (fun _ => False) [] [] world source
  refine ⟨frame, activation, result.1, result.2.2.1, result.2.2.2, ?_⟩
  intro reason final stopped
  have action : execActivationBody (fuel + 1) config activation [] frame.source.impl.body activated = .stop reason final := by
    cases body : frame.source.impl.body with
    | mk scope statements tail =>
      simp only [body] at stopped ⊢
      have stopped' : execStmts fuel config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
          statements (ownershipResultScopeState activation scope activated) = .stop reason final := by
        simpa [entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq,
          implementationBodyFrame, body, Block.scope, Block.stmts, activated, initial] using stopped
      simp only [execActivationBody, bind]
      rw [execResultScope_ownership_continuation]
      simp only [bindAll, List.forIn_nil, pure, bind, withScope, stopped']
  have invoked : invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initial = .stop reason final := by
    rw [callStep]
    change ((finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>=
      fun carriers => deliverCarriers (fuel + 2) config.layout [] carriers 0) activated) = .stop reason final
    simp only [bind, finishActivation, action]
  rw [moduleStep]
  change ((invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
    fun carriers => publishCarriers 0 carriers) initial) = .stop reason final
  simp only [bind, invoked]

#print axioms acceptedZeroGlobalScalarRun
end Goose.Proofs.ConstructionAcceptedExecution
