import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlSteps
import Goose.Lower.Validation.SummaryPreservationSourceControlKernels

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem statementOccurrence_returnUnit {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov} {origin : OriginId}
    (tables : SourceRootTables typingEnv env) :
    StatementOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop scope (.ret none origin) initial upper := by
  intro _ output start finish before after typed replay ceiling _scopes stack ready sites _targets generated _loopBounds _loopReplay _counter _included native metadata continuation
  have bounded := stack (tyStmt_returnUnit_facts typed).1
  have completed := ready.returnUnit loop typed replay (tables.mutation_origin_bound typed) bounded
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let left := Goose.Lower.leaveTo 0 le initial
  have whole : lowerStmt loop (.ret none origin) le initial = emitTerm (.ret [] (some origin)) le left.2 := by
    simp only [lowerStmt, bind_run, pure_run, left]
  have leaveLedger : OccurrenceLedger env (.statement (.ret none origin)) (lowerContextAt env.mod env.ctx env.impl) vt upper initial left.2 := by
    exact occurrenceLedger_leaveAll _ le initial _ _ rfl
  have leaveSites : OccurrenceSitesBuilder env siteRoot siteTargets le left.2 (lowerContextAt env.mod env.ctx env.impl) vt upper :=
    occurrenceSites_leaveAll _ sites
  have ledger := leaveLedger.trans (emitsOnly_emitTerm (.ret [] (some origin))
    (InstructionOccurrences.term _ _ _ _ _ _) le left.2 _ _ rfl)
  have finalSites := leaveSites.emitTerm (by simp [Term.successors]) (rfl : emitTerm (.ret [] (some origin)) le left.2 = _)
  refine ⟨upper, completed, (fun _ _ => rfl), ?_, ?_, ?_⟩
  · intro declared _ prior
    exact prior.return_unit loop ready.current
  · rw [whole]
    exact ledger
  · rw [whole]
    exact finalSites

end Goose.Lower.Validation.ReplacementContentFlowSource
