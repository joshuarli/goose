import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

theorem statement_occurrence_context_of_global {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {statement : Stmt} {initial : LS} {upper : Prov}
    (replayed : GlobalStatementOccurrenceReplayAt typingEnv env results vt
      (lowerContextAt env.mod env.ctx env.impl) env.impl.results.toList
      (typedContextSlotUpper env.mod env.ctx env.impl) target scopeCount siteRoot siteTargets
      loop scope statement initial upper) :
    StatementOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets
      loop scope statement initial upper := by
  intro source output start finish before after typed replay ceiling scopes stack ready sites targets
    generated loopBounds loopReplay counter included native metadata continuation
  obtain ⟨next, nextReady, retained, transfer, ledger, nextSites⟩ :=
    replayed source output start finish before after typed replay ceiling scopes stack ready sites targets
      generated loopBounds loopReplay counter included native metadata continuation
  exact ⟨next, nextReady, retained, transfer _, ledger, nextSites⟩

#print axioms statement_occurrence_context_of_global

end Goose.Lower.Validation.ReplacementContentFlowSource
