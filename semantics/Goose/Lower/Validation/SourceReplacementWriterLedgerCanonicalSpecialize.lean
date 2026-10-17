import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem canonical_statement_occurrence_context_of_global {ownerRoot : Fragment} {ownerInitial baseline : LS} {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {statement : Stmt} {initial : LS} {upper : Prov}
    (replayed : CanonicalGlobalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt
      (lowerContextAt env.mod env.ctx env.impl) env.impl.results.toList
      (typedContextSlotUpper env.mod env.ctx env.impl) target scopeCount siteRoot siteTargets
      loop scope statement initial upper) :
    CanonicalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets
      loop scope statement initial upper := by
  intro source cursor output start finish before after typed replay ceiling scopes stack ready sites targets
    generated loopBounds loopReplay counter included native metadata continuation
  obtain ⟨next, nextReady, retained, transfer, ledger, nextSites⟩ :=
    replayed source cursor output start finish before after typed replay ceiling scopes stack ready sites targets
      generated loopBounds loopReplay counter included native metadata continuation
  exact ⟨next, nextReady, retained, transfer _, ledger, nextSites⟩

#print axioms canonical_statement_occurrence_context_of_global

end Goose.Lower.Validation.SourceReplacementWriterLedger
