import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlBlocks

import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem globalExpressionOccurrence_block {body : Core.Block}
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body))
    (child : GlobalBlockOccurrenceReplayAt (exprEnv typingEnv) env results vt func returnTypes slots target scopeCount siteRoot siteTargets none [] true body initial upper) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.blockE body) initial upper := by
  intro source type start finish before after roots typed replay ceiling ready sites targetBounds generated native projects continuation
  obtain ⟨⟨bodyRoots, range⟩, bodyAfter, bodyReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have same := (st_pure_ok _ _ _).mp tail
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  have bodyAt : DemandNodeAt (.expression (.blockE body)) [0] (.block body) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have bodySource : ∃ path, DemandNodeAt siteRoot path (.block body) := by
    obtain ⟨path, location⟩ := source
    exact ⟨path ++ [0], sourcePath_append location bodyAt⟩
  obtain ⟨next, nextReady, nextValue, nextRoots, _transfer, ledger, finalSites⟩ :=
    child bodySource type start finish before after roots range typed bodyReplay ceiling scopes
      (by simp) (by simp) (by simp) (by intro outside; simp [exprEnv] at outside) ready sites targetBounds generated trivial trivial trivial (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets]) native projects continuation
  exact ⟨next, nextReady, nextValue rfl, nextRoots, ledger.underRoot bodyAt, finalSites⟩

#print axioms globalExpressionOccurrence_block

end Goose.Lower.Validation.ReplacementContentFlowSource
