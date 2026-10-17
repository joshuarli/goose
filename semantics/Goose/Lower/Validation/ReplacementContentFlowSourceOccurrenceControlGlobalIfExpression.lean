import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SourceCanonicalRootFloorsCheckpoints
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeParameters
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlTypedIfValue

import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem globalExpressionOccurrence_if {condition : Expr} {yes no : Core.Block}
    (tables : SourceRootTables typingEnv env)
    (noParameters : env.impl.params = #[])
    (parameterIdentity : ∀ index, func.parameterRoots index = [.param index])
    (valid : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (yesScopes : SourceScopesWithin scopeCount (Core.blockScopes none yes))
    (noScopes : SourceScopesWithin scopeCount (Core.blockScopes none no))
    (conditionChild : GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets condition initial upper)
    (blockChild : ∀ body, body = yes ∨ body = no → ∀ state provenance,
      GlobalBlockOccurrenceReplayAt (exprEnv typingEnv) env results vt func returnTypes slots target scopeCount siteRoot siteTargets none [] true body state provenance) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.ifE condition yes no) initial upper := by
  intro source type start finish before after roots typed replay ceiling ready sites targetBounds generated native projects continuation
  refine typedIfExpressionOccurrence ready sites targetBounds typed replay ceiling generated native
    ⟨returnTypes, by rw [tables.moduleEq, tables.variablesEq]⟩ ?_ projects continuation ?_ ?_
  · intro recipeMember row rowMember same
    obtain ⟨path, location⟩ := source
    rcases row with ⟨id, declared⟩
    dsimp only at same
    subst id
    have projected := projects.ifE_row valid condition yes no location replay recipeMember rowMember
    exact genericRecipeMetadataBounds roots declared noParameters parameterIdentity projected
  · intro nextCounter childRoots childAfter childTyped childReplay childCeiling childGenerated childNative childProjects childContinuation
    have conditionAt : DemandNodeAt (.expression (.ifE condition yes no)) [0] (.expression condition) :=
      .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
    have conditionSource : ∃ path, DemandNodeAt siteRoot path (.expression condition) := by
      obtain ⟨path, location⟩ := source
      exact ⟨path ++ [0], sourcePath_append location conditionAt⟩
    exact conditionChild conditionSource .bool start nextCounter before childAfter childRoots childTyped childReplay childCeiling ready sites targetBounds childGenerated childNative childProjects childContinuation
  · intro body bodyMember tn1 tn2 childRoots range childBefore childAfter state provenance
      childTyped childReplay childCeiling childReady checkpoint childGenerated childNative childSites childBounds childProjects childContinuation
    have scopes : SourceScopesWithin scopeCount (Core.blockScopes none body) := by
      rcases bodyMember with rfl | rfl
      · exact yesScopes
      · exact noScopes
    have bodySource : ∃ path, DemandNodeAt siteRoot path (.block body) := by
      obtain ⟨path, location⟩ := source
      rcases bodyMember with rfl | rfl
      · exact ⟨path ++ [1], sourcePath_append location (.child (by simp [DemandNode.child?, DemandNode.children]) (.here _))⟩
      · exact ⟨path ++ [2], sourcePath_append location (.child (by simp [DemandNode.child?, DemandNode.children]) (.here _))⟩
    obtain ⟨next, nextReady, nextValue, nextRoots, _transfer, ledger, finalSites⟩ :=
      blockChild body bodyMember state provenance bodySource type tn1 tn2 childBefore childAfter childRoots range
        childTyped childReplay childCeiling scopes (by simp) (by simp) (by simp)
        (by intro outside; simp [exprEnv] at outside) childReady childSites childBounds childGenerated trivial trivial trivial (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets]) childNative childProjects childContinuation
    exact ⟨next, nextReady, nextValue rfl, nextRoots, ledger, finalSites⟩

#print axioms globalExpressionOccurrence_if

end Goose.Lower.Validation.ReplacementContentFlowSource
