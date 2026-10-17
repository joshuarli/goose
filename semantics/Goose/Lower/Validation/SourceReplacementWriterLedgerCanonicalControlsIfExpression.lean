import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment
import Goose.Lower.Validation.SourceRootBounds
import Goose.Lower.Validation.SourceCanonicalRootFloorsCheckpoints
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeParameters
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalControlsTypedIfValue
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalControlsSourcePaths

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem canonical_expressionOccurrence_if {condition : Expr} {yes no : Core.Block}
    {contextIndex : ContextId}
    (context : SourceContextEnvironment typingEnv env contextIndex)
    (valid : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (yesScopes : SourceScopesWithin scopeCount (Core.blockScopes none yes))
    (noScopes : SourceScopesWithin scopeCount (Core.blockScopes none no))
    (conditionChild : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets condition initial upper)
    (blockChild : ∀ body, body = yes ∨ body = no → ∀ state provenance,
      CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline (exprEnv typingEnv) env results vt target scopeCount siteRoot siteTargets none [] true body state provenance) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.ifE condition yes no) initial upper := by
  intro source sourceCursor type start finish before after roots typed replay ceiling ready sites targetBounds generated native projects continuation
  refine canonical_typedIfExpressionOccurrence ready sites targetBounds typed replay ceiling generated native
    ⟨env.impl.results.toList, by rw [context.tables.moduleEq, context.tables.variablesEq]⟩ ?_ projects continuation ?_ ?_
  · intro recipeMember row rowMember same
    obtain ⟨path, location⟩ := source
    rcases row with ⟨id, declared⟩
    dsimp only at same
    subst id
    have projected := projects.ifE_row valid condition yes no location replay recipeMember rowMember
    exact contextualRecipeMetadataBounds env.mod env.ctx env.impl roots declared
      (source_expr_param_bounds (.ifE condition yes no) context.tables context.accepted context.contextRow
        context.implementationRow typed replay) projected
  · intro nextCounter childRoots childAfter childTyped childReplay childCeiling childGenerated childNative childProjects childContinuation
    have conditionAt : DemandNodeAt (.expression (.ifE condition yes no)) [0] (.expression condition) :=
      .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
    have conditionSource : ∃ path, DemandNodeAt siteRoot path (.expression condition) := by
      obtain ⟨path, location⟩ := source
      exact ⟨path ++ [0], sourcePath_append location conditionAt⟩
    exact conditionChild conditionSource (by
      obtain ⟨path, located⟩ := sourceCursor
      exact ⟨path ++ [0], located.child rfl⟩) .bool start nextCounter before childAfter childRoots childTyped childReplay childCeiling ready sites targetBounds childGenerated childNative childProjects childContinuation
  · intro body bodyMember tn1 tn2 childRoots range childBefore childAfter state provenance
      childLive childTyped childReplay childCeiling childReady checkpoint childGenerated childNative childSites childBounds childProjects childContinuation
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
      blockChild body bodyMember state provenance bodySource (by
        obtain ⟨path, located⟩ := sourceCursor
        rcases checkpoint with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨path ++ [1], located.child ?_⟩
          exact canonical_ifExpression_yes_child _ _ _ _ _ childLive
        · refine ⟨path ++ [2], located.child ?_⟩
          exact canonical_ifExpression_no_child _ _ _ _ _ childLive) type tn1 tn2 childBefore childAfter childRoots range
        childTyped childReplay childCeiling scopes (by simp) (by simp) (by simp)
        (by intro outside; simp [exprEnv] at outside) childReady childSites childBounds childGenerated trivial trivial trivial (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets]) childNative childProjects childContinuation
    exact ⟨next, nextReady, nextValue rfl, nextRoots, ledger, finalSites⟩

#print axioms canonical_expressionOccurrence_if

end Goose.Lower.Validation.SourceReplacementWriterLedger
