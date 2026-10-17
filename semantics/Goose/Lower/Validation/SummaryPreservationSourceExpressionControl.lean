import Goose.Lower.Validation.SummaryPreservationSourceBlockContracts
import Goose.Lower.Validation.SummaryPreservationReplayNativeIf

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem expressionReplay_if {condition : Expr} {yes no : Core.Block}
    (yesScopes : SourceScopesWithin scopeCount (Core.blockScopes none yes))
    (noScopes : SourceScopesWithin scopeCount (Core.blockScopes none no))
    (conditionChild : ExpressionReplayAt typingEnv env results vt target scopeCount condition initial upper)
    (blockChild : ∀ body, body = yes ∨ body = no → ∀ state provenance,
      BlockReplayAt (exprEnv typingEnv) env results vt target scopeCount none [] true body state provenance) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.ifE condition yes no) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedIfExpressionNative typed replay ceiling generated native
  · intro nextCounter childRoots childAfter childTyped childReplay childCeiling childGenerated childNative
    exact conditionChild .bool start nextCounter before childAfter childRoots childTyped childReplay childCeiling ready childGenerated childNative
  · intro body bodyMember tn1 tn2 childRoots range childBefore childAfter state provenance
      childTyped childReplay childCeiling childReady checkpoint childGenerated childNative
    have scopes : SourceScopesWithin scopeCount (Core.blockScopes none body) := by
      rcases bodyMember with rfl | rfl
      · exact yesScopes
      · exact noScopes
    obtain ⟨next, nextReady, nextValue, nextRoots, _transfer⟩ :=
      blockChild body bodyMember state provenance type tn1 tn2 childBefore childAfter childRoots range
        childTyped childReplay childCeiling scopes (by simp) (by simp) (by simp)
        (by intro outside; simp [exprEnv] at outside) childReady childGenerated trivial childNative
    exact ⟨next, nextReady, nextValue rfl, nextRoots⟩

theorem expressionReplay_block {body : Core.Block}
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body))
    (child : BlockReplayAt (exprEnv typingEnv) env results vt target scopeCount none [] true body initial upper) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.blockE body) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  obtain ⟨⟨bodyRoots, range⟩, bodyAfter, bodyReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have same := (st_pure_ok _ _ _).mp tail
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  obtain ⟨next, nextReady, nextValue, nextRoots, _transfer⟩ :=
    child type start finish before after roots range typed bodyReplay ceiling scopes
      (by simp) (by simp) (by simp) (by intro outside; simp [exprEnv] at outside) ready generated trivial native
  exact ⟨next, nextReady, nextValue rfl, nextRoots⟩

#print axioms expressionReplay_if
#print axioms expressionReplay_block

end Goose.Lower.Validation.SummaryPreservation
