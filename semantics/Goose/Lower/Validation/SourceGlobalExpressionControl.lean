import Goose.Lower.Validation.SourceGlobalReplayContracts
import Goose.Lower.Validation.SummaryPreservationReplayNativeIf

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem globalExpressionReplay_if {condition : Expr} {yes no : Core.Block}
    (yesScopes : SourceScopesWithin scopeCount (Core.blockScopes none yes))
    (noScopes : SourceScopesWithin scopeCount (Core.blockScopes none no))
    (conditionChild : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount condition initial upper)
    (blockChild : ∀ body state provenance,
      (let le := lowerEnv env.mod env.impl.vars returnTypes
       let lowered := lowerExpr condition le initial
       let forked := (fork lowered.1 le lowered.2).2
       let yesStart := { forked with cur := some lowered.2.blocks.size }
       let yesResult := lowerBlock none [] true yes le yesStart
       (body = yes ∧ state = yesStart) ∨
         (body = no ∧ state = { yesResult.2 with cur := some (lowered.2.blocks.size + 1) })) →
      GlobalBlockReplayAt (exprEnv typingEnv) env results vt func returnTypes slots target scopeCount none [] true body state provenance) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.ifE condition yes no) initial upper := by
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
    obtain ⟨next, nextReady, nextValue, nextRoots⟩ :=
      blockChild body state provenance checkpoint type tn1 tn2 childBefore childAfter childRoots range
        childTyped childReplay childCeiling scopes (by simp) (by simp) (by simp)
        (by intro outside; simp [exprEnv] at outside) childReady childGenerated trivial trivial childNative
    exact ⟨next, nextReady, nextValue rfl, nextRoots⟩

theorem globalExpressionReplay_block {body : Core.Block}
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body))
    (child : GlobalBlockReplayAt (exprEnv typingEnv) env results vt func returnTypes slots target scopeCount none [] true body initial upper) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.blockE body) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  obtain ⟨⟨bodyRoots, range⟩, bodyAfter, bodyReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have same := (st_pure_ok _ _ _).mp tail
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ :=
    child type start finish before after roots range typed bodyReplay ceiling scopes
      (by simp) (by simp) (by simp) (by intro outside; simp [exprEnv] at outside) ready generated trivial trivial native
  exact ⟨next, nextReady, nextValue rfl, nextRoots⟩

#print axioms globalExpressionReplay_if
#print axioms globalExpressionReplay_block

end Goose.Lower.Validation.SummaryPreservation
