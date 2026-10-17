import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlTypedShortCircuit

import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem globalExpressionOccurrence_shortCircuit {left right : Expr} (isAnd : Bool)
    (leftChild : GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets left initial upper)
    (rightChild : ∀ targets provenance,
      let le := lowerEnv env.mod env.impl.vars returnTypes
      let lowered := lowerExpr left le initial
      let forked := scFork isAnd lowered.1 le lowered.2
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot targets right
        { forked.2 with cur := some forked.1.1 } provenance) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      (if isAnd then .and left right else .or left right) initial upper := by
  intro source type start finish before after roots typed replay ceiling ready sites targetBounds generated native projects continuation
  apply typedShortCircuitOccurrence isAnd ready sites targetBounds typed replay ceiling generated native projects continuation
  · intro nextCounter childRoots childAfter childTyped childReplay childEffect childGenerated childNative childProjects childContinuation
    have leftAt : DemandNodeAt (.expression (if isAnd then .and left right else .or left right)) [0] (.expression left) := by
      cases isAnd <;> exact .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
    have leftSource : ∃ path, DemandNodeAt siteRoot path (.expression left) := by
      obtain ⟨path, location⟩ := source
      exact ⟨path ++ [0], sourcePath_append location leftAt⟩
    exact leftChild leftSource .bool start nextCounter before childAfter childRoots childTyped childReplay childEffect ready sites targetBounds childGenerated childNative childProjects childContinuation
  · intro nextCounter childRoots childBefore provenance
    dsimp only
    intro childTyped childReplay childReady childGenerated childNative childSites childBounds childProjects childContinuation
    have rightAt : DemandNodeAt (.expression (if isAnd then .and left right else .or left right)) [1] (.expression right) := by
      cases isAnd <;> exact .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
    have rightSource : ∃ path, DemandNodeAt siteRoot path (.expression right) := by
      obtain ⟨path, location⟩ := source
      exact ⟨path ++ [1], sourcePath_append location rightAt⟩
    exact rightChild _ provenance rightSource .bool nextCounter finish childBefore after childRoots
      childTyped childReplay ceiling childReady childSites childBounds childGenerated childNative childProjects childContinuation

#print axioms globalExpressionOccurrence_shortCircuit

end Goose.Lower.Validation.ReplacementContentFlowSource
