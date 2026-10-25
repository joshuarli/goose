import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalControlsTypedShortCircuit

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem canonical_expressionOccurrence_shortCircuit {left right : Expr} (isAnd : Bool)
    (leftChild : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets left initial upper)
    (rightChild : ∀ targets provenance,
      let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
      let lowered := lowerExpr left le initial
      let forked := scFork isAnd lowered.1 le lowered.2
      CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot targets right
        { forked.2 with cur := some forked.1.1 } provenance) :
    CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets
      (if isAnd then .and left right else .or left right) initial upper := by
  intro source sourceCursor type start finish before after roots typed replay ceiling ready sites targetBounds generated native projects continuation
  apply canonical_typedShortCircuitOccurrence isAnd ready sites targetBounds typed replay ceiling generated native projects continuation
  · intro nextCounter childRoots childAfter childTyped childReplay childEffect childGenerated childNative childProjects childContinuation
    have leftAt : DemandNodeAt (.expression (if isAnd then .and left right else .or left right)) [0] (.expression left) := by
      cases isAnd <;> exact .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
    have leftSource : ∃ path, DemandNodeAt siteRoot path (.expression left) := by
      obtain ⟨path, location⟩ := source
      exact ⟨path ++ [0], sourcePath_append location leftAt⟩
    exact leftChild leftSource (by
      obtain ⟨path, located⟩ := sourceCursor
      refine ⟨path ++ [0], located.child ?_⟩
      cases isAnd <;> rfl) .bool start nextCounter before childAfter childRoots childTyped childReplay childEffect ready sites targetBounds childGenerated childNative childProjects childContinuation
  · intro nextCounter childRoots childBefore provenance
    dsimp only
    intro childLive childTyped childReplay childReady childGenerated childNative childSites childBounds childProjects childContinuation
    have rightAt : DemandNodeAt (.expression (if isAnd then .and left right else .or left right)) [1] (.expression right) := by
      cases isAnd <;> exact .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
    have rightSource : ∃ path, DemandNodeAt siteRoot path (.expression right) := by
      obtain ⟨path, location⟩ := source
      exact ⟨path ++ [1], sourcePath_append location rightAt⟩
    exact rightChild _ provenance rightSource (by
      obtain ⟨path, located⟩ := sourceCursor
      refine ⟨path ++ [1], located.child ?_⟩
      cases isAnd <;> simp [Fragment.child?, Fragment.children, shortCircuitChild, childLive, setCur_run]) .bool nextCounter finish childBefore after childRoots
      childTyped childReplay ceiling childReady childSites childBounds childGenerated childNative childProjects childContinuation

#print axioms canonical_expressionOccurrence_shortCircuit

end Goose.Lower.Validation.SourceReplacementWriterLedger
