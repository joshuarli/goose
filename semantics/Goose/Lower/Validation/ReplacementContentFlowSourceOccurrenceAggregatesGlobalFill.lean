import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAggregatesConsumed
import Goose.Lower.Validation.SummaryPreservationReplayAggregates
import Goose.Lower.Validation.ExpressionTypingAggregateOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem globalExpressionOccurrence_arrayFill {type : Ty} {element : Expr}
    (tables : SourceRootTables typingEnv env)
    (child : GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets element initial upper) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.fill type element) initial upper := by
  intro rooted resultType start finish before after roots typed replay ceiling ready sites targetBounds generated native metadata continuation
  obtain ⟨sameType, elementType, count, childStart, childFinish, shape, childTyped⟩ := tyExpr_fill_child typed
  subst resultType
  obtain ⟨childRoots, middleSource, elementReplay, tailReplay⟩ :=
    (st_bind_ok _ _ _ _).mp replay
  have afterEq : after = middleSource := congrArg Prod.snd ((st_pure_ok _ _ _).mp tailReplay)
  subst after
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerExpr element le initial
  have childNative := native.of_prefix (types_emitDef (.arrFill type lowered.1) le lowered.2 _ _ rfl)
  have childMetadata := metadata.of_advance (advB_emitDef (.arrFill type lowered.1) le lowered.2 _ _ rfl)
  have childContinuation := continuation.of_advance (advB_emitDef (.arrFill type lowered.1) le lowered.2 _ _ rfl)
  have childAtSite : ∃ path, DemandNodeAt siteRoot path (.expression element) := by
    obtain ⟨path, atSite⟩ := rooted
    exact ⟨path ++ [0], atSite.snoc 0 (by simp [DemandNode.child?, DemandNode.children])⟩
  obtain ⟨middle, childReady, childValue, childRoots, childLedger, childSites⟩ := child childAtSite elementType childStart childFinish
    before middleSource childRoots childTyped elementReplay ceiling ready sites targetBounds generated childNative childMetadata childContinuation
  obtain ⟨next, completed, value, retained⟩ := childReady.arrayFill elementReplay replay
    (rfl : lowerExpr element le initial = lowered) (fun live => (childValue live).bound)
  have childPath : DemandNodeAt (.expression (.fill type element)) [0] (.expression element) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  refine ⟨next, completed, value, ?_, ?_⟩
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, childReady.roots.valueSize]
      exact (advB_lowerExpr element le initial lowered.1 lowered.2 rfl).vals
    exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (childRoots index bound)
  · apply (childLedger.underRoot childPath).emitDef_sites childSites childReady completed rfl retained
    · intro live candidate member
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst candidate
      exact expression_operand_occurrence childPath elementReplay childReady (childValue live)
    · intro address same; cases same
    · intro callee arguments org same; cases same
    · intro live candidate member mutability payload reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst candidate
      have row := sourceExpressionNative tables childNative generated childTyped (rfl : lowerExpr element le initial = lowered) live
      have flat := sourceFillElement_flat (by simpa only [shape] using typed)
      exact False.elim (nativeFlat_not_reference row flat mutability payload reference)

#print axioms globalExpressionOccurrence_arrayFill

end Goose.Lower.Validation.ReplacementContentFlowSource
