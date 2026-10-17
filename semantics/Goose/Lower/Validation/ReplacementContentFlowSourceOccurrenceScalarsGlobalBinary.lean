import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsConsumed
import Goose.Lower.Validation.SummaryPreservationReplayScalar
import Goose.Lower.Validation.ScalarTyping
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem globalExpressionOccurrence_binary {left right : Expr} (op : BinOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (leftChild : GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets left initial upper)
    (rightChild : ∀ provenance, GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets right
      (lowerExpr left (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.bin op left right origin) initial upper := by
  intro rooted type start finish before after sourceRoots source replayed wholeEffect ready sites targetBounds generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  have originBound : origin < le.mod.origins.size := by
    simpa only [le, lowerEnv, ← tables.moduleEq] using Core.tyExpr_bin_success_origin_bound source
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, integer, leftTyped, rightTyped, shape⟩ :=
    tyExpr_bin_children source
  subst type
  obtain ⟨leftRoots, sourceMiddle, leftReplay, rest⟩ := (st_bind_ok _ _ _ _).mp replayed
  obtain ⟨rightRoots, sourceAfter, rightReplay, _⟩ := (st_bind_ok _ _ _ _).mp rest
  have exactReplay := rpExpr_bin_after_operands leftReplay rightReplay (op := op) (origin := origin)
  rw [exactReplay] at replayed
  cases replayed
  have rightEffect : EffectRefinement func sourceAfter.eff target := by
    cases aborts : op.mayAbort with
    | false => simpa only [aborts, Bool.false_eq_true, ite_false] using wholeEffect
    | true =>
      have bound : EffectRefinement func { sourceAfter.eff with aborts := true } target := by
        simpa only [aborts, ite_true] using wholeEffect
      exact ⟨bound.reads, bound.writes, bound.grows, bound.shrinks, bound.rebinds,
        fun _ => bound.aborts rfl, bound.outputs, bound.unknown⟩
  have leftEffect := effectRefinement_before_expression rightReplay rightEffect
  let leftRun := lowerExpr left le initial
  let rightRun := lowerExpr right le leftRun.2
  have tailTypes : TypeRun (do
      let ty ← intTyOf leftRun.1
      Goose.Lower.emitDef (.bin op ty leftRun.1 rightRun.1 (some origin))) :=
    TypeRun.bind (types_intTyOf _) fun _ => types_emitDef _
  have tailAdvance : AdvB (do
      let ty ← intTyOf leftRun.1
      Goose.Lower.emitDef (.bin op ty leftRun.1 rightRun.1 (some origin))) :=
    AdvB.bind (advB_intTyOf _) fun _ => advB_emitDef _
  have rightNative := native.of_prefix (tailTypes le rightRun.2 _ _ rfl)
  have rightMetadata := metadata.of_advance (tailAdvance le rightRun.2 _ _ rfl)
  have rightContinuation := continuation.of_advance (tailAdvance le rightRun.2 _ _ rfl)
  have leftMetadata := rightMetadata.of_advance (advB_lowerExpr right le leftRun.2 rightRun.1 rightRun.2 rfl)
  have leftContinuation := rightContinuation.of_advance (advB_lowerExpr right le leftRun.2 rightRun.1 rightRun.2 rfl)
  have leftNative := rightNative.of_prefix (types_lowerExpr right le leftRun.2 rightRun.1 rightRun.2 rfl)
  have leftAtSite : ∃ path, DemandNodeAt siteRoot path (.expression left) := by
    obtain ⟨path, atSite⟩ := rooted
    exact ⟨path ++ [0], atSite.snoc 0 (by simp [DemandNode.child?, DemandNode.children])⟩
  have rightAtSite : ∃ path, DemandNodeAt siteRoot path (.expression right) := by
    obtain ⟨path, atSite⟩ := rooted
    exact ⟨path ++ [1], atSite.snoc 1 (by simp [DemandNode.child?, DemandNode.children])⟩
  obtain ⟨middle, middleReady, leftValue, middleRoots, leftLedger, leftSites⟩ :=
    leftChild leftAtSite (.int integer) leftStart leftFinish before sourceMiddle leftRoots leftTyped leftReplay leftEffect ready sites targetBounds generated leftNative leftMetadata leftContinuation
  obtain ⟨last, lastReady, rightValue, lastRoots, rightLedger, rightSites⟩ :=
    rightChild middle rightAtSite (.int integer) rightStart rightFinish sourceMiddle sourceAfter rightRoots rightTyped rightReplay rightEffect
      middleReady leftSites (targetBounds.mono (advB_lowerExpr left le initial leftRun.1 leftRun.2 rfl).ext)
      (generated.lowerExpr left rfl) rightNative rightMetadata rightContinuation
  have typeRun : intTyOf leftRun.1 le rightRun.2 = ((intTyOf leftRun.1 le rightRun.2).1, rightRun.2) :=
    Prod.ext rfl (by
      simp only [intTyOf, bind_run, valTy_run]
      cases (valTy leftRun.1 le rightRun.2).1 with
      | data type => cases type <;> rfl
      | view => rfl)
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := lastReady.binary leftReplay rightReplay exactReplay wholeEffect
    (initial := initial) (middle := leftRun.2) rfl rfl typeRun (by
      intro live
      have leftLive := (dead_lowerExpr right).live_before (le := le) rfl live
      exact ⟨Nat.lt_of_lt_of_le (leftValue leftLive).bound (advB_lowerExpr right le leftRun.2 _ _ rfl).vals,
        (rightValue live).bound⟩) originBound
  have leftPath : DemandNodeAt (.expression (.bin op left right origin)) [0] (.expression left) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have rightPath : DemandNodeAt (.expression (.bin op left right origin)) [1] (.expression right) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have rightGrowth := (advB_lowerExpr right le leftRun.2 rightRun.1 rightRun.2 rfl).vals
  have ghostGrowth : middle.vals.size ≤ last.vals.size := by
    simpa only [middleReady.roots.valueSize, lastReady.roots.valueSize] using rightGrowth
  have argumentLedger := ((leftLedger.underRoot leftPath).replay_retained middleReady lastReady rightGrowth lastRoots).trans
    (rightLedger.underRoot rightPath)
  have whole : lowerExpr (.bin op left right origin) le initial =
      Goose.Lower.emitDef (.bin op (intTyOf leftRun.1 le rightRun.2).1 leftRun.1 rightRun.1 (some origin)) le rightRun.2 := by
    exact lowerExpr_bin_after_operands rfl rfl typeRun
  refine ⟨next, nextReady, ?_, ?_, ?_⟩
  · intro live
    have value := nextValue live
    exact ⟨value.bound, value.refined, fun _ => value.scalar rfl⟩
  · intro index bound
    have firstGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, middleReady.roots.valueSize]
      exact (advB_lowerExpr left le initial leftRun.1 leftRun.2 rfl).vals
    exact (nextRoots index (Nat.lt_of_lt_of_le bound (Nat.le_trans firstGrowth ghostGrowth))).trans
      ((lastRoots index (Nat.lt_of_lt_of_le bound firstGrowth)).trans (middleRoots index bound))
  · apply OccurrenceLedger.emitDef_sites argumentLedger rightSites lastReady nextReady (by rw [whole]) nextRoots
    · intro live value member
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have leftLive := (dead_lowerExpr right).live_before (le := le) rfl live
        exact (expression_operand_occurrence leftPath leftReplay middleReady (leftValue leftLive)).retained ghostGrowth lastRoots
      · exact expression_operand_occurrence rightPath rightReplay lastReady (rightValue live)
    · intro address same; cases same
    · intro callee arguments org same; cases same
    · intro live value member mutability payload reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have leftLive := (dead_lowerExpr right).live_before (le := le) rfl live
        have row := sourceExpressionNative tables leftNative generated leftTyped (rfl : lowerExpr left le initial = leftRun) leftLive
        exact False.elim (nativeFlat_not_reference row (by rfl) mutability payload reference)
      · have row := sourceExpressionNative tables rightNative (generated.lowerExpr left rfl) rightTyped (rfl : lowerExpr right le leftRun.2 = rightRun) live
        exact False.elim (nativeFlat_not_reference row (by rfl) mutability payload reference)

#print axioms globalExpressionOccurrence_binary

end Goose.Lower.Validation.ReplacementContentFlowSource
