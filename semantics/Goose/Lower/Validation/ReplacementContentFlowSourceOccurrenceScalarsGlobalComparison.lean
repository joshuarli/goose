import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsConsumed
import Goose.Lower.Validation.SummaryPreservationReplayCompare
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem globalExpressionOccurrence_comparison {left right : Expr} (op : CmpOp)
    (tables : SourceRootTables typingEnv env)
    (leftChild : GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets left initial upper)
    (rightChild : ∀ provenance, GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets right
      (lowerExpr left (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.cmp op left right) initial upper := by
  intro rooted type start finish before after roots typed replay ceiling ready sites targetBounds generated native metadata continuation
  obtain ⟨leftTy, rightTy, leftFinish, rightFinish, leftTyped, rightTyped, rfl, shape⟩ := tyExpr_comparison_children typed
  have flat : leftTy.flat = true ∧ rightTy.flat = true := by
    rcases shape with ⟨integer, rfl, rfl⟩ | ⟨rfl, rfl, _⟩ <;> exact ⟨rfl, rfl⟩
  obtain ⟨leftRoots, middleSource, leftReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨rightRoots, lastSource, rightReplay, _⟩ := (st_bind_ok _ _ _ _).mp tail
  have exactReplay := rpExpr_cmp_after_operands leftReplay rightReplay (op := op)
  rw [exactReplay] at replay
  cases replay
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let first := lowerExpr left le initial
  let last := lowerExpr right le first.2
  have tailTypes : TypeRun (do
      match (← valTy first.1) with
      | .data (.int integer) => Goose.Lower.emitDef (.cmp op integer first.1 last.1)
      | _ => Goose.Lower.emitDef (.boolCmp op first.1 last.1)) := by
    apply TypeRun.bind (types_valTy _)
    intro type
    cases type with
    | data type => cases type <;> exact types_emitDef _
    | view => exact types_emitDef _
  have tailAdvance : AdvB (do
      match (← valTy first.1) with
      | .data (.int integer) => Goose.Lower.emitDef (.cmp op integer first.1 last.1)
      | _ => Goose.Lower.emitDef (.boolCmp op first.1 last.1)) := by
    apply AdvB.bind (advB_valTy _)
    intro type
    cases type with
    | data type => cases type <;> exact advB_emitDef _
    | view => exact advB_emitDef _
  have rightNative := native.of_prefix (tailTypes le last.2 _ _ rfl)
  have rightMetadata := metadata.of_advance (tailAdvance le last.2 _ _ rfl)
  have rightContinuation := continuation.of_advance (tailAdvance le last.2 _ _ rfl)
  have leftMetadata := rightMetadata.of_advance (advB_lowerExpr right le first.2 last.1 last.2 rfl)
  have leftContinuation := rightContinuation.of_advance (advB_lowerExpr right le first.2 last.1 last.2 rfl)
  have leftNative := rightNative.of_prefix (types_lowerExpr right le first.2 last.1 last.2 rfl)
  have leftEffect := effectRefinement_before_expression rightReplay ceiling
  have leftAtSite : ∃ path, DemandNodeAt siteRoot path (.expression left) := by
    obtain ⟨path, atSite⟩ := rooted
    exact ⟨path ++ [0], atSite.snoc 0 (by simp [DemandNode.child?, DemandNode.children])⟩
  have rightAtSite : ∃ path, DemandNodeAt siteRoot path (.expression right) := by
    obtain ⟨path, atSite⟩ := rooted
    exact ⟨path ++ [1], atSite.snoc 1 (by simp [DemandNode.child?, DemandNode.children])⟩
  obtain ⟨middle, middleReady, leftValue, middleRoots, leftLedger, leftSites⟩ :=
    leftChild leftAtSite leftTy start leftFinish before middleSource leftRoots leftTyped leftReplay leftEffect ready sites targetBounds generated leftNative leftMetadata leftContinuation
  obtain ⟨lastUpper, lastReady, rightValue, lastRoots, rightLedger, rightSites⟩ := rightChild middle rightAtSite
    rightTy leftFinish rightFinish middleSource after rightRoots rightTyped rightReplay ceiling middleReady leftSites (targetBounds.mono (advB_lowerExpr left le initial first.1 first.2 rfl).ext)
    (generated.lowerExpr left rfl) rightNative rightMetadata rightContinuation
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := lastReady.comparison leftReplay rightReplay exactReplay
    (initial := initial) (middle := first.2) rfl rfl (Prod.ext rfl (valTy_run first.1 le last.2)) (by
      intro live
      have firstLive := (dead_lowerExpr right).live_before (le := le) rfl live
      exact ⟨Nat.lt_of_lt_of_le (leftValue firstLive).bound (advB_lowerExpr right le first.2 _ _ rfl).vals,
        (rightValue live).bound⟩)
  let emitted : Op := match (valTy first.1 le last.2).1 with
    | .data (.int integer) => .cmp op integer first.1 last.1
    | _ => .boolCmp op first.1 last.1
  have whole : lowerExpr (.cmp op left right) le initial = Goose.Lower.emitDef emitted le last.2 := by
    dsimp only [emitted]
    simp only [lowerExpr, bind_run, show lowerExpr left le initial = first from rfl,
      show lowerExpr right le first.2 = last from rfl]
    rw [show valTy first.1 le last.2 = ((valTy first.1 le last.2).1, last.2) from Prod.ext rfl (valTy_run _ _ _)]
    cases (valTy first.1 le last.2).1 with
    | data type => cases type <;> rfl
    | view => rfl
  have leftPath : DemandNodeAt (.expression (.cmp op left right)) [0] (.expression left) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have rightPath : DemandNodeAt (.expression (.cmp op left right)) [1] (.expression right) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have rightGrowth := (advB_lowerExpr right le first.2 last.1 last.2 rfl).vals
  have ghostGrowth : middle.vals.size ≤ lastUpper.vals.size := by
    simpa only [middleReady.roots.valueSize, lastReady.roots.valueSize] using rightGrowth
  have argumentLedger := ((leftLedger.underRoot leftPath).replay_retained middleReady lastReady rightGrowth lastRoots).trans
    (rightLedger.underRoot rightPath)
  have uses : GIR.ReplacementContentFlow.Model.accessOperands (.def last.2.vals.size emitted) = [first.1, last.1] := by
    dsimp only [emitted]
    split <;> rfl
  refine ⟨next, nextReady, nextValue, ?_, ?_⟩
  · intro old bound
    have firstGrowth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, middleReady.roots.valueSize]
      exact (advB_lowerExpr left le initial first.1 first.2 rfl).vals
    exact (nextRoots old (Nat.lt_of_lt_of_le bound (Nat.le_trans firstGrowth ghostGrowth))).trans
      ((lastRoots old (Nat.lt_of_lt_of_le bound firstGrowth)).trans (middleRoots old bound))
  · apply OccurrenceLedger.emitDef_sites argumentLedger rightSites lastReady nextReady (by rw [whole]) nextRoots
    · intro live value member
      rw [uses] at member
      rcases List.mem_cons.mp member with rfl | member
      · have leftLive := (dead_lowerExpr right).live_before (le := le) rfl live
        exact (expression_operand_occurrence leftPath leftReplay middleReady (leftValue leftLive)).retained ghostGrowth lastRoots
      · have same := List.mem_singleton.mp member
        subst value
        exact expression_operand_occurrence rightPath rightReplay lastReady (rightValue live)
    · dsimp only [emitted]
      split <;> intro address same <;> cases same
    · dsimp only [emitted]
      split <;> intro callee arguments org same <;> cases same
    · intro live value member mutability payload reference
      rw [uses] at member
      rcases List.mem_cons.mp member with rfl | member
      · have leftLive := (dead_lowerExpr right).live_before (le := le) rfl live
        have row := sourceExpressionNative tables leftNative generated leftTyped (rfl : lowerExpr left le initial = first) leftLive
        exact False.elim (nativeFlat_not_reference row flat.1 mutability payload reference)
      · have same := List.mem_singleton.mp member
        subst value
        have row := sourceExpressionNative tables rightNative (generated.lowerExpr left rfl) rightTyped (rfl : lowerExpr right le first.2 = last) live
        exact False.elim (nativeFlat_not_reference row flat.2 mutability payload reference)

#print axioms globalExpressionOccurrence_comparison

end Goose.Lower.Validation.ReplacementContentFlowSource
