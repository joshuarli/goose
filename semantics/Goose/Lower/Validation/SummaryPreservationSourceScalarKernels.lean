import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SummaryPreservationReplayTypedPlacesContracts
import Goose.Lower.Validation.SummaryPreservationReplayCompare
import Goose.Lower.Validation.SummaryPreservationReplayConversion
import Goose.Lower.Validation.SummaryPreservationReplaySlices
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem expressionReplay_comparison {left right : Expr} (op : CmpOp)
    (leftChild : ExpressionReplayAt typingEnv env results vt target scopeCount left initial upper)
    (rightChild : ∀ provenance, ExpressionReplayAt typingEnv env results vt target scopeCount right
      (lowerExpr left (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.cmp op left right) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  obtain ⟨leftTy, rightTy, leftFinish, rightFinish, leftTyped, rightTyped, rfl, _⟩ := tyExpr_comparison_children typed
  obtain ⟨leftRoots, middleSource, leftReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨rightRoots, lastSource, rightReplay, _⟩ := (st_bind_ok _ _ _ _).mp tail
  have exactReplay := rpExpr_cmp_after_operands leftReplay rightReplay (op := op)
  rw [exactReplay] at replay
  cases replay
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
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
  have rightNative := native.of_prefix (tailTypes le last.2 _ _ rfl)
  have leftNative := rightNative.of_prefix (types_lowerExpr right le first.2 last.1 last.2 rfl)
  have leftEffect := effectRefinement_before_expression rightReplay ceiling
  obtain ⟨middle, middleReady, leftValue, middleRoots⟩ :=
    leftChild leftTy start leftFinish before middleSource leftRoots leftTyped leftReplay leftEffect ready generated leftNative
  obtain ⟨lastUpper, lastReady, rightValue, lastRoots⟩ := rightChild middle
    rightTy leftFinish rightFinish middleSource after rightRoots rightTyped rightReplay ceiling middleReady
    (generated.lowerExpr left rfl) rightNative
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := lastReady.comparison leftReplay rightReplay exactReplay
    (initial := initial) (middle := first.2) rfl rfl (Prod.ext rfl (valTy_run first.1 le last.2)) (by
      intro live
      have firstLive := (dead_lowerExpr right).live_before (le := le) rfl live
      exact ⟨Nat.lt_of_lt_of_le (leftValue firstLive).bound (advB_lowerExpr right le first.2 _ _ rfl).vals,
        (rightValue live).bound⟩)
  refine ⟨next, nextReady, nextValue, ?_⟩
  intro old bound
  have firstGrowth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, middleReady.roots.valueSize]
    exact (advB_lowerExpr left le initial _ _ rfl).vals
  have secondGrowth : middle.vals.size ≤ lastUpper.vals.size := by
    rw [middleReady.roots.valueSize, lastReady.roots.valueSize]
    exact (advB_lowerExpr right le first.2 _ _ rfl).vals
  exact (nextRoots old (Nat.lt_of_lt_of_le bound (Nat.le_trans firstGrowth secondGrowth))).trans
    ((lastRoots old (Nat.lt_of_lt_of_le bound firstGrowth)).trans (middleRoots old bound))

theorem expressionReplay_conversion {operand : Expr} (kind : ConvKind) (destination : Ty) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : ExpressionReplayAt typingEnv env results vt target scopeCount operand initial upper) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.conv kind destination operand origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  have originBound : origin < env.mod.origins.size := by
    simpa only [← tables.moduleEq] using Core.tyExpr_conv_success_origin_bound typed
  obtain ⟨src, dst, childStart, childFinish, childTyped, rfl, rfl, _⟩ := tyExpr_conversion_child typed
  obtain ⟨childRoots, childAfter, childReplay, _⟩ := (st_bind_ok _ _ _ _).mp replay
  have exactReplay := rpExpr_conv_after_operand childReplay (kind := kind) (targetTy := .int dst) (origin := origin)
  rw [exactReplay] at replay
  cases replay
  have childEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) childAfter.eff target := by
    cases kind with
    | widen | asUnchecked => exact ceiling
    | as => exact ⟨ceiling.reads, ceiling.writes, ceiling.grows, ceiling.shrinks, ceiling.rebinds,
        fun _ => ceiling.aborts rfl, ceiling.outputs, ceiling.unknown⟩
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerExpr operand le initial
  have tailTypes : TypeRun (do
      let integer ← intTyOf lowered.1
      Goose.Lower.emitDef (.conv kind integer dst lowered.1 (some origin))) :=
    TypeRun.bind (types_intTyOf _) fun _ => types_emitDef _
  have childNative := native.of_prefix (tailTypes le lowered.2 _ _ rfl)
  obtain ⟨middle, middleReady, middleValue, middleRoots⟩ := child (.int src) childStart childFinish before childAfter
    childRoots childTyped childReplay childEffect ready generated childNative
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.conversion childReplay exactReplay ceiling
    (initial := initial) rfl (Prod.ext rfl (intTyOf_state lowered.1 le lowered.2))
    (fun live => (middleValue live).bound) originBound
  refine ⟨next, nextReady, nextValue, ?_⟩
  intro old bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, middleReady.roots.valueSize]
    exact (advB_lowerExpr operand le initial _ _ rfl).vals
  exact (nextRoots old (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots old bound)

theorem expressionReplay_length {view : View}
    (child : ViewReplayAt typingEnv env results vt target scopeCount view initial upper) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.len view) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  obtain ⟨info, nextCounter, childTyped, typedTail⟩ := (st_bind_ok _ _ _ _).mp typed
  have shape : type = .int .i64 := congrArg Prod.fst ((st_pure_ok _ _ _).mp typedTail)
  subst type
  obtain ⟨childRoots, childAfter, childReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have stateEq := congrArg Prod.snd ((st_pure_ok _ _ _).mp tail)
  dsimp only at stateEq
  subst after
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerView view le initial
  have childNative := native.of_prefix (types_emitDef (.viewLen lowered.1) le lowered.2 _ _ rfl)
  obtain ⟨middle, middleReady, middleValue, middleRoots⟩ := child info start nextCounter before childAfter
    childRoots childTyped childReplay ceiling ready generated childNative
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.length childReplay
    (show rpExpr env (.len view) before = .ok (roots, childAfter) by
      simpa only [rpExpr, childReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure] using tail)
    (initial := initial) rfl (fun live => (middleValue live).bound)
  refine ⟨next, nextReady, nextValue, ?_⟩
  intro old bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, middleReady.roots.valueSize]
    exact (advB_lowerView view le initial _ _ rfl).vals
  exact (nextRoots old (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots old bound)

#print axioms expressionReplay_comparison
#print axioms expressionReplay_conversion
#print axioms expressionReplay_length

end Goose.Lower.Validation.SummaryPreservation
