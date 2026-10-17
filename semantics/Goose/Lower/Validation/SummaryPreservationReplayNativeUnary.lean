import Goose.Lower.Validation.SummaryPreservationReplayUnary
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem before_aborts {func : Func} {before target : Core.Eff}
    (bound : EffectRefinement func { before with aborts := true } target) :
    EffectRefinement func before target :=
  ⟨bound.reads, bound.writes, bound.grows, bound.shrinks, bound.rebinds,
    fun _ => bound.aborts rfl, bound.outputs, bound.unknown⟩

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem typedUnaryNative {env : TEnv} {penv : PEnv} {op : UnOp} {operand : Expr} {origin : OriginId}
    {type : Ty} {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : Core.tyExpr env (.un op operand origin) start = .ok (type, finish))
    (replayed : rpExpr penv (.un op operand origin) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (originBound : origin < le.mod.origins.size)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.un op operand origin) le ls).2)
    (child : ∀ childStart childFinish integer roots sourceAfter,
      Core.tyExpr env operand childStart = .ok (.int integer, childFinish) →
      rpExpr penv operand before = .ok (roots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      GeneratedBuilderState ls → NativeRows vt (lowerExpr operand le ls).2 →
      ∃ middle, ReplayBuilder module results vt func target le scopeCount slots (lowerExpr operand le ls).2 middle ∧
        ((lowerExpr operand le ls).2.cur.isSome = true → ReplayValue func middle
          (lowerExpr operand le ls).2 (lowerExpr operand le ls).1 roots (.data (.int integer))) ∧
        ∀ index, index < upper.vals.size → rootsAt middle.vals index = rootsAt upper.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.un op operand origin) le ls).2 next ∧
      ((lowerExpr (.un op operand origin) le ls).2.cur.isSome = true → ReplayValue func next
        (lowerExpr (.un op operand origin) le ls).2 (lowerExpr (.un op operand origin) le ls).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨childStart, childFinish, integer, typed, shape, _⟩ := tyExpr_un_child source
  subst type
  obtain ⟨roots, sourceAfter, operandReplay, _⟩ := (st_bind_ok _ _ _ _).mp replayed
  have exactReplay := rpExpr_un_after_operand operandReplay (op := op) (origin := origin)
  rw [exactReplay] at replayed
  cases replayed
  have childEffect : EffectRefinement func sourceAfter.eff target := by
    cases op with
    | neg => exact before_aborts wholeEffect
    | bitnot => exact wholeEffect
  let lowered := lowerExpr operand le ls
  have tailTypes : TypeRun (do
      let ty ← intTyOf lowered.1
      Goose.Lower.emitDef (.un op ty lowered.1 (some origin))) :=
    TypeRun.bind (types_intTyOf _) fun _ => types_emitDef _
  have childNative := native.of_prefix (tailTypes le lowered.2 _ _ rfl)
  obtain ⟨middle, middleReady, middleValue, middleRoots⟩ :=
    child childStart childFinish integer roots sourceAfter typed operandReplay childEffect generated childNative
  have typeRun : intTyOf lowered.1 le lowered.2 = ((intTyOf lowered.1 le lowered.2).1, lowered.2) :=
    Prod.ext rfl (by
      simp only [intTyOf, bind_run, valTy_run]
      cases (valTy lowered.1 le lowered.2).1 with
      | data type => cases type <;> rfl
      | view => rfl)
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.unary operandReplay exactReplay wholeEffect
    (initial := ls) rfl typeRun (fun live => (middleValue live).bound) originBound
  refine ⟨next, nextReady, ?_, ?_⟩
  · intro live
    have value := nextValue live
    exact ⟨value.bound, value.refined, fun _ => value.scalar rfl⟩
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, middleReady.roots.valueSize]
      exact (advB_lowerExpr operand le ls lowered.1 lowered.2 rfl).vals
    exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)

theorem typedNotNative {env : TEnv} {penv : PEnv} {operand : Expr} {type : Ty}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : Core.tyExpr env (.not operand) start = .ok (type, finish))
    (replayed : rpExpr penv (.not operand) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.not operand) le ls).2)
    (child : ∀ childFinish roots sourceAfter,
      Core.tyExpr env operand start = .ok (.bool, childFinish) →
      rpExpr penv operand before = .ok (roots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      GeneratedBuilderState ls → NativeRows vt (lowerExpr operand le ls).2 →
      ∃ middle, ReplayBuilder module results vt func target le scopeCount slots (lowerExpr operand le ls).2 middle ∧
        ((lowerExpr operand le ls).2.cur.isSome = true → ReplayValue func middle
          (lowerExpr operand le ls).2 (lowerExpr operand le ls).1 roots (.data .bool)) ∧
        ∀ index, index < upper.vals.size → rootsAt middle.vals index = rootsAt upper.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.not operand) le ls).2 next ∧
      ((lowerExpr (.not operand) le ls).2.cur.isSome = true → ReplayValue func next
        (lowerExpr (.not operand) le ls).2 (lowerExpr (.not operand) le ls).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨childFinish, typed, shape⟩ := tyExpr_not_child source
  subst type
  obtain ⟨roots, sourceAfter, operandReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replayed
  have afterEq : after = sourceAfter := (congrArg Prod.snd ((st_pure_ok _ _ _).mp tail))
  subst after
  have childNative := native.of_prefix (types_emitDef (.boolNot (lowerExpr operand le ls).1)
    le (lowerExpr operand le ls).2 _ _ rfl)
  obtain ⟨middle, middleReady, middleValue, middleRoots⟩ :=
    child childFinish roots sourceAfter typed operandReplay wholeEffect generated childNative
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.logicalNot operandReplay
    (show rpExpr penv (.not operand) before = .ok (sourceRoots, sourceAfter) from by
      simpa only [rpExpr, operandReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure] using tail)
    (initial := ls) rfl (fun live => (middleValue live).bound)
  refine ⟨next, nextReady, nextValue, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, middleReady.roots.valueSize]
    exact (advB_lowerExpr operand le ls _ _ rfl).vals
  exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)

#print axioms typedUnaryNative
#print axioms typedNotNative

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
