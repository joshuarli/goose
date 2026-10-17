import Goose.Lower.Validation.SummaryPreservationReplayShortCircuit
import Goose.Lower.Validation.SummaryPreservationReplayShortCircuitSource
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedShortCircuit {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env : TEnv} {penv : PEnv} {left right : Expr} {start finish : Nat} {type : Ty}
    {before after : RState} {sourceRoots : List RootRef} (isAnd : Bool)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyExpr env (if isAnd then .and left right else .or left right) start = .ok (type, finish))
    (replayed : rpExpr penv (if isAnd then .and left right else .or left right) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (leftChild : ∀ tn2 roots sourceAfter,
      tyExpr env left start = .ok (.bool, tn2) →
      rpExpr penv left before = .ok (roots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerExpr left le ls).2 next ∧
        ((lowerExpr left le ls).2.cur.isSome = true →
          ReplayValue func next (lowerExpr left le ls).2 (lowerExpr left le ls).1 roots (.data .bool)) ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index)
    (rightChild : ∀ tn1 roots sourceBefore provenance,
      let loweredLeft := lowerExpr left le ls
      let forked := scFork isAnd loweredLeft.1 le loweredLeft.2
      let entry := { forked.2 with cur := some forked.1.1 }
      tyExpr env right tn1 = .ok (.bool, finish) →
      rpExpr penv right sourceBefore = .ok (roots, after) →
      ReplayBuilder module results vt func target le scopeCount slots entry provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerExpr right le entry).2 next ∧
        ((lowerExpr right le entry).2.cur.isSome = true →
          ReplayValue func next (lowerExpr right le entry).2 (lowerExpr right le entry).1 roots (.data .bool)) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (if isAnd then .and left right else .or left right) le ls).2 next ∧
      ((lowerExpr (if isAnd then .and left right else .or left right) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (if isAnd then .and left right else .or left right) le ls).2
          (lowerExpr (if isAnd then .and left right else .or left right) le ls).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨rfl, middleCounter, typedLeft, typedRight⟩ := tyExpr_shortCircuit_children isAnd source
  obtain ⟨rfl, leftRoots, middleSource, rightRoots, replayedLeft, replayedRight⟩ :=
    rpExpr_shortCircuit_children isAnd replayed
  have leftEffect := effectRefinement_before_expression replayedRight wholeEffect
  obtain ⟨middle, leftReady, leftValue, leftPrefix⟩ :=
    leftChild middleCounter leftRoots middleSource typedLeft replayedLeft leftEffect
  let loweredLeft := lowerExpr left le ls
  obtain ⟨next, completed, returned, retained⟩ := leftReady.shortCircuit isAnd loweredLeft.1
    (lowerExpr right) (advB_lowerExpr right)
    (fun live => ⟨(leftValue live).bound, (leftValue live).scalar rfl⟩)
    (fun provenance _live stateReady => by
      obtain ⟨next, generated, value, growth⟩ :=
        rightChild middleCounter rightRoots middleSource provenance typedRight replayedRight stateReady
      exact ⟨next, generated, fun live => ⟨(value live).bound, (value live).scalar rfl⟩, growth⟩)
  have whole : lowerExpr (if isAnd then .and left right else .or left right) le ls =
      Goose.Lower.shortCircuit isAnd loweredLeft.1 (lowerExpr right) le loweredLeft.2 := by
    cases isAnd <;> simp only [Bool.false_eq_true, ite_false, ite_true, lowerExpr, bind_run]
    all_goals rfl
  rw [whole]
  refine ⟨next, completed, returned, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, leftReady.roots.valueSize]
    exact (advB_lowerExpr left le ls loweredLeft.1 loweredLeft.2 rfl).vals
  exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (leftPrefix index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
