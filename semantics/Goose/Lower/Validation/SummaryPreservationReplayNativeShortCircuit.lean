import Goose.Lower.Validation.SummaryPreservationReplayTypedShortCircuit
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedShortCircuitNative {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
    {env : TEnv} {penv : PEnv} {left right : Expr} {start finish : Nat} {type : Ty}
    {before after : RState} {sourceRoots : List RootRef} (isAnd : Bool)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (source : tyExpr env (if isAnd then .and left right else .or left right) start = .ok (type, finish))
    (replayed : rpExpr penv (if isAnd then .and left right else .or left right) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (if isAnd then .and left right else .or left right) le ls).2)
    (leftChild : ∀ tn2 roots sourceAfter,
      tyExpr env left start = .ok (.bool, tn2) →
      rpExpr penv left before = .ok (roots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      GeneratedBuilderState ls → NativeRows vt (lowerExpr left le ls).2 →
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
      GeneratedBuilderState entry → NativeRows vt (lowerExpr right le entry).2 →
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
  let loweredLeft := lowerExpr left le ls
  have whole : lowerExpr (if isAnd then .and left right else .or left right) le ls =
      Goose.Lower.shortCircuit isAnd loweredLeft.1 (lowerExpr right) le loweredLeft.2 := by
    cases isAnd <;> simp only [Bool.false_eq_true, ite_false, ite_true, lowerExpr, bind_run]
    all_goals rfl
  have leftNative := native.of_prefix
    (types_shortCircuit isAnd loweredLeft.1 (types_lowerExpr right) le loweredLeft.2 _ _ (by rw [whole]))
  obtain ⟨middle, leftReady, leftValue, leftPrefix⟩ :=
    leftChild middleCounter leftRoots middleSource typedLeft replayedLeft leftEffect generated leftNative
  obtain ⟨next, completed, returned, retained⟩ := leftReady.shortCircuit isAnd loweredLeft.1
    (lowerExpr right) (advB_lowerExpr right)
    (fun live => ⟨(leftValue live).bound, (leftValue live).scalar rfl⟩)
    (fun provenance live stateReady => by
      let forked := scFork isAnd loweredLeft.1 le loweredLeft.2
      let entry := { forked.2 with cur := some forked.1.1 }
      let produced := lowerExpr right le entry
      obtain ⟨currentBlock, current⟩ := Option.isSome_iff_exists.mp live
      have selected : loweredLeft.2.cur = some currentBlock := current
      have rightBound : forked.1.1 < forked.2.blocks.size := by
        simp [forked, scFork_run _ _ _ selected]
        exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
      have leftGenerated := generated.lowerExpr left (rfl : lowerExpr left le ls = loweredLeft)
      have forkGenerated := leftGenerated.scFork isAnd loweredLeft.1 (rfl : scFork isAnd loweredLeft.1 le loweredLeft.2 = forked)
      have entryGenerated : GeneratedBuilderState entry := by
        exact forkGenerated.setCur (env := le) (some forked.1.1) (by
          intro block row
          cases row
          exact rightBound) rfl
      have finalRun : Goose.Lower.shortCircuit isAnd loweredLeft.1 (lowerExpr right) le loweredLeft.2 =
          (forked.1.2.2, (Goose.Lower.setCur (some forked.1.2.1) le
            (Goose.Lower.emitTerm (.br forked.1.2.1 [produced.1]) le produced.2).2).2) := by
        simp only [Goose.Lower.shortCircuit, whenLive_some _ _ _ selected, bind_run, setCur_run, pure_run]
        rfl
      have suffixNative : NativeRows vt (Goose.Lower.setCur (some forked.1.2.1) le
          (Goose.Lower.emitTerm (.br forked.1.2.1 [produced.1]) le produced.2).2).2 := by
        simpa only [whole, finalRun] using native
      have rhsNative := suffixNative.of_prefix
        ((types_emitTerm (.br forked.1.2.1 [produced.1]) le produced.2 _ _ rfl).trans
          (types_setCur (some forked.1.2.1) le _ _ _ rfl))
      obtain ⟨next, generated, value, growth⟩ :=
        rightChild middleCounter rightRoots middleSource provenance typedRight replayedRight stateReady entryGenerated rhsNative
      exact ⟨next, generated, fun live => ⟨(value live).bound, (value live).scalar rfl⟩, growth⟩)
  rw [whole]
  refine ⟨next, completed, returned, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, leftReady.roots.valueSize]
    exact (advB_lowerExpr left le ls loweredLeft.1 loweredLeft.2 rfl).vals
  exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (leftPrefix index bound)

#print axioms typedShortCircuitNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
