import Goose.Lower.Validation.SummaryPreservationJoinValue
import Goose.Lower.Validation.SummaryPreservationScalarSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpExpr_ifE_after_branches {env : PEnv} {condition : Expr} {yes no : Core.Block}
    {initial conditionState yesState after : RState} {conditionRoots yesRoots noRoots : List RootRef}
    {yesRange noRange : Nat × Nat}
    (conditionReplay : rpExpr env condition initial = .ok (conditionRoots, conditionState))
    (yesReplay : rpBlockValue env [] yes conditionState = .ok ((yesRoots, yesRange), yesState))
    (noReplay : rpBlockValue env [] no yesState = .ok ((noRoots, noRange), after)) :
    rpExpr env (.ifE condition yes no) initial = .ok (unionRoots yesRoots noRoots, after) := by
  simp [rpExpr, conditionReplay, yesReplay, noReplay, bind, pure,
    Except.bind, Except.pure, StateT.bind, StateT.pure]

theorem lowerExpr_ifE_after_branches {condition : Expr} {yes no : Core.Block}
    {le : LEnv} {initial conditionLS forked yesLS noLS : LS}
    {conditionValue yesValue noValue : ValueId} {current yesBlock noBlock : BlockId}
    (conditionRun : lowerExpr condition le initial = (conditionValue, conditionLS))
    (live : conditionLS.cur = some current)
    (forkRun : fork conditionValue le conditionLS = ((yesBlock, noBlock), forked))
    (yesRun : lowerBlock none [] true yes le { forked with cur := some yesBlock } = (yesValue, yesLS))
    (noRun : lowerBlock none [] true no le { yesLS with cur := some noBlock } = (noValue, noLS)) :
    lowerExpr (.ifE condition yes no) le initial =
      (joinValue yesLS.cur yesValue noLS.cur noValue >>= fun value => do
        recordValueRootRecipe value (sourceBlockScope yes)
        pure value) le noLS := by
  simp only [lowerExpr, bind_run, conditionRun, whenLive_some _ _ _ live,
    forkRun, setCur_run, yesRun, noRun, curBlock_run]

theorem joinValue_recordValueRootRecipe_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots : List RootRef} {ls final : LS} {le : LEnv}
    {scopeCount : Nat} {value trueValue falseValue : ValueId} {trueEnd falseEnd : Option BlockId}
    {sourceScope : ScopeId}
    (symbols : ls.SymbolWF le scopeCount)
    (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (trueBound : ∀ block, trueEnd = some block → block < ls.blocks.size ∧ trueValue < ls.vals.size)
    (falseBound : ∀ block, falseEnd = some block → block < ls.blocks.size ∧ falseValue < ls.vals.size)
    (trueRoots : trueEnd.isSome = true → RootsRefine func (rootsAt upper.vals trueValue) sourceRoots)
    (falseRoots : falseEnd.isSome = true → RootsRefine func (rootsAt upper.vals falseValue) sourceRoots)
    (run : (joinValue trueEnd trueValue falseEnd falseValue >>= fun result => do
      recordValueRootRecipe result sourceScope
      pure result) le ls = (value, final)) :
    ∃ next : Prov, BuilderRootWitness results vt func next final ∧
      BuilderEffectRefinement module vt func next source final ∧
      (final.cur.isSome = true → RootsRefine func (rootsAt next.vals value) sourceRoots) ∧
      next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases joinResult : joinValue trueEnd trueValue falseEnd falseValue le ls with
  | mk joinedValue joinedState =>
    simp only [bind_run, recordValueRootRecipe_run, pure_run, joinResult] at run
    obtain ⟨rfl, stateEq⟩ := Prod.mk.inj run
    have recipeRun : recordValueRootRecipe joinedValue sourceScope le joinedState = ((), final) := by
      rw [recordValueRootRecipe_run]
      exact Prod.ext rfl stateEq
    obtain ⟨next, joinedWitness, joinedEffects, joinedRoots, slots, unchanged⟩ :=
      joinValue_refined_witness symbols witness prior trueBound falseBound trueRoots falseRoots joinResult
    have blocksEq : final.blocks = joinedState.blocks := by
      rw [← stateEq]
    have valuesEq : final.vals = joinedState.vals := by
      rw [← stateEq]
    have currentEq : final.cur = joinedState.cur := by
      rw [← stateEq]
    have instructionsEq : final.insts = joinedState.insts := by
      simp only [LS.insts, blocksEq]
    refine ⟨next, ?_, ?_, ?_, slots, unchanged⟩
    · constructor
      · simpa only [valuesEq] using joinedWitness.valueSize
      · intro instruction member
        have oldMember : instruction ∈ joinedState.insts := by simpa only [instructionsEq] using member
        simpa only [blocksEq] using joinedWitness.instructions instruction oldMember
    · intro instruction member
      have oldMember : instruction ∈ joinedState.insts := by simpa only [instructionsEq] using member
      exact joinedEffects instruction oldMember
    · intro live
      apply joinedRoots
      simpa only [currentEq] using live

theorem lowerExpr_ifE_join_source_witness {env : PEnv} {condition : Expr} {yes no : Core.Block}
    {initialSource conditionState yesState after : RState}
    {conditionRoots yesRoots noRoots sourceRoots : List RootRef} {yesRange noRange : Nat × Nat}
    {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {target : Core.Eff} {scopeCount : Nat}
    {le : LEnv} {initial conditionLS forked yesLS noLS : LS}
    {conditionValue yesValue noValue : ValueId} {current yesBlock noBlock : BlockId}
    (conditionReplay : rpExpr env condition initialSource = .ok (conditionRoots, conditionState))
    (yesReplay : rpBlockValue env [] yes conditionState = .ok ((yesRoots, yesRange), yesState))
    (noReplay : rpBlockValue env [] no yesState = .ok ((noRoots, noRange), after))
    (source : rpExpr env (.ifE condition yes no) initialSource = .ok (sourceRoots, after))
    (conditionRun : lowerExpr condition le initial = (conditionValue, conditionLS))
    (live : conditionLS.cur = some current)
    (forkRun : fork conditionValue le conditionLS = ((yesBlock, noBlock), forked))
    (yesRun : lowerBlock none [] true yes le { forked with cur := some yesBlock } = (yesValue, yesLS))
    (noRun : lowerBlock none [] true no le { yesLS with cur := some noBlock } = (noValue, noLS))
    (symbols : noLS.SymbolWF le scopeCount)
    (witness : BuilderRootWitness results vt func upper noLS)
    (prior : BuilderEffectRefinement module vt func upper target noLS)
    (yesBound : ∀ block, yesLS.cur = some block → block < noLS.blocks.size ∧ yesValue < noLS.vals.size)
    (noBound : ∀ block, noLS.cur = some block → block < noLS.blocks.size ∧ noValue < noLS.vals.size)
    (yesRefines : yesLS.cur.isSome = true → RootsRefine func (rootsAt upper.vals yesValue) yesRoots)
    (noRefines : noLS.cur.isSome = true → RootsRefine func (rootsAt upper.vals noValue) noRoots) :
    ∃ next : Prov,
      BuilderRootWitness results vt func next (lowerExpr (.ifE condition yes no) le initial).2 ∧
      BuilderEffectRefinement module vt func next target (lowerExpr (.ifE condition yes no) le initial).2 ∧
      ((lowerExpr (.ifE condition yes no) le initial).2.cur.isSome = true →
        RootsRefine func (rootsAt next.vals (lowerExpr (.ifE condition yes no) le initial).1) sourceRoots) ∧
      next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  rw [rpExpr_ifE_after_branches conditionReplay yesReplay noReplay] at source
  cases source
  rw [lowerExpr_ifE_after_branches conditionRun live forkRun yesRun noRun]
  apply joinValue_recordValueRootRecipe_refined_witness
    (symbols := symbols) (witness := witness) (prior := prior)
    (trueBound := yesBound) (falseBound := noBound) (sourceScope := sourceBlockScope yes)
    (run := by
      cases result : (joinValue yesLS.cur yesValue noLS.cur noValue >>= fun value => do
        recordValueRootRecipe value (sourceBlockScope yes)
        pure value) le noLS <;> rfl)
  · intro reachable
    exact (yesRefines reachable).source_mono (fun root member => mem_unionRoots_iff.mpr (Or.inl member))
  · intro reachable
    exact (noRefines reachable).source_mono (fun root member => mem_unionRoots_iff.mpr (Or.inr member))

end Goose.Lower.Validation.SummaryPreservation
