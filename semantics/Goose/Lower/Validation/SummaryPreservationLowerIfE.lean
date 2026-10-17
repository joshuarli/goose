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
      let joined := joinValue yesLS.cur yesValue noLS.cur noValue le noLS
      (joined.1, (recordValueRootRecipe joined.1 (sourceBlockScope yes) le joined.2).2) := by
  simp only [lowerExpr, bind_run, conditionRun, whenLive_some _ _ _ live,
    forkRun, setCur_run, yesRun, noRun, curBlock_run, pure_run]

private theorem recordValueRootRecipe_frame (value : ValueId) (scope : ScopeId)
    (le : LEnv) (state : LS) :
    let after := (recordValueRootRecipe value scope le state).2
    after.blocks = state.blocks ∧ after.vals = state.vals ∧ after.cur = state.cur := by
  rw [recordValueRootRecipe_run]
  exact ⟨rfl, rfl, rfl⟩

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
  obtain ⟨next, joinedRoots, joinedEffects, returned, slots, retained⟩ :=
    joinValue_refined_witness symbols witness prior yesBound noBound
      (fun reachable => (yesRefines reachable).source_mono
        (fun root member => mem_unionRoots_iff.mpr (Or.inl member)))
      (fun reachable => (noRefines reachable).source_mono
        (fun root member => mem_unionRoots_iff.mpr (Or.inr member))) rfl
  rw [lowerExpr_ifE_after_branches conditionRun live forkRun yesRun noRun]
  let joined := joinValue yesLS.cur yesValue noLS.cur noValue le noLS
  let recorded := (recordValueRootRecipe joined.1 (sourceBlockScope yes) le joined.2).2
  have frame := recordValueRootRecipe_frame joined.1 (sourceBlockScope yes) le joined.2
  change recorded.blocks = joined.2.blocks ∧ recorded.vals = joined.2.vals ∧ recorded.cur = joined.2.cur at frame
  have instructions : recorded.insts = joined.2.insts := by simp only [LS.insts, frame.1]
  refine ⟨next, ⟨?_, ?_⟩, ?_, ?_, slots, retained⟩
  · exact joinedRoots.valueSize.trans (congrArg Array.size frame.2.1).symm
  · intro inst member
    change InstructionRootsClosed results vt {func with blocks := finishBlocks recorded.blocks} next inst
    rw [frame.1]
    exact joinedRoots.instructions inst (instructions ▸ member)
  · intro inst member
    exact joinedEffects inst (instructions ▸ member)
  · intro current
    change recorded.cur.isSome = true at current
    rw [frame.2.2] at current
    exact returned current

end Goose.Lower.Validation.SummaryPreservation
