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
      joinValue yesLS.cur yesValue noLS.cur noValue le noLS := by
  simp only [lowerExpr, bind_run, conditionRun, whenLive_some _ _ _ live,
    forkRun, setCur_run, yesRun, noRun, curBlock_run]

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
  apply joinValue_refined_witness symbols witness prior yesBound noBound
  · intro reachable
    exact (yesRefines reachable).source_mono (fun root member => mem_unionRoots_iff.mpr (Or.inl member))
  · intro reachable
    exact (noRefines reachable).source_mono (fun root member => mem_unionRoots_iff.mpr (Or.inr member))
  · rfl

end Goose.Lower.Validation.SummaryPreservation
