import Goose.Lower.Validation.SummaryPreservationReplayLoopsRange
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_while_children {env : PEnv} {condition : Expr} {body : Core.Block} {origin : OriginId}
    {before after : RState}
    (source : rpStmt env (.while condition body origin) before = .ok ((), after)) :
    ∃ conditionRoots conditionState bodyRoots bodyRange bodyState,
      rpExpr env condition before = .ok (conditionRoots, conditionState) ∧
      rpBlockValue env [] body conditionState = .ok ((bodyRoots, bodyRange), bodyState) := by
  simp only [rpStmt] at source
  obtain ⟨conditionRoots, conditionState, conditionReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨result, bodyState, bodyReplay, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ⟨conditionRoots, conditionState, result.1, result.2, bodyState, conditionReplay, bodyReplay⟩

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem while_statement {tenv output : TEnv} {env : PEnv} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {scope start finish : Nat} {before after : RState} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typing : Core.tyStmt tenv scope (.while condition body origin) start = .ok (output, finish))
    (source : rpStmt env (.while condition body origin) before = .ok ((), after))
    (conditionStep : ∀ typeStart typeFinish sourceBefore sourceAfter sourceRoots state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      Core.tyExpr tenv condition typeStart = .ok (.bool, typeFinish) →
      rpExpr env condition sourceBefore = .ok (sourceRoots, sourceAfter) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerExpr condition le state).2 next ∧
        ((lowerExpr condition le state).2.cur.isSome = true →
          ReplayValue func next (lowerExpr condition le state).2 (lowerExpr condition le state).1 sourceRoots (.data .bool)) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (bodyStep : ∀ depth header exit typeStart bodyType sourceBefore sourceAfter bodyRoots bodyRange state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      header < state.blocks.size → exit < state.blocks.size →
      Core.tyBlock { tenv with loops := tenv.loops + 1 } [] body typeStart = .ok (bodyType, finish) →
      rpBlockValue env [] body sourceBefore = .ok ((bodyRoots, bodyRange), sourceAfter) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerStmt loop (.while condition body origin) le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨conditionFinish, bodyType, conditionTyped, bodyTyped, _⟩ := tyStmt_while_children typing
  obtain ⟨conditionRoots, conditionState, bodyRoots, bodyRange, bodyState, conditionReplay, bodyReplay⟩ :=
    rpStmt_while_children source
  let allocated := newBlock [] le ls
  have allocatedReady := ready.loopEmptyBlock
  have headerBound : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock0_run]
  let bridged := emitTerm (.br allocated.1.1 []) le allocated.2
  have bridgedReady := allocatedReady.loopBranch allocated.1.1 [] headerBound (by simp) (by simp)
  have branchAdv := advB_emitTerm (.br allocated.1.1 []) le allocated.2 bridged.1 bridged.2 rfl
  have headerStill := Nat.lt_of_lt_of_le headerBound branchAdv.ext.1
  let started := (Goose.Lower.setCur (some allocated.1.1) le bridged.2).2
  have startedReady := bridgedReady.setCur (some allocated.1.1) (by intro block row; cases row; exact headerStill)
  obtain ⟨conditionProv, conditionReady, conditionValue, conditionGrowth⟩ :=
    conditionStep start conditionFinish before conditionState conditionRoots started upper startedReady conditionTyped conditionReplay
  obtain ⟨next, nextReady, growth⟩ := startedReady.loopWhile allocated.1.1 (lowerExpr condition)
    (fun depth exit => lowerBlock (some ⟨depth, exit, .jump allocated.1.1⟩) [] false body)
    headerStill (advB_lowerExpr condition) (fun _ _ => advB_lowerBlock _ _ _ _)
    ⟨conditionProv, conditionReady, fun live => (conditionValue live).bound, conditionGrowth⟩
    (by
      intro depth exit state provenance stateReady headerBound exitBound
      exact bodyStep depth allocated.1.1 exit conditionFinish bodyType conditionState bodyState bodyRoots bodyRange
        state provenance stateReady headerBound exitBound bodyTyped bodyReplay)
  refine ⟨next, ?_, growth⟩
  simpa only [lowerStmt, bind_run] using nextReady

end ReplayBuilder

#print axioms rpStmt_while_children
#print axioms ReplayBuilder.while_statement

end Goose.Lower.Validation.SummaryPreservation
