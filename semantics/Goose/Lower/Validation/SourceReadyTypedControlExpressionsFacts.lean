import Goose.Lower.Validation.SourceReadyTypedStatements
import Goose.Lower.Validation.SourceReadyControlShortCircuit

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem ready_recordValueRootRecipe_fields (value : ValueId) (scope : ScopeId) (env : LEnv) (before : LS) :
    let after := (recordValueRootRecipe value scope env before).2
    after.blocks = before.blocks ∧ after.vals = before.vals ∧ after.cur = before.cur := by
  rw [recordValueRootRecipe_run]
  exact ⟨rfl, rfl, rfl⟩

private theorem ready_patchBrs_values (target : BlockId) (incoming : List (BlockId × ValueId))
    (env : LEnv) (before : LS) : (patchBrs target incoming env before).2.vals = before.vals := by
  induction incoming generalizing before with
  | nil => rfl
  | cons pair rest ih =>
    simpa only [patchBrs, bind_run, patchTerm_run] using
      ih ((patchTerm pair.1 (.br target [pair.2]) env before).2)

private theorem ready_joinLive_grows (incoming : List (BlockId × ValueId)) (env : LEnv) (before : LS) :
    let action : B ValueId := do
      let type ← valTy (incoming.headD (0, 0)).2
      let (target, parameters) ← newBlock [type]
      patchBrs target incoming
      setCur (some target)
      pure (parameters.headD 0)
    before.vals.size < (action env before).2.vals.size := by
  let type := (valTy (incoming.headD (0, 0)).2 env before).1
  let created := newBlock [type] env before
  have fresh : before.vals.size < created.2.vals.size := by simp [created, newBlock1_run]
  have growth : created.2.vals.size ≤ (patchBrs created.1.1 incoming env created.2).2.vals.size := by
    rw [ready_patchBrs_values]
    exact Nat.le_refl _
  simpa only [bind_run, valTy_run, newBlock1_run, setCur_run, pure_run, type, created] using
    Nat.lt_of_lt_of_le fresh growth

theorem ready_joinValue_grows {yes no : Option BlockId} {yesValue noValue : ValueId}
    (env : LEnv) (before : LS) (live : (yes.isSome || no.isSome) = true) :
    before.vals.size < (Lower.joinValue yes yesValue no noValue env before).2.vals.size := by
  cases yes <;> cases no
  · simp at live
  all_goals exact ready_joinLive_grows _ env before

private theorem ready_joinLive_ext (incoming : List (BlockId × ValueId)) (env : LEnv) (before : LS) :
    let action : B ValueId := do
      let type ← valTy (incoming.headD (0, 0)).2
      let (target, parameters) ← newBlock [type]
      patchBrs target incoming
      setCur (some target)
      pure (parameters.headD 0)
    before.Ext (action env before).2 := by
  let type := (valTy (incoming.headD (0, 0)).2 env before).1
  let created := newBlock [type] env before
  have growth := (advB_newBlock1 type env before _ _ rfl).ext
  have patched : created.2.Ext (patchBrs created.1.1 incoming env created.2).2 := adv_patchBrs_ext incoming rfl
  have combined := growth.trans patched
  simp only [bind_run, valTy_run, newBlock1_run, setCur_run, pure_run]
  exact combined

theorem ready_joinValue_prefix {yes no : Option BlockId} {yesValue noValue : ValueId}
    (env : LEnv) (before : LS) :
    before.Ext (Lower.joinValue yes yesValue no noValue env before).2 ∧
      before.vals.size ≤ (Lower.joinValue yes yesValue no noValue env before).2.vals.size := by
  cases yes <;> cases no
  · exact ⟨LS.Ext.refl _, Nat.le_refl _⟩
  all_goals exact ⟨ready_joinLive_ext _ env before, Nat.le_of_lt (ready_joinLive_grows _ env before)⟩

theorem ready_shortCircuit_grows {isAnd : Bool} {condition : ValueId} {rhs : B ValueId}
    (env : LEnv) (before : LS) (live : before.cur.isSome = true) (advance : AdvB rhs) :
    before.vals.size < (Lower.shortCircuit isAnd condition rhs env before).2.vals.size := by
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  let forked := Lower.scFork isAnd condition env before
  let started := { forked.2 with cur := some forked.1.1 }
  let evaluated := rhs env started
  let closed := (emitTerm (.br forked.1.2.1 [evaluated.1]) env evaluated.2).2
  have fresh : before.vals.size < started.vals.size := by
    simp only [started, forked, scFork_run _ _ _ current, Array.size_push]
    exact Nat.lt_succ_self _
  have growth := (advance env started _ _ rfl).vals
  have closedGrowth : evaluated.2.vals.size ≤ closed.vals.size :=
    (advB_emitTerm (.br forked.1.2.1 [evaluated.1]) env evaluated.2 _ _ rfl).vals
  have bound : before.vals.size < closed.vals.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le fresh growth) closedGrowth
  simpa only [Lower.shortCircuit, whenLive_some _ _ _ current, bind_run, setCur_run,
    pure_run, forked, started, evaluated, closed] using bound

theorem tyExpr_ifE_checked_children {env : TEnv} {condition : Expr} {yes no : Core.Block}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.ifE condition yes no) start = .ok (type, finish)) :
    ∃ conditionFinish yesStart yesFinish,
      Core.tyExpr env condition start = .ok (.bool, conditionFinish) ∧
      yesStart = conditionFinish ∧
      Core.tyBlock (Core.exprEnv env) [] yes yesStart = .ok (type, yesFinish) ∧
      Core.tyBlock (Core.exprEnv env) [] no yesFinish = .ok (type, finish) := by
  simp only [Core.tyExpr] at source
  obtain ⟨conditionType, conditionFinish, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, yesStart, conditionBoolean, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨yesType, yesFinish, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨noType, noFinish, noSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have conditionFacts := (requireBool_ok _ _ _ _).mp conditionBoolean
  rw [conditionFacts.1] at conditionSource
  by_cases same : (yesType == noType) = true
  · simp only [same, ite_true] at source
    have result := (st_pure_ok _ _ _).mp source
    have resultType : type = yesType := congrArg Prod.fst result
    have resultFinish : finish = noFinish := congrArg Prod.snd result
    subst type finish
    have equal := eq_of_beq same
    subst noType
    exact ⟨conditionFinish, yesStart, yesFinish, conditionSource, conditionFacts.2, yesSource, noSource⟩
  · simp only [same] at source
    obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (rej_ok _ _ _ _).mp rejected |>.elim

end Goose.Lower.Validation.ReplacementContentFlowSource
