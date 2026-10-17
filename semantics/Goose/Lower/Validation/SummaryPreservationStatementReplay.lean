import Goose.Lower.Validation.SummaryPreservationArgumentReplay

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmts_cons_contract {env : PEnv} {statement : Stmt} {rest : List Stmt}
    {before after : RState} (source : rpStmts env (statement :: rest) before = .ok ((), after)) :
    ∃ middle, rpStmt env statement before = .ok ((), middle) ∧
      rpStmts env rest middle = .ok ((), after) := by
  obtain ⟨first, middle, firstRun, tail⟩ := (st_bind_ok _ _ _ _).mp source
  cases first
  exact ⟨middle, firstRun, tail⟩

theorem lowerStmts_source_composition {env : PEnv} {le : LEnv}
    (Ready : LS → Prov → Prop) (loop : Option LoopCtx)
    (step : ∀ statement before after ls upper,
      Ready ls upper → rpStmt env statement before = .ok ((), after) → ls.cur.isSome = true →
      ∃ next, Ready (lowerStmt loop statement le ls).2 next ∧ next.slots = upper.slots ∧
        ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index)
    (statements : List Stmt) {before after : RState} {ls : LS} {upper : Prov}
    (sizes : ∀ ls upper, Ready ls upper → upper.vals.size = ls.vals.size)
    (ready : Ready ls upper)
    (source : rpStmts env statements before = .ok ((), after)) :
    ∃ next, Ready (lowerStmts loop statements le ls).2 next ∧ next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  induction statements generalizing before after ls upper with
  | nil => exact ⟨upper, ready, rfl, fun _ _ => rfl⟩
  | cons statement rest ih =>
    cases current : ls.cur with
    | none =>
      have stopped : lowerStmts loop (statement :: rest) le ls = ((), ls) := by
        simp [lowerStmts, bind_run, isLive, curBlock_run, current, pure_run]
      rw [stopped]
      exact ⟨upper, ready, rfl, fun _ _ => rfl⟩
    | some block =>
      obtain ⟨middleSource, firstReplay, restReplay⟩ := rpStmts_cons_contract source
      obtain ⟨middle, middleReady, middleSlots, middlePrefix⟩ :=
        step statement before middleSource ls upper ready firstReplay (by simp [current])
      obtain ⟨next, nextReady, nextSlots, nextPrefix⟩ := ih middleReady restReplay
      have whole : lowerStmts loop (statement :: rest) le ls =
          lowerStmts loop rest le (lowerStmt loop statement le ls).2 := by
        simp [lowerStmts, bind_run, isLive, curBlock_run, current, pure_run]
      rw [whole]
      refine ⟨next, nextReady, nextSlots.trans middleSlots, ?_⟩
      intro index bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [sizes _ _ ready, sizes _ _ middleReady]
        exact (advB_lowerStmt loop statement le ls _ _ rfl).vals
      rw [nextPrefix index (Nat.lt_of_lt_of_le bound growth), middlePrefix index bound]

end Goose.Lower.Validation.SummaryPreservation
