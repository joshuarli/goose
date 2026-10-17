import Goose.Lower.Validation.SourceReadyTypedStatementsOutput

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem printArgs_split_source {typingEnv : TEnv} {earlier later : List PrintArg} {expression : Expr}
    {start finish : Nat}
    (source : Core.tyPrintArgs typingEnv (earlier ++ .expr expression :: later) start = .ok ((), finish)) :
    ∃ next last type, Core.tyPrintArgs typingEnv earlier start = .ok ((), next) ∧
      Core.tyExpr typingEnv expression next = .ok (type, last) := by
  induction earlier generalizing start with
  | nil =>
    obtain ⟨type, last, child, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact ⟨start, last, type, rfl, child⟩
  | cons argument rest ih =>
    cases argument with
    | text text => exact ih source
    | expr value =>
      obtain ⟨type, offset, child, remaining⟩ := (st_bind_ok _ _ _ _).mp source
      cases type <;> simp only at remaining
      all_goals try { inv at remaining }
      all_goals
        obtain ⟨next, last, finalType, prefixChecked, checked⟩ := ih remaining
        refine ⟨next, last, finalType, ?_, checked⟩
        exact (st_bind_ok _ _ _ _).mpr ⟨_, offset, child, prefixChecked⟩

theorem typed_ready_print {state : State} {before : LS} {typingEnv output : TEnv} {results : List Ty}
    {loop : Option LoopCtx} {scope start finish : Nat} {origin : OriginId} {arguments : List PrintArg}
    (source : Core.tyStmt typingEnv scope (.print arguments origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (child : ∀ earlier expression later type next last,
      arguments = earlier ++ .expr expression :: later →
      Core.tyPrintArgs typingEnv earlier start = .ok ((), next) →
      Core.tyExpr typingEnv expression next = .ok (type, last) →
      ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results)
        (lowerPrintArgs earlier (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.print arguments origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨checked, outputEq⟩ := tyStmt_print_children source
  subst output
  have values := lowerPrintArgs_ready state arguments (lowerEnv typingEnv.mod typingEnv.vars results) before (by
    intro earlier expression later split
    have selected := checked
    rw [split] at selected
    obtain ⟨next, last, type, prefixChecked, expressionChecked⟩ := printArgs_split_source selected
    exact child earlier expression later type next last split prefixChecked expressionChecked)
  exact ⟨ready_print (loop := loop) values, fun _ => visible⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
