import Goose.Lower.Validation.SourceReadyObservationMutations

namespace Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {initial : LS}
  {loop : Option LoopCtx}

theorem statement_return_none (origin : OriginId) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.ret none origin) le initial).2 := by
  let left := Goose.Lower.leaveTo 0 le initial
  exact (emits_leaveTo 0 le initial _ _ rfl).trans (emits_term (.ret [] (some origin)) le left.2 _ _ rfl)

theorem statement_return_some (expression : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.ret (some expression) origin) le initial).2 := by
  let value := lowerExpr expression le initial
  let coerced := Goose.Lower.coerceResult value.1 origin le value.2
  let left := Goose.Lower.leaveTo 0 le coerced.2
  exact ((child.trans (emits_coerceResult value.1 origin le value.2 _ _ rfl)).trans
    (emits_leaveTo 0 le coerced.2 _ _ rfl)).trans (emits_term (.ret [coerced.1] (some origin)) le left.2 _ _ rfl)

theorem print_arguments_nil :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerPrintArgs [] le initial).2 :=
  .refl _ _

theorem print_arguments_text (text : String) (arguments : List PrintArg)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPrintArgs arguments le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerPrintArgs (.text text :: arguments) le initial).2 :=
  child

theorem print_arguments_expr (expression : Expr) (arguments : List PrintArg)
    (head : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2)
    (tail : EmitsOnly (ReadyCallObservations module func state) (lowerExpr expression le initial).2
      (lowerPrintArgs arguments le (lowerExpr expression le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerPrintArgs (.expr expression :: arguments) le initial).2 :=
  head.trans tail

theorem statement_print (arguments : List PrintArg) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPrintArgs arguments le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.print arguments origin) le initial).2 := by
  let parts := lowerPrintArgs arguments le initial
  exact child.trans (emits_effect (.print parts.1 (some origin)) le parts.2 _ _ rfl)

theorem statement_assert (expression : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.assertS expression origin) le initial).2 := by
  let value := lowerExpr expression le initial
  have suffix : EmitsOnlyRun (ReadyCallObservations module func state)
      (Goose.Lower.whenLive () fun _ => do
        let (passed, failed) ← fork value.1
        setCur (some failed)
        Goose.Lower.emitTerm (.abort .assert (some origin))
        setCur (some passed)) := by
    apply emits_whenLive
    intro block
    apply EmitsOnlyRun.bind (emits_fork value.1)
    rintro ⟨passed, failed⟩
    apply EmitsOnlyRun.bind (emits_setCur (some failed))
    intro _
    apply EmitsOnlyRun.bind (emits_term (.abort .assert (some origin)))
    intro _
    exact emits_setCur (some passed)
  exact child.trans (suffix le value.2 _ _ rfl)

theorem statement_abort (kind : String) (origin : OriginId) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.abort kind origin) le initial).2 :=
  emits_term (.abort .userAbort (some origin)) le initial _ _ rfl

theorem statement_exit (expression : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.exit expression origin) le initial).2 := by
  let value := lowerExpr expression le initial
  exact child.trans (emits_term (.exit value.1 (some origin)) le value.2 _ _ rfl)

theorem statement_break (origin : OriginId) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.brk origin) le initial).2 := by
  cases loop with
  | none => exact .refl _ _
  | some context =>
    let left := Goose.Lower.leaveTo context.depth le initial
    exact (emits_leaveTo context.depth le initial _ _ rfl).trans
      (emits_term (.br context.breakTo []) le left.2 _ _ rfl)

theorem statement_continue (origin : OriginId) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.cont origin) le initial).2 := by
  cases loop with
  | none => exact .refl _ _
  | some context =>
    let left := Goose.Lower.leaveTo context.depth le initial
    cases target : context.cont with
    | jump block =>
      simp only [lowerStmt, bind_run, target]
      exact (emits_leaveTo context.depth le initial _ _ rfl).trans
          (emits_term (.br block []) le left.2 _ _ rfl)
    | next block type value =>
      let incremented := Goose.Lower.emitDef (.next type value) le left.2
      simp only [lowerStmt, bind_run, target]
      exact ((emits_leaveTo context.depth le initial _ _ rfl).trans
          (emits_noncall_def (.next type value) (by intro callee arguments origin same; cases same) le left.2 _ _ rfl)).trans
            (emits_term (.br block [incremented.1]) le incremented.2 _ _ rfl)

end Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations
