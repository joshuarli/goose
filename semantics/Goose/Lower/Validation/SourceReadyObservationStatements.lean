import Goose.Lower.Validation.SourceReadyObservationStatementsActions

namespace Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {initial : LS}
  {loop : Option LoopCtx}

theorem statement_let (slot : VarId) (expression : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.letS slot expression origin) le initial).2 := by
  let value := lowerExpr expression le initial
  let coerced := coerceSlot slot value.1 origin le value.2
  exact (child.trans (emits_coerceSlot slot value.1 origin le value.2 _ _ rfl)).trans
    (emits_effect (.slotInit slot coerced.1 (some origin)) le coerced.2 _ _ rfl)

theorem statement_rebind (slot : VarId) (expression : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.rebind slot expression origin) le initial).2 := by
  let value := lowerExpr expression le initial
  let coerced := coerceSlot slot value.1 origin le value.2
  let address := Goose.Lower.emitDef (.slotAddr slot) le coerced.2
  exact ((child.trans (emits_coerceSlot slot value.1 origin le value.2 _ _ rfl)).trans
    (emits_noncall_def (.slotAddr slot) (by intro callee arguments origin same; cases same) le coerced.2 _ _ rfl)).trans
    (emits_effect (.store address.1 coerced.1 (some origin)) le address.2 _ _ rfl)

theorem statement_expression (expression : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.expr expression origin) le initial).2 :=
  child

theorem statement_assign (place : Place) (expression : Expr) (origin : OriginId)
    (addressChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace place le initial).2)
    (valueChild : EmitsOnly (ReadyCallObservations module func state) (lowerPlace place le initial).2
      (lowerExpr expression le (lowerPlace place le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.assign place expression origin) le initial).2 := by
  let address := lowerPlace place le initial
  let value := lowerExpr expression le address.2
  exact (addressChild.trans valueChild).trans
    (emits_effect (.store address.1 value.1 (some origin)) le value.2 _ _ rfl)

theorem statement_assignOp (operation : BinOp) (place : Place) (expression : Expr) (origin : OriginId)
    (addressChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace place le initial).2)
    (valueChild : EmitsOnly (ReadyCallObservations module func state)
      (Goose.Lower.emitDef (.load (lowerPlace place le initial).1) le (lowerPlace place le initial).2).2
      (lowerExpr expression le (Goose.Lower.emitDef (.load (lowerPlace place le initial).1) le (lowerPlace place le initial).2).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.assignOp operation place expression origin) le initial).2 := by
  let address := lowerPlace place le initial
  let old := Goose.Lower.emitDef (.load address.1) le address.2
  let rhs := lowerExpr expression le old.2
  let integer := intTyOf old.1 le rhs.2
  let value := Goose.Lower.emitDef (.bin operation integer.1 old.1 rhs.1 (some origin)) le integer.2
  exact ((((addressChild.trans
    (emits_noncall_def (.load address.1) (by intro callee arguments origin same; cases same) le address.2 _ _ rfl)).trans
    valueChild).trans (emits_intTyOf old.1 le rhs.2 _ _ rfl)).trans
    (emits_noncall_def (.bin operation integer.1 old.1 rhs.1 (some origin))
      (by intro callee arguments origin same; cases same) le integer.2 _ _ rfl)).trans
    (emits_effect (.store address.1 value.1 (some origin)) le value.2 _ _ rfl)

end Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations
