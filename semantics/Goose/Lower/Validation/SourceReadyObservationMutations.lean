import Goose.Lower.Validation.SourceReadyObservationStatements

namespace Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {initial : LS}
  {loop : Option LoopCtx}

theorem mutation_clear (owner : Place) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.clear owner origin) le initial).2 := by
  let address := lowerPlace owner le initial
  exact child.trans (emits_effect (.clear address.1 (some origin)) le address.2 _ _ rfl)

theorem mutation_append (owner : Place) (view : View) (origin : OriginId)
    (ownerChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2)
    (viewChild : EmitsOnly (ReadyCallObservations module func state) (lowerPlace owner le initial).2
      (lowerView view le (lowerPlace owner le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.append owner view origin) le initial).2 := by
  let address := lowerPlace owner le initial
  let value := lowerView view le address.2
  exact (ownerChild.trans viewChild).trans (emits_effect (.append address.1 value.1 (some origin)) le value.2 _ _ rfl)

theorem mutation_popN (owner : Place) (count : Expr) (origin : OriginId)
    (ownerChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2)
    (countChild : EmitsOnly (ReadyCallObservations module func state) (lowerPlace owner le initial).2
      (lowerExpr count le (lowerPlace owner le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.popN owner count origin) le initial).2 := by
  let address := lowerPlace owner le initial
  let amount := lowerExpr count le address.2
  exact (ownerChild.trans countChild).trans (emits_effect (.popN address.1 amount.1 (some origin)) le amount.2 _ _ rfl)

theorem mutation_resize_none (owner : Place) (count : Expr) (origin : OriginId)
    (ownerChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2)
    (countChild : EmitsOnly (ReadyCallObservations module func state) (lowerPlace owner le initial).2
      (lowerExpr count le (lowerPlace owner le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.resize owner count none origin) le initial).2 := by
  let address := lowerPlace owner le initial
  let amount := lowerExpr count le address.2
  exact (ownerChild.trans countChild).trans (emits_effect (.resize address.1 amount.1 none (some origin)) le amount.2 _ _ rfl)

theorem mutation_resize_some (owner : Place) (count fill : Expr) (origin : OriginId)
    (ownerChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2)
    (countChild : EmitsOnly (ReadyCallObservations module func state) (lowerPlace owner le initial).2
      (lowerExpr count le (lowerPlace owner le initial).2).2)
    (fillChild : EmitsOnly (ReadyCallObservations module func state)
      (lowerExpr count le (lowerPlace owner le initial).2).2
      (lowerExpr fill le (lowerExpr count le (lowerPlace owner le initial).2).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.resize owner count (some fill) origin) le initial).2 := by
  let address := lowerPlace owner le initial
  let amount := lowerExpr count le address.2
  let value := lowerExpr fill le amount.2
  exact ((ownerChild.trans countChild).trans fillChild).trans
    (emits_effect (.resize address.1 amount.1 (some value.1) (some origin)) le value.2 _ _ rfl)

theorem mutation_assignWhole (owner : Place) (expression : Expr) (origin : OriginId)
    (ownerChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2)
    (valueChild : EmitsOnly (ReadyCallObservations module func state)
      (Goose.Lower.emitEffect (.clear (lowerPlace owner le initial).1 (some origin)) le (lowerPlace owner le initial).2).2
      (lowerExpr expression le
        (Goose.Lower.emitEffect (.clear (lowerPlace owner le initial).1 (some origin)) le (lowerPlace owner le initial).2).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerStmt loop (.assignWhole owner expression origin) le initial).2 := by
  let address := lowerPlace owner le initial
  let cleared := Goose.Lower.emitEffect (.clear address.1 (some origin)) le address.2
  let value := lowerExpr expression le cleared.2
  exact ((ownerChild.trans (emits_effect (.clear address.1 (some origin)) le address.2 _ _ rfl)).trans valueChild).trans
    (emits_effect (.replace address.1 value.1 (some origin)) le value.2 _ _ rfl)

end Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations
