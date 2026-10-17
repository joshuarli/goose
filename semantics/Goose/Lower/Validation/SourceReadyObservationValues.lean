import Goose.Lower.Validation.SourceReadyObservations

namespace Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {initial : LS}

theorem emitDefinition (operation : Op)
    (absent : ∀ callee arguments origin, operation ≠ .call callee arguments origin) :
    EmitsOnlyRun (ReadyCallObservations module func state) (emitDef operation) := by
  intro le before value after run
  exact emitsOnly_emitDef run (.definition _ _ absent)

theorem valueType (value : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (valTy value) := by
  intro le before result after run
  have same := congrArg Prod.snd run
  rw [valTy_run] at same
  exact .of_blocks (congrArg LS.blocks same.symm)

theorem integerType (value : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (intTyOf value) := by
  intro le before result after run
  have same := congrArg Prod.snd run
  rw [intTyOf_state] at same
  exact .of_blocks (congrArg LS.blocks same.symm)

theorem literal (integer : IntTy) (value : Int) :
    EmitsOnly (ReadyCallObservations module func state) initial
      (lowerExpr (.lit integer value) le initial).2 :=
  emitDefinition (.constInt integer value) (by intros; intro same; cases same) le initial _ _ rfl

theorem boolean (value : Bool) :
    EmitsOnly (ReadyCallObservations module func state) initial
      (lowerExpr (.bool value) le initial).2 :=
  emitDefinition (.constBool value) (by intros; intro same; cases same) le initial _ _ rfl

theorem unary (operation : UnOp) (operand : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr operand le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial
      (lowerExpr (.un operation operand origin) le initial).2 := by
  let lowered := lowerExpr operand le initial
  have tail : EmitsOnlyRun (ReadyCallObservations module func state) (do
      let integer ← intTyOf lowered.1
      emitDef (.un operation integer lowered.1 (some origin))) :=
    (integerType lowered.1).bind fun _ => emitDefinition _ (by intros; intro same; cases same)
  exact child.trans (tail le lowered.2 _ _ rfl)

theorem binary (operation : BinOp) (left right : Expr) (origin : OriginId)
    (leftChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr left le initial).2)
    (rightChild : EmitsOnly (ReadyCallObservations module func state) (lowerExpr left le initial).2
      (lowerExpr right le (lowerExpr left le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial
      (lowerExpr (.bin operation left right origin) le initial).2 := by
  let first := lowerExpr left le initial
  let last := lowerExpr right le first.2
  have tail : EmitsOnlyRun (ReadyCallObservations module func state) (do
      let integer ← intTyOf first.1
      emitDef (.bin operation integer first.1 last.1 (some origin))) :=
    (integerType first.1).bind fun _ => emitDefinition _ (by intros; intro same; cases same)
  exact (leftChild.trans rightChild).trans (tail le last.2 _ _ rfl)

theorem comparison (operation : CmpOp) (left right : Expr)
    (leftChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr left le initial).2)
    (rightChild : EmitsOnly (ReadyCallObservations module func state) (lowerExpr left le initial).2
      (lowerExpr right le (lowerExpr left le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial
      (lowerExpr (.cmp operation left right) le initial).2 := by
  let first := lowerExpr left le initial
  let last := lowerExpr right le first.2
  have tail : EmitsOnlyRun (ReadyCallObservations module func state) (do
      match (← valTy first.1) with
      | .data (.int integer) => emitDef (.cmp operation integer first.1 last.1)
      | _ => emitDef (.boolCmp operation first.1 last.1)) := by
    apply EmitsOnlyRun.bind (valueType first.1)
    intro type
    cases type with
    | data type => cases type <;> exact emitDefinition _ (by intros; intro same; cases same)
    | view => exact emitDefinition _ (by intros; intro same; cases same)
  exact (leftChild.trans rightChild).trans (tail le last.2 _ _ rfl)

theorem logicalNot (operand : Expr)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr operand le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.not operand) le initial).2 :=
  child.trans (emitDefinition (.boolNot (lowerExpr operand le initial).1)
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem conversion (kind : ConvKind) (target : Ty) (operand : Expr) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr operand le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial
      (lowerExpr (.conv kind target operand origin) le initial).2 := by
  let lowered := lowerExpr operand le initial
  have tail : EmitsOnlyRun (ReadyCallObservations module func state) (do
      let source ← intTyOf lowered.1
      let destination := match target with | .int integer => integer | _ => source
      emitDef (.conv kind source destination lowered.1 (some origin))) :=
    (integerType lowered.1).bind fun _ => emitDefinition _ (by intros; intro same; cases same)
  exact child.trans (tail le lowered.2 _ _ rfl)

theorem arrayLiteral (type : Ty) (elements : List Expr)
    (children : EmitsOnly (ReadyCallObservations module func state) initial (lowerExprs elements le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.arrLit type elements) le initial).2 :=
  children.trans (emitDefinition (.arrLit type (lowerExprs elements le initial).1)
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem structLiteral (type : Ty) (elements : List Expr)
    (children : EmitsOnly (ReadyCallObservations module func state) initial (lowerExprs elements le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.structLit type elements) le initial).2 :=
  children.trans (emitDefinition (.structLit type (lowerExprs elements le initial).1)
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem arrayFill (type : Ty) (element : Expr)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr element le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.fill type element) le initial).2 :=
  child.trans (emitDefinition (.arrFill type (lowerExpr element le initial).1)
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem push (owner : Place) (element : Expr) (origin : OriginId)
    (ownerChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2)
    (elementChild : EmitsOnly (ReadyCallObservations module func state) (lowerPlace owner le initial).2
      (lowerExpr element le (lowerPlace owner le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.push owner element origin) le initial).2 :=
  (ownerChild.trans elementChild).trans (emitDefinition
    (.push (lowerPlace owner le initial).1 (lowerExpr element le (lowerPlace owner le initial).2).1 origin)
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem pop (owner : Place) (origin : OriginId)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.pop owner origin) le initial).2 :=
  child.trans (emitDefinition (.pop (lowerPlace owner le initial).1 (some origin))
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem expressionsNil :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExprs [] le initial).2 :=
  .refl _ _

theorem expressionsCons (expression : Expr) (rest : List Expr)
    (head : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2)
    (tail : EmitsOnly (ReadyCallObservations module func state) (lowerExpr expression le initial).2
      (lowerExprs rest le (lowerExpr expression le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial
      (lowerExprs (expression :: rest) le initial).2 :=
  head.trans tail

end Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations
