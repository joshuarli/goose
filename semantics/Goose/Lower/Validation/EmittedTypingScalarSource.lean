import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingScalarCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_source_literal (env : Core.TEnv) (results : List Ty) (type : IntTy) (value : Int) :
    EmittedSourceExpression env results (.lit type value) := by
  intro result start finish source initial before generated builder
  have range : type.inRange value = true := by
    by_cases range : type.inRange value = true
    · exact range
    · simp [Core.tyExpr, range, chk] at source
  exact builder.emitDef (.constInt type value)
    (fun _ => ⟨.data (.int type), by simp [Op.resultTy, range, pure, Except.pure]⟩)
    (by intro active operand member; simp [Op.uses] at member)

theorem emitted_source_bool (env : Core.TEnv) (results : List Ty) (value : Bool) :
    EmittedSourceExpression env results (.bool value) := by
  intro result start finish source initial before generated builder
  exact builder.emitDef (.constBool value) (fun _ => ⟨.data .bool, rfl⟩)
    (by intro active operand member; simp [Op.uses] at member)

theorem emitted_source_not {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) (expr : Expr)
    (child : EmittedSourceExpression env results expr) :
    EmittedSourceExpression env results (.not expr) := by
  intro result start finish source initial before generated builder
  obtain ⟨childFinish, childSource, _⟩ := tyExpr_not_child source
  have lowered := child childSource generated builder
  let value := lowerExpr expr (lowerEnv env.mod env.vars results) before
  apply lowered.emitDef (.boolNot value.1)
  · intro active
    have typed := outputs.expression expr childSource generated rfl active
    exact ⟨.data .bool, by
      simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed,
        pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have same : operand = value.1 := by simpa [Op.uses] using member
    subst operand
    exact (Array.getElem?_eq_some_iff.mp (outputs.expression expr childSource generated rfl active)).1

theorem emitted_source_unary {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) (op : UnOp) (expr : Expr) (origin : OriginId)
    (child : EmittedSourceExpression env results expr) :
    EmittedSourceExpression env results (.un op expr origin) := by
  intro result start finish source initial before generated builder
  obtain ⟨childStart, childFinish, type, childSource, _, signed⟩ := tyExpr_un_child source
  have lowered := child childSource generated builder
  let value := lowerExpr expr (lowerEnv env.mod env.vars results) before
  have sameState : (lowerExpr (.un op expr origin) (lowerEnv env.mod env.vars results) before).2 =
      (emitDef (.un op (intTyOf value.1 (lowerEnv env.mod env.vars results) value.2).1 value.1 (some origin))
        (lowerEnv env.mod env.vars results) value.2).2 := by
    simp only [lowerExpr, bind_run, intTyOf_state, value]
  rw [sameState]
  apply lowered.emitDef
  · intro active
    have typed := outputs.expression expr childSource generated rfl active
    have chosen : (intTyOf value.1 (lowerEnv env.mod env.vars results) value.2).1 = type :=
      congrArg Prod.fst (intTyOf_recorded (le := lowerEnv env.mod env.vars results) typed)
    rw [chosen]
    refine ⟨.data (.int type), ?_⟩
    cases op with
    | neg =>
      simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed, signed rfl,
        pure, Except.pure, bind, Except.bind]
    | bitnot =>
      simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed,
        pure, Except.pure, bind, Except.bind]
  · intro active operand member
    have same : operand = value.1 := by simpa [Op.uses] using member
    subst operand
    exact (Array.getElem?_eq_some_iff.mp (outputs.expression expr childSource generated rfl active)).1

theorem emitted_source_binary {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) (op : BinOp) (left right : Expr) (origin : OriginId)
    (leftChild : EmittedSourceExpression env results left) (rightChild : EmittedSourceExpression env results right) :
    EmittedSourceExpression env results (.bin op left right origin) := by
  intro result start finish source initial before generated builder
  obtain ⟨leftStart, leftFinish, rightStart, rightFinish, type, leftSource, rightSource, _⟩ := tyExpr_bin_children source
  let lhs := lowerExpr left (lowerEnv env.mod env.vars results) before
  let rhs := lowerExpr right (lowerEnv env.mod env.vars results) lhs.2
  have leftBuilder := leftChild leftSource generated builder
  have leftGenerated : GeneratedBuilderState lhs.2 := generated.lowerExpr left rfl
  have rightBuilder := rightChild rightSource leftGenerated leftBuilder
  have rows : rhs.2.cur.isSome = true →
      rhs.2.vals[lhs.1]? = some (some (.data (.int type))) ∧
      rhs.2.vals[rhs.1]? = some (some (.data (.int type))) := by
    intro active
    have leftLive := (dead_lowerExpr right).live_before rfl active
    have leftTyped := outputs.expression left leftSource generated rfl leftLive
    exact ⟨(types_lowerExpr right _ lhs.2 _ _ rfl) _ _ leftTyped,
      outputs.expression right rightSource leftGenerated rfl active⟩
  have sameState : (lowerExpr (.bin op left right origin) (lowerEnv env.mod env.vars results) before).2 =
      (emitDef (.bin op (intTyOf lhs.1 (lowerEnv env.mod env.vars results) rhs.2).1 lhs.1 rhs.1 (some origin))
        (lowerEnv env.mod env.vars results) rhs.2).2 := by
    simp only [lowerExpr, bind_run, intTyOf_state, lhs, rhs]
  rw [sameState]
  apply rightBuilder.emitDef
  · intro active
    obtain ⟨leftTyped, rightTyped⟩ := rows active
    have chosen : (intTyOf lhs.1 (lowerEnv env.mod env.vars results) rhs.2).1 = type :=
      congrArg Prod.fst (intTyOf_recorded (le := lowerEnv env.mod env.vars results) leftTyped)
    rw [chosen]
    refine ⟨.data (.int type), ?_⟩
    dsimp only [lhs, rhs] at leftTyped rightTyped ⊢
    simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, leftTyped, rightTyped,
      pure, Except.pure, bind, Except.bind]
  · intro active operand member
    obtain ⟨leftTyped, rightTyped⟩ := rows active
    have either : operand = lhs.1 ∨ operand = rhs.1 := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp leftTyped).1
    · exact (Array.getElem?_eq_some_iff.mp rightTyped).1

end Goose.Lower.Validation
