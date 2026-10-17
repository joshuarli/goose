import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingSourceOutputs

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_source_comparison {env : Core.TEnv} {results : List Ty}
    (op : CmpOp) (left right : Expr)
    (leftChild : EmittedSourceExpression env results left) (rightChild : EmittedSourceExpression env results right) :
    EmittedSourceExpression env results (.cmp op left right) := by
  intro result start finish source initial before generated builder
  obtain ⟨leftType, rightType, leftFinish, rightFinish, leftSource, rightSource, _, allowed⟩ :=
    tyExpr_comparison_children source
  let le := lowerEnv env.mod env.vars results
  let lhs := lowerExpr left le before
  let rhs := lowerExpr right le lhs.2
  have lhsBuilder := leftChild leftSource generated builder
  have lhsGenerated : GeneratedBuilderState lhs.2 := generated.lowerExpr left rfl
  have rhsBuilder := rightChild rightSource lhsGenerated lhsBuilder
  have rows : rhs.2.cur.isSome = true →
      rhs.2.vals[lhs.1]? = some (some (.data leftType)) ∧
      rhs.2.vals[rhs.1]? = some (some (.data rightType)) := by
    intro active
    have lhsLive := (dead_lowerExpr right).live_before rfl active
    have lhsTyped := lowerExpr_generated_typed left leftSource (show lowerExpr left le before = lhs from rfl) lhsLive generated
    exact ⟨(types_lowerExpr right le lhs.2 _ _ rfl) _ _ lhsTyped,
      lowerExpr_generated_typed right rightSource rfl active lhsGenerated⟩
  have sameState : (lowerExpr (.cmp op left right) le before).2 =
      (match (generalizing := false) (valTy lhs.1 le rhs.2).1 with
        | .data (.int integer) => (emitDef (.cmp op integer lhs.1 rhs.1) le rhs.2).2
        | _ => (emitDef (.boolCmp op lhs.1 rhs.1) le rhs.2).2) := by
    simp only [lowerExpr, bind_run, valTy_run, lhs, rhs]
    split <;> simp_all
  rw [sameState]
  split
  next integer observed =>
    apply rhsBuilder.emitDef (.cmp op integer lhs.1 rhs.1)
    · intro active
      obtain ⟨lhsTyped, rhsTyped⟩ := rows active
      rcases allowed with ⟨type, leftShape, rightShape⟩ | ⟨leftShape, rightShape, equalities⟩
      · subst leftType rightType
        have expected := congrArg Prod.fst (valTy_of_recorded (le := le) lhsTyped)
        have same : integer = type := by rw [expected] at observed; simpa using observed.symm
        subst integer
        dsimp only [le, lhs, rhs] at lhsTyped rhsTyped ⊢
        exact ⟨.data .bool, by
          simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, lhsTyped, rhsTyped,
            pure, Except.pure, bind, Except.bind]⟩
      · subst leftType rightType
        have expected := congrArg Prod.fst (valTy_of_recorded (le := le) lhsTyped)
        rw [expected] at observed
        cases observed
    · intro active operand member
      obtain ⟨lhsTyped, rhsTyped⟩ := rows active
      have either : operand = lhs.1 ∨ operand = rhs.1 := by simpa [Op.uses] using member
      rcases either with rfl | rfl
      · exact (Array.getElem?_eq_some_iff.mp lhsTyped).1
      · exact (Array.getElem?_eq_some_iff.mp rhsTyped).1
  next other notInteger =>
    apply rhsBuilder.emitDef (.boolCmp op lhs.1 rhs.1)
    · intro active
      obtain ⟨lhsTyped, rhsTyped⟩ := rows active
      rcases allowed with ⟨type, leftShape, rightShape⟩ | ⟨leftShape, rightShape, equalities⟩
      · subst leftType rightType
        exact False.elim (notInteger type (congrArg Prod.fst (valTy_of_recorded (le := le) lhsTyped)))
      · subst leftType rightType
        dsimp only [le, lhs, rhs] at lhsTyped rhsTyped ⊢
        rcases equalities with rfl | rfl
        all_goals exact ⟨.data .bool, by
          simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, lhsTyped, rhsTyped,
            pure, Except.pure, bind, Except.bind]⟩
    · intro active operand member
      obtain ⟨lhsTyped, rhsTyped⟩ := rows active
      have either : operand = lhs.1 ∨ operand = rhs.1 := by simpa [Op.uses] using member
      rcases either with rfl | rfl
      · exact (Array.getElem?_eq_some_iff.mp lhsTyped).1
      · exact (Array.getElem?_eq_some_iff.mp rhsTyped).1

end Goose.Lower.Validation
