import Goose.Lower.Validation.EmittedTypingScalars
import Goose.Lower.Validation.EmittedTypingCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_lowerExpr_scalar_checked (expr : Expr) (supported : EmittedScalarExpression expr)
    {env : Core.TEnv} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (type, finish))
    (results : List Ty) (before : LS) {initial : LS}
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) {block : BlockId} (live : before.cur = some block) :
    let le := lowerEnv env.mod env.vars results
    let (value, after) := lowerExpr expr le before
    EmittedBuilder le initial after ∧ after.cur = before.cur ∧
      after.vals[value]? = some (some (.data type)) := by
  cases expr with
  | lit integer value =>
    have typed := lowerExpr_literal_typed source (lowerEnv env.mod env.vars results) before live
    have range : integer.inRange value = true := by
      by_cases range : integer.inRange value = true
      · exact range
      · simp [Core.tyExpr, range, chk] at source
    exact ⟨builder.emitDef (.constInt integer value)
      (fun _ => ⟨.data (.int integer), by simp [Op.resultTy, range, pure, Except.pure]⟩)
      (by intro active operand member; simp [Op.uses] at member), typed.2⟩
  | bool value =>
    have same := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    change type = .bool at same
    subst type
    exact ⟨builder.emitDef (.constBool value) (fun _ => ⟨.data .bool, rfl⟩)
      (by intro active operand member; simp [Op.uses] at member), lowerExpr_bool_typed _ _ _ live⟩
  | un op child origin =>
    obtain ⟨childStart, childFinish, integer, childSource, same, signed⟩ := tyExpr_un_child source
    subst type
    cases childRun : lowerExpr child (lowerEnv env.mod env.vars results) before with
    | mk value middle =>
      have childProof := emitted_lowerExpr_scalar_checked child supported childSource results before builder live
      simp only [childRun] at childProof
      have output := lowerExpr_un_typed_of_child (op := op) (origin := origin) childRun childProof.2.2 signed (childProof.2.1.trans live)
      have integerRead := intTyOf_recorded (le := lowerEnv env.mod env.vars results) childProof.2.2
      have trace := childProof.1.emitDef (.un op integer value (some origin))
        (fun _ => ⟨.data (.int integer), by
          cases op with
          | neg => simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
              childProof.2.2, signed rfl, pure, Except.pure, bind, Except.bind]
          | bitnot => simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
              childProof.2.2, pure, Except.pure, bind, Except.bind]⟩)
        (by
          intro active operand member
          have same : operand = value := by simpa [Op.uses] using member
          subst operand
          exact (Array.getElem?_eq_some_iff.mp childProof.2.2).1)
      refine ⟨?_, ?_⟩
      · have sameState : (lowerExpr (.un op child origin) (lowerEnv env.mod env.vars results) before).2 =
            (emitDef (.un op integer value (some origin)) (lowerEnv env.mod env.vars results) middle).2 := by
          simp only [lowerExpr, bind_run, childRun, integerRead]
        change EmittedBuilder (lowerEnv env.mod env.vars results) initial
          (lowerExpr (.un op child origin) (lowerEnv env.mod env.vars results) before).2
        rw [sameState]
        exact trace
      · exact ⟨output.1.trans childProof.2.1, output.2⟩
  | bin op left right origin =>
    obtain ⟨leftStart, leftFinish, rightStart, rightFinish, integer, leftSource, rightSource, same⟩ := tyExpr_bin_children source
    subst type
    cases leftRun : lowerExpr left (lowerEnv env.mod env.vars results) before with
    | mk leftValue leftEnd =>
      have leftProof := emitted_lowerExpr_scalar_checked left supported.1 leftSource results before builder live
      simp only [leftRun] at leftProof
      cases rightRun : lowerExpr right (lowerEnv env.mod env.vars results) leftEnd with
      | mk rightValue middle =>
        have rightProof := emitted_lowerExpr_scalar_checked right supported.2 rightSource results leftEnd leftProof.1 (leftProof.2.1.trans live)
        simp only [rightRun] at rightProof
        have retained := (types_lowerExpr right _ _ _ _ rightRun) leftValue (.data (.int integer)) leftProof.2.2
        have integerRead := intTyOf_recorded (le := lowerEnv env.mod env.vars results) retained
        have output := lowerExpr_bin_typed_of_children (op := op) (origin := origin)
          leftRun leftProof.2.2 rightRun rightProof.2.2 (rightProof.2.1.trans (leftProof.2.1.trans live))
        have trace := rightProof.1.emitDef (.bin op integer leftValue rightValue (some origin))
          (fun _ => ⟨.data (.int integer), by
            simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
              retained, rightProof.2.2, pure, Except.pure, bind, Except.bind]⟩)
          (by
            intro active operand member
            have either : operand = leftValue ∨ operand = rightValue := by simpa [Op.uses] using member
            rcases either with rfl | rfl
            · exact (Array.getElem?_eq_some_iff.mp retained).1
            · exact (Array.getElem?_eq_some_iff.mp rightProof.2.2).1)
        refine ⟨?_, ?_⟩
        · have sameState : (lowerExpr (.bin op left right origin) (lowerEnv env.mod env.vars results) before).2 =
              (emitDef (.bin op integer leftValue rightValue (some origin)) (lowerEnv env.mod env.vars results) middle).2 := by
            simp only [lowerExpr, bind_run, leftRun, rightRun, integerRead]
          change EmittedBuilder (lowerEnv env.mod env.vars results) initial
            (lowerExpr (.bin op left right origin) (lowerEnv env.mod env.vars results) before).2
          rw [sameState]
          exact trace
        · exact ⟨output.1.trans (rightProof.2.1.trans leftProof.2.1), output.2⟩
  | not child =>
    obtain ⟨childFinish, childSource, same⟩ := tyExpr_not_child source
    subst type
    cases childRun : lowerExpr child (lowerEnv env.mod env.vars results) before with
    | mk value middle =>
      have childProof := emitted_lowerExpr_scalar_checked child supported childSource results before builder live
      simp only [childRun] at childProof
      have output := lowerExpr_not_typed_of_child childRun childProof.2.2 (childProof.2.1.trans live)
      have trace := childProof.1.emitDef (.boolNot value)
        (fun _ => ⟨.data .bool, by
          simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, childProof.2.2,
            pure, Except.pure, bind, Except.bind]⟩)
        (by
          intro active operand member
          have same : operand = value := by simpa [Op.uses] using member
          subst operand
          exact (Array.getElem?_eq_some_iff.mp childProof.2.2).1)
      refine ⟨?_, ?_⟩
      · have sameState : (lowerExpr (.not child) (lowerEnv env.mod env.vars results) before).2 =
            (emitDef (.boolNot value) (lowerEnv env.mod env.vars results) middle).2 := by
          simp only [lowerExpr, bind_run, childRun]
        change EmittedBuilder (lowerEnv env.mod env.vars results) initial
          (lowerExpr (.not child) (lowerEnv env.mod env.vars results) before).2
        rw [sameState]
        exact trace
      · exact ⟨output.1.trans childProof.2.1, output.2⟩
  | _ => contradiction

end Goose.Lower.Validation
