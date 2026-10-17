import Goose.Lower.Validation.EmittedTypingOperations
import Goose.Lower.Validation.ScalarTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def EmittedScalarExpression : Expr → Prop
  | .lit _ _ | .bool _ => True
  | .un _ child _ | .not child => EmittedScalarExpression child
  | .bin _ left right _ => EmittedScalarExpression left ∧ EmittedScalarExpression right
  | _ => False

theorem emitted_lowerExpr_scalar (expr : Expr) (supported : EmittedScalarExpression expr)
    {env : Core.TEnv} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (type, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let le := lowerEnv env.mod env.vars results
    let (value, after) := lowerExpr expr le before
    EmittedAt le before (lowerExpr expr) ∧ after.cur = before.cur ∧
      after.vals[value]? = some (some (.data type)) := by
  cases expr with
  | lit integer value =>
    have typed := lowerExpr_literal_typed source (lowerEnv env.mod env.vars results) before live
    have range : integer.inRange value = true := by
      by_cases range : integer.inRange value = true
      · exact range
      · simp [Core.tyExpr, range, chk] at source
    exact ⟨emitted_constInt _ _ _ _ range, typed.2⟩
  | bool value =>
    have same := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    change type = .bool at same
    subst type
    exact ⟨emitted_constBool _ _ _, lowerExpr_bool_typed _ _ _ live⟩
  | un op child origin =>
    obtain ⟨childStart, childFinish, integer, childSource, same, signed⟩ := tyExpr_un_child source
    subst type
    cases childRun : lowerExpr child (lowerEnv env.mod env.vars results) before with
    | mk value middle =>
      have childProof := emitted_lowerExpr_scalar child supported childSource results before live
      simp only [EmittedAt, childRun] at childProof
      have output := lowerExpr_un_typed_of_child (op := op) (origin := origin) childRun childProof.2.2 signed (childProof.2.1.trans live)
      have integerRead := intTyOf_recorded (le := lowerEnv env.mod env.vars results) childProof.2.2
      have trace := childProof.1.append (emitted_un (le := lowerEnv env.mod env.vars results) childProof.2.2 op signed (some origin))
      refine ⟨?_, ?_⟩
      · simpa only [EmittedAt, lowerExpr, bind_run, childRun, integerRead] using trace
      · exact ⟨output.1.trans childProof.2.1, output.2⟩
  | bin op left right origin =>
    obtain ⟨leftStart, leftFinish, rightStart, rightFinish, integer, leftSource, rightSource, same⟩ := tyExpr_bin_children source
    subst type
    cases leftRun : lowerExpr left (lowerEnv env.mod env.vars results) before with
    | mk leftValue leftEnd =>
      have leftProof := emitted_lowerExpr_scalar left supported.1 leftSource results before live
      simp only [EmittedAt, leftRun] at leftProof
      cases rightRun : lowerExpr right (lowerEnv env.mod env.vars results) leftEnd with
      | mk rightValue middle =>
        have rightProof := emitted_lowerExpr_scalar right supported.2 rightSource results leftEnd (leftProof.2.1.trans live)
        simp only [EmittedAt, rightRun] at rightProof
        have retained := rightProof.1.prefix.typed leftValue (.data (.int integer)) leftProof.2.2
        have integerRead := intTyOf_recorded (le := lowerEnv env.mod env.vars results) retained
        have output := lowerExpr_bin_typed_of_children (op := op) (origin := origin)
          leftRun leftProof.2.2 rightRun rightProof.2.2 (rightProof.2.1.trans (leftProof.2.1.trans live))
        have trace := (leftProof.1.append rightProof.1).append
          (emitted_bin (le := lowerEnv env.mod env.vars results) retained rightProof.2.2 op (some origin))
        refine ⟨?_, ?_⟩
        · simpa only [EmittedAt, lowerExpr, bind_run, leftRun, rightRun, integerRead] using trace
        · exact ⟨output.1.trans (rightProof.2.1.trans leftProof.2.1), output.2⟩
  | not child =>
    obtain ⟨childFinish, childSource, same⟩ := tyExpr_not_child source
    subst type
    cases childRun : lowerExpr child (lowerEnv env.mod env.vars results) before with
    | mk value middle =>
      have childProof := emitted_lowerExpr_scalar child supported childSource results before live
      simp only [EmittedAt, childRun] at childProof
      have output := lowerExpr_not_typed_of_child childRun childProof.2.2 (childProof.2.1.trans live)
      have trace := childProof.1.append (emitted_boolNot (le := lowerEnv env.mod env.vars results) childProof.2.2)
      refine ⟨?_, ?_⟩
      · simpa only [EmittedAt, lowerExpr, bind_run, childRun] using trace
      · exact ⟨output.1.trans childProof.2.1, output.2⟩
  | _ => contradiction

end Goose.Lower.Validation
