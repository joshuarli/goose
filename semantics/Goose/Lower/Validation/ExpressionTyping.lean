import Goose.Lower.Validation.ScalarTyping
import Goose.Lower.Validation.ExpressionTypingBorrowOps
import Goose.Lower.Validation.ViewTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

mutual

def StaticExpression : Expr → Prop
  | .lit _ _ | .bool _ => True
  | .read p | .ref .readOnly p => StaticPlace p
  | .ref .mutable (.var _) | .ref .mutable (.global _) => True
  | .un _ e _ | .not e => StaticExpression e
  | .bin _ a b _ => StaticExpression a ∧ StaticExpression b
  | .len v => StaticView v
  | _ => False

def StaticPlace : Place → Prop
  | .var _ | .global _ => True
  | .field p _ => StaticPlace p
  | .deref e => StaticExpression e
  | .elem v i _ => StaticView v ∧ StaticExpression i

def StaticView : View → Prop
  | .of p => StaticPlace p
  | .val e => StaticExpression e

end

mutual

theorem lowerExpr_static_typed (e : Expr) (supported : StaticExpression e)
    {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env e start = .ok (ty, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerExpr e (lowerEnv env.mod env.vars results) before
    after.cur = before.cur ∧ after.vals[value]? = some (some (.data ty)) := by
  cases e with
  | lit t n =>
    have result := lowerExpr_literal_typed source (lowerEnv env.mod env.vars results) before live
    exact ⟨result.2.1, result.2.2⟩
  | bool b =>
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    change ty = .bool at shape
    subst ty
    exact lowerExpr_bool_typed b _ before live
  | read p =>
    obtain ⟨info, next, childSource, shape⟩ := tyExpr_read_place source
    subst ty
    cases childRun : lowerPlace p (lowerEnv env.mod env.vars results) before with
    | mk value mid =>
      have child := lowerPlace_static_typed p supported childSource results before live
      rw [childRun] at child
      obtain ⟨mu, same, typed⟩ := child
      have loaded := lowerExpr_read_typed_of_place childRun typed (same.trans live)
      simpa only [same] using loaded
  | ref mu p =>
    cases mu with
    | mutable =>
      cases p with
      | var x => exact lowerExpr_ref_var_exact source results before live
      | global g => exact lowerExpr_ref_global_exact source env.vars results before live
      | _ => contradiction
    | readOnly =>
      obtain ⟨info, next, childSource, shape, _⟩ := tyExpr_ref_place source
      subst ty
      cases childRun : lowerPlace p (lowerEnv env.mod env.vars results) before with
      | mk value mid =>
        have child := lowerPlace_static_typed p supported childSource results before live
        rw [childRun] at child
        obtain ⟨actual, same, typed⟩ := child
        have permission : actual.atLeast .readOnly = true := by cases actual <;> rfl
        have frozen := borrowTo_typed (le := lowerEnv env.mod env.vars results) typed permission (same.trans live)
        simpa only [lowerExpr, bind_run, childRun, same] using frozen
  | un op e origin =>
    obtain ⟨childStart, childFinish, intTy, childSource, shape, signed⟩ := tyExpr_un_child source
    subst ty
    cases childRun : lowerExpr e (lowerEnv env.mod env.vars results) before with
    | mk value mid =>
      have child := lowerExpr_static_typed e supported childSource results before live
      rw [childRun] at child
      have lowered := lowerExpr_un_typed_of_child (origin := origin) childRun child.2 signed (child.1.trans live)
      simpa only [child.1] using lowered
  | bin op a b origin =>
    obtain ⟨aStart, aFinish, bStart, bFinish, intTy, aSource, bSource, shape⟩ := tyExpr_bin_children source
    subst ty
    obtain ⟨aSupported, bSupported⟩ := supported
    cases aRun : lowerExpr a (lowerEnv env.mod env.vars results) before with
    | mk av aState =>
      have left := lowerExpr_static_typed a aSupported aSource results before live
      rw [aRun] at left
      cases bRun : lowerExpr b (lowerEnv env.mod env.vars results) aState with
      | mk bv mid =>
        have right := lowerExpr_static_typed b bSupported bSource results aState (left.1.trans live)
        rw [bRun] at right
        have lowered := lowerExpr_bin_typed_of_children (op := op) (origin := origin) aRun left.2 bRun right.2
          (right.1.trans (left.1.trans live))
        simpa only [right.1, left.1] using lowered
  | not e =>
    obtain ⟨childFinish, childSource, shape⟩ := tyExpr_not_child source
    subst ty
    cases childRun : lowerExpr e (lowerEnv env.mod env.vars results) before with
    | mk value mid =>
      have child := lowerExpr_static_typed e supported childSource results before live
      rw [childRun] at child
      have lowered := lowerExpr_not_typed_of_child childRun child.2 (child.1.trans live)
      simpa only [child.1] using lowered
  | len v =>
    simp only [Core.tyExpr] at source
    obtain ⟨pair, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp tail)
    change ty = .int .i64 at shape
    subst ty
    cases childRun : lowerView v (lowerEnv env.mod env.vars results) before with
    | mk value mid =>
      have child := lowerView_static_typed v supported childSource results before live
      rw [childRun] at child
      obtain ⟨mu, same, typed⟩ := child
      have operation : (Op.viewLen value).resultTy (tyEnv (lowerEnv env.mod env.vars results) mid) =
          .ok (.data (.int .i64)) := by
        simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, tyEnv, typed, pure, Except.pure, bind, Except.bind]
      have emitted := emitDef_recorded (same.trans live) operation
      simp only [lowerExpr, bind_run, childRun]
      exact ⟨emitted.2.1.trans same, emitted.2.2.1⟩
  | _ => contradiction

theorem lowerPlace_static_typed (p : Place) (supported : StaticPlace p)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env p start = .ok (info, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace p (lowerEnv env.mod env.vars results) before
    ∃ mu, after.cur = before.cur ∧ after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  cases p with
  | var x => exact lowerPlace_var_typed source results before live
  | global g => exact lowerPlace_global_typed source env.vars results before live
  | field owner index =>
    have children := source
    simp only [Core.tyPlace] at children
    obtain ⟨ownerInfo, ownerFinish, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp children
    cases childRun : lowerPlace owner (lowerEnv env.mod env.vars results) before with
    | mk value mid =>
      have child := lowerPlace_static_typed owner supported ownerSource results before live
      rw [childRun] at child
      obtain ⟨mu, same, typed⟩ := child
      have lowered := lowerPlace_field_typed_of_owner ownerSource source childRun typed (same.trans live)
      simpa only [same] using lowered
  | deref e =>
    cases special : Core.sliceRefTy env e with
    | none =>
      obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
      exact ⟨mu, lowerExpr_static_typed e supported childSource results before live⟩
    | some target =>
      cases e with
      | read p =>
        cases p with
        | var x => exact lowerPlace_deref_read_variable_exact source results before live
        | _ => simp [Core.sliceRefTy] at special
      | _ => simp [Core.sliceRefTy] at special
  | elem v i origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, writable, intTy, viewSource, indexSource⟩ :=
      tyPlace_elem_children source
    obtain ⟨vSupported, iSupported⟩ := supported
    cases vRun : lowerView v (lowerEnv env.mod env.vars results) before with
    | mk vv vState =>
      have viewTyped := lowerView_static_typed v vSupported viewSource results before live
      rw [vRun] at viewTyped
      obtain ⟨mu, same, typed⟩ := viewTyped
      cases iRun : lowerExpr i (lowerEnv env.mod env.vars results) vState with
      | mk iv mid =>
        have indexTyped := lowerExpr_static_typed i iSupported indexSource results vState (same.trans live)
        rw [iRun] at indexTyped
        have lowered := lowerPlace_elem_typed_of_children (origin := origin) vRun typed iRun indexTyped.2
          (indexTyped.1.trans (same.trans live))
        simp only [lowerPlace, bind_run, vRun, iRun] at lowered ⊢
        exact ⟨mu, lowered.1.trans (indexTyped.1.trans same), lowered.2⟩

theorem lowerView_static_typed (v : View) (supported : StaticView v)
    {env : Core.TEnv} {pair : Ty × Bool} {start finish : Nat}
    (source : Core.tyView env v start = .ok (pair, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerView v (lowerEnv env.mod env.vars results) before
    ∃ mu, after.cur = before.cur ∧ after.vals[value]? = some (some (.view mu pair.1)) := by
  cases v with
  | of p =>
    have children := source
    simp only [Core.tyView] at children
    obtain ⟨info, next, childSource, _⟩ := (st_bind_ok _ _ _ _).mp children
    cases childRun : lowerPlace p (lowerEnv env.mod env.vars results) before with
    | mk value mid =>
      have child := lowerPlace_static_typed p supported childSource results before live
      rw [childRun] at child
      obtain ⟨mu, same, typed⟩ := child
      have lowered := lowerView_of_typed_of_place childSource source childRun typed (same.trans live)
      simpa only [same] using lowered
  | val e =>
    have children := source
    simp only [Core.tyView] at children
    obtain ⟨childTy, next, childSource, tail⟩ := (st_bind_ok _ _ _ _).mp children
    cases childTy with
    | slice mu element =>
      cases childRun : lowerExpr e (lowerEnv env.mod env.vars results) before with
      | mk value mid =>
        have child := lowerExpr_static_typed e supported childSource results before live
        rw [childRun] at child
        have lowered := lowerView_val_typed_of_expr childSource source childRun child.2 (child.1.trans live)
        simp only [lowerView, bind_run, childRun] at lowered ⊢
        exact ⟨mu, lowered.1.trans child.1, lowered.2⟩
    | _ => exact (rej_ok _ _ _ _).mp tail |>.elim

end

end Goose.Lower.Validation

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerPlace_static_live_typed {place : Place} (supported : StaticPlace place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) :
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  have initial := (dead_lowerPlace place).live_before run live
  cases current : before.cur with
  | none => simp [current] at initial
  | some block =>
    have typed := lowerPlace_static_typed place supported source results before current
    rw [run] at typed
    obtain ⟨mu, _, typed⟩ := typed
    exact ⟨mu, typed⟩

end Goose.Lower.Validation
