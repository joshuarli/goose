import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

inductive TypedValues (state : LS) : List Ty → List ValueId → Prop where
  | nil : TypedValues state [] []
  | cons {ty : Ty} {value : ValueId} {types : List Ty} {values : List ValueId}
      (head : state.vals[value]? = some (some (.data ty)))
      (tail : TypedValues state types values) : TypedValues state (ty :: types) (value :: values)

theorem TypedValues.length_eq {state : LS} {types : List Ty} {values : List ValueId}
    (typed : TypedValues state types values) : types.length = values.length := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem TypedValues.retained {before after : LS} {types : List Ty} {values : List ValueId}
    (typed : TypedValues before types values) (retained : TypePrefix before after) :
    TypedValues after types values := by
  induction typed with
  | nil => exact .nil
  | cons head _ ih => exact .cons (retained _ _ head) ih

theorem TypedValues.replicate {state : LS} {element : Ty} {count : Nat} {values : List ValueId}
    (typed : TypedValues state (List.replicate count element) values) :
    ∀ value ∈ values, state.vals[value]? = some (some (.data element)) := by
  induction count generalizing values with
  | zero => cases typed; simp
  | succ count ih =>
    cases typed with
    | cons head tail =>
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact ih tail value member

private theorem array_elements_forIn {le : LEnv} {state : LS} {element : Ty} {values : List ValueId}
    (typed : ∀ value ∈ values, state.vals[value]? = some (some (.data element))) :
    forIn values PUnit.unit (fun value _ => do
      unless (← (tyEnv le state).dataTy value) = element do tyErr "array element of another type than the array's"
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    have head := typed value (by simp)
    have tail := ih (fun value member => typed value (by simp [member]))
    rw [List.forIn_cons]
    simpa [TyEnv.dataTy, TyEnv.valTy, tyEnv, head, pure, Except.pure, bind, Except.bind] using tail

def ArrayLiteralCount : Ty → Nat → Prop
  | .arr _ size, count => count = size
  | .limited _ capacity, count => count ≤ capacity
  | _, _ => True

theorem arrayLiteral_resultTy {le : LEnv} {state : LS} {ty element : Ty} {values : List ValueId}
    (shape : GIR.arrayElem? ty = some element) (count : ArrayLiteralCount ty values.length)
    (typed : ∀ value ∈ values, state.vals[value]? = some (some (.data element))) :
    (Op.arrLit ty values).resultTy (tyEnv le state) = .ok (.data ty) := by
  have elements := array_elements_forIn (le := le) typed
  cases ty <;> simp only [GIR.arrayElem?] at shape
  all_goals try contradiction
  all_goals cases shape
  all_goals simp only [ArrayLiteralCount] at count
  all_goals
    simp only [Op.resultTy, count, ↓reduceIte]
    rw [elements]
    rfl

theorem tyExpr_arrayLiteral_children {env : Core.TEnv} {arrayTy resultTy : Ty} {exprs : List Expr}
    {start finish : Nat}
    (source : Core.tyExpr env (.arrLit arrayTy exprs) start = .ok (resultTy, finish)) :
    resultTy = arrayTy ∧ ∃ element childStart childFinish,
      GIR.arrayElem? arrayTy = some element ∧ ArrayLiteralCount arrayTy exprs.length ∧
      Core.tyExprsAs env element exprs childStart = .ok ((), childFinish) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, childStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases arrayTy with
  | arr element size =>
    by_cases flat : element.flat = true
    · simp only [flat, ite_true] at source
      by_cases count : exprs.length = size
      · simp only [count, ite_true] at source
        obtain ⟨_, childFinish, children, source⟩ := (st_bind_ok _ _ _ _).mp source
        have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        exact ⟨shape, element, childStart, childFinish, rfl, count, children⟩
      · simp [count, chk] at source
    · simp [flat, chk] at source
  | grow element | growshrink element =>
    by_cases flat : element.flat = true
    · simp only [flat, ite_true] at source
      obtain ⟨_, childFinish, children, source⟩ := (st_bind_ok _ _ _ _).mp source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      exact ⟨shape, element, childStart, childFinish, rfl, True.intro, children⟩
    · simp [flat, chk] at source
  | limited element capacity =>
    by_cases allowed : (element.flat && decide (exprs.length ≤ capacity)) = true
    · simp only [allowed, ite_true] at source
      obtain ⟨_, childFinish, children, source⟩ := (st_bind_ok _ _ _ _).mp source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      have count : exprs.length ≤ capacity := of_decide_eq_true (Bool.and_eq_true_iff.mp allowed).2
      exact ⟨shape, element, childStart, childFinish, rfl, count, children⟩
    · simp [allowed, chk] at source
  | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem tyExprsAs_structExprs {env : Core.TEnv} {element : Ty} {exprs : List Expr} {start finish : Nat}
    (source : Core.tyExprsAs env element exprs start = .ok ((), finish)) :
    Core.tyStructExprs env (List.replicate exprs.length element) exprs start = .ok ((), finish) := by
  induction exprs generalizing start with
  | nil => exact source
  | cons expr rest ih =>
    simp only [Core.tyExprsAs] at source
    obtain ⟨ty, next, child, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (ty == element) = true
    · simp only [equal, ite_true] at source
      simp only [List.length_cons, List.replicate_succ, Core.tyStructExprs]
      apply (st_bind_ok _ _ _ _).mpr
      exact ⟨ty, next, child, by simpa only [equal, ite_true] using ih source⟩
    · simp [equal, chk] at source

private theorem struct_elements_forIn {le : LEnv} {state : LS} {fields : List StructField} {values : List ValueId}
    (typed : TypedValues state (fields.map (·.ty)) values) :
    forIn (values.zip fields) PUnit.unit (fun (pair : ValueId × StructField) _ => do
      unless (← (tyEnv le state).dataTy pair.1) == StructField.ty pair.2 do tyErr "struct initializer has another field type"
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit := by
  induction fields generalizing values with
  | nil => cases typed; rfl
  | cons field fields ih =>
    cases typed with
    | cons head tail =>
      rw [List.zip_cons_cons, List.forIn_cons]
      simpa [TyEnv.dataTy, TyEnv.valTy, tyEnv, head, pure, Except.pure, bind, Except.bind] using ih tail

theorem structLiteral_resultTy {env : Core.TEnv} {ty : Ty} {descriptor : StructDef}
    {start finish : Nat} (definition : Core.structDef env ty start = .ok (descriptor, finish))
    {vars : Array LocalVar} {results : List Ty} {state : LS} {values : List ValueId}
    (typed : TypedValues state (descriptor.fields.toList.map (·.ty)) values) :
    (Op.structLit ty values).resultTy (tyEnv (lowerEnv env.mod vars results) state) = .ok (.data ty) := by
  obtain ⟨id, fields, shape, _, nominal, lookup, _⟩ := structDef_ok _ _ _ _ _ definition
  have payload : fields = TyList.ofList (descriptor.fields.toList.map (·.ty)) := by
    simpa only [Core.Module.structType?, lookup, Option.map_some, shape,
      Option.some.injEq, Ty.structT.injEq, true_and] using nominal.symm
  have length : values.length = descriptor.fields.size := by
    simpa only [List.length_map, Array.length_toList] using typed.length_eq.symm
  have elements := struct_elements_forIn (le := lowerEnv env.mod vars results) typed
  simp only [Op.resultTy, tyEnv, lowerEnv, shape, lookup, payload, BEq.rfl, ite_true, length]
  simp only [tyEnv, lowerEnv, pure, Except.pure, bind, Except.bind] at elements ⊢
  rw [elements]

theorem tyExpr_structLiteral_children {env : Core.TEnv} {structTy resultTy : Ty} {exprs : List Expr}
    {start finish : Nat}
    (source : Core.tyExpr env (.structLit structTy exprs) start = .ok (resultTy, finish)) :
    resultTy = structTy ∧ ∃ descriptor definitionFinish childStart childFinish,
      Core.structDef env structTy start = .ok (descriptor, definitionFinish) ∧
      Core.tyStructExprs env (descriptor.fields.toList.map (·.ty)) exprs childStart = .ok ((), childFinish) := by
  simp only [Core.tyExpr] at source
  obtain ⟨descriptor, definitionFinish, definition, source⟩ := (st_bind_ok _ _ _ _).mp source
  by_cases count : (descriptor.fields.size == exprs.length) = true
  · simp only [count, ite_true] at source
    obtain ⟨_, childFinish, children, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    exact ⟨shape, descriptor, definitionFinish, definitionFinish, childFinish, definition, children⟩
  · simp [count, chk] at source

theorem tyExpr_fill_child {env : Core.TEnv} {arrayTy resultTy : Ty} {expr : Expr} {start finish : Nat}
    (source : Core.tyExpr env (.fill arrayTy expr) start = .ok (resultTy, finish)) :
    resultTy = arrayTy ∧ ∃ element size childStart childFinish,
      arrayTy = .arr element size ∧ Core.tyExpr env expr childStart = .ok (element, childFinish) := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, childStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases arrayTy with
  | arr element size =>
    by_cases flat : element.flat = true
    · simp only [flat, ite_true] at source
      obtain ⟨argTy, childFinish, child, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases equal : (argTy == element) = true
      · simp only [equal, ite_true] at source
        have same := eq_of_beq equal
        subst argTy
        have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        exact ⟨shape, element, size, childStart, childFinish, rfl, child⟩
      · simp only [equal] at source
        change ((rej .type "fill value of another type than the elements" : Core.T Unit) >>=
          fun _ => pure (.arr element size)) childFinish = .ok (resultTy, finish) at source
        obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
        exact (rej_ok _ _ _ _).mp rejected |>.elim
    · simp [flat, chk] at source
  | _ => exact (rej_ok _ _ _ _).mp source |>.elim

end Goose.Lower.Validation
