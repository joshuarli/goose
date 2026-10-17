import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_checked_lowerBound_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) (bound : Bound) {start finish : Nat}
    (source : Core.tyBound env bound start = .ok ((), finish))
    (children : ∀ expr, bound = .expr expr ∨ bound = .fromEnd expr →
      ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
      ∀ {initial before : LS}, GeneratedBuilderState before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr expr (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerBound bound (lowerEnv env.mod env.vars results) before).2 ∧
    ((lowerBound bound (lowerEnv env.mod env.vars results) before).2.cur.isSome = true →
      BoundTyped (lowerBound bound (lowerEnv env.mod env.vars results) before).2
        (lowerBound bound (lowerEnv env.mod env.vars results) before).1) := by
  cases bound with
  | omitted => exact ⟨builder, fun _ => trivial⟩
  | expr expr | fromEnd expr =>
    obtain ⟨type, childFinish, childSource⟩ := tyBound_child source
    exact ⟨children expr (by simp) childSource generated builder,
      fun active => ⟨type, outputs.expression expr childSource generated rfl active⟩⟩

theorem emitted_checked_len_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {view : View} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.len view) start = .ok (type, finish))
    (child : ∀ {element : Ty} {writable : Bool} {start finish : Nat},
      Core.tyView env view start = .ok ((element, writable), finish) →
      ∀ {initial before : LS}, GeneratedBuilderState before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerView view (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.len view) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨pair, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  have lowered := child childSource generated builder
  let value := lowerView view (lowerEnv env.mod env.vars results) before
  apply lowered.emitDef (.viewLen value.1)
  · intro active
    obtain ⟨mu, typed⟩ := outputs.view view childSource generated rfl active
    exact ⟨.data (.int .i64), by
      simp [Op.resultTy, TyEnv.viewTy, TyEnv.valTy, tyEnv, value, typed,
        pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have same : operand = value.1 := by simpa [Op.uses] using member
    subst operand
    obtain ⟨mu, typed⟩ := outputs.view view childSource generated rfl active
    exact (Array.getElem?_eq_some_iff.mp typed).1

theorem emitted_checked_view_of_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {place : Place} {element : Ty} {writable : Bool}
    {start finish : Nat} (source : Core.tyView env (.of place) start = .ok ((element, writable), finish))
    (child : ∀ {info : PlaceInfo} {start finish : Nat},
      Core.tyPlace env place start = .ok (info, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerPlace place (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerView (.of place) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨info, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have shape : ∃ element, GIR.arrayElem? info.ty = some element := by
    cases actual : info.ty <;> simp only [actual] at source
    all_goals first
      | exact ⟨_, rfl⟩
      | exact (rej_ok _ _ _ _).mp source |>.elim
  obtain ⟨actualElement, shape⟩ := shape
  have lowered := child childSource generated builder
  let value := lowerPlace place (lowerEnv env.mod env.vars results) before
  apply lowered.emitDef (.snapshot (match (generalizing := false) place with | .var _ | .global _ => .owner | _ => .borrowed) value.1)
  · intro active
    obtain ⟨mu, typed⟩ := outputs.place place childSource generated rfl active
    simp only [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed, shape,
      pure, Except.pure, bind, Except.bind]
    exact ⟨_, rfl⟩
  · intro active operand member
    have same : operand = value.1 := by simpa [Op.uses] using member
    subst operand
    obtain ⟨mu, typed⟩ := outputs.place place childSource generated rfl active
    exact (Array.getElem?_eq_some_iff.mp typed).1

theorem emitted_checked_view_val_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {expr : Expr} {element : Ty} {writable : Bool}
    {start finish : Nat} (source : Core.tyView env (.val expr) start = .ok ((element, writable), finish))
    (child : ∀ {type : Ty} {start finish : Nat},
      Core.tyExpr env expr start = .ok (type, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr expr (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerView (.val expr) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨type, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases type with
  | slice mu actualElement =>
    have lowered := child childSource generated builder
    let value := lowerExpr expr (lowerEnv env.mod env.vars results) before
    apply lowered.emitDef (.sliceView value.1)
    · intro active
      have typed := outputs.expression expr childSource generated rfl active
      exact ⟨.view mu actualElement, by
        simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed,
          pure, Except.pure, bind, Except.bind]⟩
    · intro active operand member
      have same : operand = value.1 := by simpa [Op.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp (outputs.expression expr childSource generated rfl active)).1
  | _ => exact (rej_ok _ _ _ _).mp source |>.elim

end Goose.Lower.Validation
