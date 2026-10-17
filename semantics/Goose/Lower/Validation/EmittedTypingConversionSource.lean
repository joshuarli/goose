import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_checked_conversion_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {expr : Expr} {kind : ConvKind} {target type : Ty}
    {origin : OriginId} {start finish : Nat}
    (source : Core.tyExpr env (.conv kind target expr origin) start = .ok (type, finish))
    (child : ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
      ∀ {initial before : LS}, GeneratedBuilderState before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr expr (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.conv kind target expr origin) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨src, dst, childStart, childFinish, childSource, targetShape, _, widening⟩ :=
    tyExpr_conversion_child source
  subst target
  have lowered := child childSource generated builder
  let value := lowerExpr expr (lowerEnv env.mod env.vars results) before
  have sameState : (lowerExpr (.conv kind (.int dst) expr origin)
      (lowerEnv env.mod env.vars results) before).2 =
      (emitDef (.conv kind (intTyOf value.1 (lowerEnv env.mod env.vars results) value.2).1 dst value.1 (some origin))
        (lowerEnv env.mod env.vars results) value.2).2 := by
    simp only [lowerExpr, bind_run, intTyOf_state, value]
  rw [sameState]
  apply lowered.emitDef
  · intro active
    have typed := outputs.expression expr childSource generated rfl active
    have integerRead := intTyOf_recorded (le := lowerEnv env.mod env.vars results) typed
    have chosen : (intTyOf value.1 (lowerEnv env.mod env.vars results) value.2).1 = src :=
      congrArg Prod.fst integerRead
    rw [chosen]
    refine ⟨.data (.int dst), ?_⟩
    cases kind with
    | widen =>
      simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed, widening rfl,
        pure, Except.pure, bind, Except.bind]
    | as | asUnchecked =>
      simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed,
        pure, Except.pure, bind, Except.bind]
  · intro active operand member
    have same : operand = value.1 := by simpa [Op.uses] using member
    subst operand
    exact (Array.getElem?_eq_some_iff.mp (outputs.expression expr childSource generated rfl active)).1

end Goose.Lower.Validation
