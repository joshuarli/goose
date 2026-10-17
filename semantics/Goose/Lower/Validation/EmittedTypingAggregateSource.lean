import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.EmittedTypingAggregateCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_checked_lowerExprs_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) (exprs : List Expr) {types : List Ty}
    {start finish : Nat} (source : Core.tyStructExprs env types exprs start = .ok ((), finish))
    (children : ∀ expr ∈ exprs, ∀ {type : Ty} {start finish : Nat},
      Core.tyExpr env expr start = .ok (type, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr expr (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExprs exprs (lowerEnv env.mod env.vars results) before).2 ∧
    ((lowerExprs exprs (lowerEnv env.mod env.vars results) before).2.cur.isSome = true →
      TypedValues (lowerExprs exprs (lowerEnv env.mod env.vars results) before).2 types
        (lowerExprs exprs (lowerEnv env.mod env.vars results) before).1) := by
  induction exprs generalizing types start before with
  | nil =>
    cases types with
    | nil => exact ⟨builder, fun _ => .nil⟩
    | cons type types => exact (rej_ok _ _ _ _).mp source |>.elim
  | cons expr rest inductionHypothesis =>
    cases types with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons type types =>
      simp only [Core.tyStructExprs] at source
      obtain ⟨actual, middle, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases equal : (actual == type) = true
      · have same := eq_of_beq equal
        subst actual
        simp only [BEq.rfl, ite_true] at source
        let child := lowerExpr expr (lowerEnv env.mod env.vars results) before
        have childBuilder := children expr (by simp) childSource generated builder
        have childGenerated := generated.lowerExpr expr (show lowerExpr expr _ before = child from rfl)
        have tail := inductionHypothesis source
          (fun e member => children e (by simp [member])) childGenerated childBuilder
        refine ⟨tail.1, ?_⟩
        intro live
        have tailLive : (lowerExprs rest (lowerEnv env.mod env.vars results) child.2).2.cur.isSome = true := live
        have childLive := (dead_lowerExprs rest).live_before rfl tailLive
        have head := outputs.expression expr childSource generated
          (show lowerExpr expr _ before = child from rfl) childLive
        exact .cons ((types_lowerExprs rest _ child.2 _ _ rfl) _ _ head) (tail.2 tailLive)
      · simp [equal, chk] at source

theorem emitted_checked_arrayLiteral_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {arrayType resultType : Ty} (exprs : List Expr)
    {start finish : Nat} (source : Core.tyExpr env (.arrLit arrayType exprs) start = .ok (resultType, finish))
    (children : ∀ expr ∈ exprs, ∀ {type : Ty} {start finish : Nat},
      Core.tyExpr env expr start = .ok (type, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr expr (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.arrLit arrayType exprs) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨_, element, childStart, childFinish, shape, count, childSource⟩ := tyExpr_arrayLiteral_children source
  have lowered := emitted_checked_lowerExprs_source outputs exprs
    (tyExprsAs_structExprs childSource) children generated builder
  let values := lowerExprs exprs (lowerEnv env.mod env.vars results) before
  apply lowered.1.emitDef (.arrLit arrayType values.1)
  · intro active
    have typed := lowered.2 active
    have sameCount : values.1.length = exprs.length := by
      simpa only [List.length_replicate] using typed.length_eq.symm
    exact ⟨.data arrayType, arrayLiteral_resultTy shape (by simpa [sameCount] using count) typed.replicate⟩
  · intro active operand member
    exact (lowered.2 active).emitted_bounds operand (by simpa [Op.uses] using member)

theorem emitted_checked_structLiteral_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {structType resultType : Ty} (exprs : List Expr)
    {start finish : Nat} (source : Core.tyExpr env (.structLit structType exprs) start = .ok (resultType, finish))
    (children : ∀ expr ∈ exprs, ∀ {type : Ty} {start finish : Nat},
      Core.tyExpr env expr start = .ok (type, finish) → ∀ {initial before : LS},
      GeneratedBuilderState before → EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr expr (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.structLit structType exprs) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, definition, childSource⟩ :=
    tyExpr_structLiteral_children source
  have lowered := emitted_checked_lowerExprs_source outputs exprs childSource children generated builder
  let values := lowerExprs exprs (lowerEnv env.mod env.vars results) before
  apply lowered.1.emitDef (.structLit structType values.1)
  · intro active
    exact ⟨.data structType, structLiteral_resultTy definition (lowered.2 active)⟩
  · intro active operand member
    exact (lowered.2 active).emitted_bounds operand (by simpa [Op.uses] using member)

theorem emitted_checked_fill_source {env : Core.TEnv} {results : List Ty}
    (outputs : EmittedSourceResults env results) {arrayType resultType : Ty} (expr : Expr)
    {start finish : Nat} (source : Core.tyExpr env (.fill arrayType expr) start = .ok (resultType, finish))
    (child : ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
      ∀ {initial before : LS}, GeneratedBuilderState before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial before →
      EmittedBuilder (lowerEnv env.mod env.vars results) initial
        (lowerExpr expr (lowerEnv env.mod env.vars results) before).2)
    {initial before : LS} (generated : GeneratedBuilderState before)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initial before) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.fill arrayType expr) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨_, element, size, childStart, childFinish, shape, childSource⟩ := tyExpr_fill_child source
  subst arrayType
  rw [shape]
  have lowered := child childSource generated builder
  let value := lowerExpr expr (lowerEnv env.mod env.vars results) before
  apply lowered.emitDef (.arrFill (.arr element size) value.1)
  · intro active
    have typed := outputs.expression expr childSource generated rfl active
    exact ⟨.data (.arr element size), by
      simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, value, typed,
        pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have same : operand = value.1 := by simpa [Op.uses] using member
    subst operand
    exact (Array.getElem?_eq_some_iff.mp (outputs.expression expr childSource generated rfl active)).1

end Goose.Lower.Validation
