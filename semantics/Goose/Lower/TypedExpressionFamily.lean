import Goose.Lower.TypedCall
import Goose.Lower.TypedControlExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR

structure TypedExpressionFamily (n : Nat) (cfg : Cfg) : Prop where
  expr : ∀ results expr, TypedExprClaim n cfg results expr
  place : ∀ results place, TypedPlaceClaim n cfg results place
  view : ∀ results view, TypedViewClaim n cfg results view
  bound : ∀ results bound, TypedBoundClaim n cfg results bound
  arg : ∀ results arg, TypedArgClaim n cfg results arg
  args : ∀ results args, TypedArgsClaim n cfg results args
  exprs : ∀ results exprs, TypedExprsClaim n cfg results exprs
  blockValue : ∀ results block, TypedBlockValueClaim n cfg results block

theorem typedExpressionFamily_zero (cfg : Cfg) : TypedExpressionFamily 0 cfg := by
  exact {
    expr := typedExprClaim_zero cfg,
    place := typedPlaceClaim_zero cfg,
    view := typedViewClaim_zero cfg,
    bound := typedBoundClaim_zero cfg,
    arg := typedArgClaim_zero cfg,
    args := fun results args => typedArgsClaim args (fun arg _ => typedArgClaim_zero cfg results arg),
    exprs := fun results exprs => typedExprsClaim exprs (fun expr _ => typedExprClaim_zero cfg results expr),
    blockValue := typedBlockValueClaim_zero cfg }

theorem typedExpressionFamily_succ {n : Nat} {cfg : Cfg}
    (smaller : TypedExpressionFamily n cfg)
    (blocks : ∀ k, k ≤ n → ∀ results pre pre' want block,
      TypedBlockLoopSimulation k cfg results none pre pre' want block) :
    TypedExpressionFamily (n + 1) cfg := by
  have expr : ∀ results expr, TypedExprClaim (n + 1) cfg results expr := by
    intro results expr
    cases expr with
    | lit ty value => exact typedExprClaim_lit (n + 1) cfg results ty value
    | bool value => exact typedExprClaim_bool (n + 1) cfg results value
    | read place => exact typedExprClaim_read (smaller.place results place)
    | ref mutability place => exact typedExprClaim_ref (smaller.place results place) mutability
    | slice mutability view low high origin =>
      exact typedExprClaim_slice (smaller.view results view) (smaller.bound results low)
        (smaller.bound results high) mutability origin
    | len view => exact typedExprClaim_len (smaller.view results view)
    | un op expr origin => exact typedExprClaim_un (smaller.expr results expr) op origin
    | bin op left right origin =>
      exact typedExprClaim_bin (smaller.expr results left) (smaller.expr results right) op origin
    | cmp op left right =>
      exact typedExprClaim_cmp (smaller.expr results left) (smaller.expr results right) op
    | and left right => exact typedExprClaim_and (smaller.expr results left) (smaller.expr results right)
    | or left right => exact typedExprClaim_or (smaller.expr results left) (smaller.expr results right)
    | not expr => exact typedExprClaim_not (smaller.expr results expr)
    | conv kind target expr origin =>
      exact typedExprClaim_conv (smaller.expr results expr) kind target origin
    | call context args origin =>
      cases n with
      | zero => exact typedExprClaim_call_one cfg results context args origin
      | succ k =>
        apply typedExprClaim_call_of_blocks (smaller.args results args)
        intro ctx impl hcontext himpl pre
        exact blocks k (by omega) impl.results.toList (callPre impl) pre false impl.body
    | push owner expr origin =>
      exact typedExprClaim_push (smaller.place results owner) (smaller.expr results expr) origin
    | pop owner origin => exact typedExprClaim_pop (smaller.place results owner) origin
    | ifE cond thenBlock elseBlock =>
      exact typedExprClaim_ifE (smaller.expr results cond) (smaller.blockValue results thenBlock)
        (smaller.blockValue results elseBlock)
    | blockE block => exact typedExprClaim_blockE (smaller.blockValue results block)
    | arrLit target exprs => exact typedExprClaim_arrLit (smaller.exprs results exprs) target
    | fill target expr => exact typedExprClaim_fill (smaller.expr results expr) target
    | structLit target exprs => exact typedExprClaim_structLit (smaller.exprs results exprs) target
  have place : ∀ results place, TypedPlaceClaim (n + 1) cfg results place := by
    intro results place
    cases place with
    | var id => exact typedPlaceClaim_var (n + 1) cfg results id
    | global id => exact typedPlaceClaim_global (n + 1) cfg results id
    | deref expr => exact typedPlaceClaim_deref (smaller.expr results expr)
    | elem view index origin =>
      exact typedPlaceClaim_elem (smaller.view results view) (smaller.expr results index) origin
    | field place index => exact typedPlaceClaim_field (smaller.place results place) index
  have view : ∀ results view, TypedViewClaim (n + 1) cfg results view := by
    intro results view
    cases view with
    | of place => exact typedViewClaim_of (smaller.place results place)
    | val expr => exact typedViewClaim_val (smaller.expr results expr)
  have bound : ∀ results bound, TypedBoundClaim (n + 1) cfg results bound := by
    intro results bound
    cases bound with
    | omitted => exact typedBoundClaim_omitted (n + 1) cfg results
    | expr expr => exact typedBoundClaim_expr (smaller.expr results expr)
    | fromEnd expr => exact typedBoundClaim_fromEnd (smaller.expr results expr)
  have arg : ∀ results arg, TypedArgClaim (n + 1) cfg results arg := by
    intro results arg
    cases arg with
    | byVal expr => exact typedArgClaim_byVal (smaller.expr results expr)
    | byRef mutability place => exact typedArgClaim_byRef (smaller.place results place) mutability
  exact {
    expr := expr, place := place, view := view, bound := bound, arg := arg,
    args := fun results args => typedArgsClaim args (fun arg' _ => arg results arg'),
    exprs := fun results exprs => typedExprsClaim exprs (fun expr' _ => expr results expr'),
    blockValue := fun results block =>
      typedBlockValueClaim_succ (blocks n (Nat.le_refl n) results [] [] true block) }

example (cfg : Cfg) : TypedExpressionFamily 1 cfg := by
  apply typedExpressionFamily_succ (typedExpressionFamily_zero cfg)
  intro k hk results pre pre' want block
  have hk0 : k = 0 := by omega
  subst k
  exact typedBlockLoopSimulation_zero cfg results none pre pre' want block

end Goose.Lower
