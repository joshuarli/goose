import Goose.Lower.TypedEntry
import Goose.Lower.TypedExpressionFamily
import Goose.Lower.TypedIf
import Goose.Lower.TypedWhile
import Goose.Lower.FinalStatements
import Goose.Lower.MutationStatements
import Goose.Lower.CompoundStatements
import Goose.Lower.ResizeStatements
import Goose.Lower.AppendStatements
import Goose.Lower.TypedLists
import Goose.Lower.TypedTransfers
import Goose.Lower.PrintStatements
import Goose.Lower.WholeReplacementStatements
import Goose.Lower.EachFamily
import Goose.Lower.RangeFamily

namespace Goose.Lower

open Goose.Core Goose.GIR

structure TypedStatementFamily (n : Nat) (cfg : Cfg) : Prop where
  expressions : TypedExpressionFamily n cfg
  statement : ∀ results loop stmt, TypedStatementLoopSimulation n cfg results loop stmt
  statements : ∀ results loop stmts, TypedStatementsLoopSimulation n cfg results loop stmts
  block : ∀ results loop pre pre' want block,
    TypedBlockLoopSimulation n cfg results loop pre pre' want block
  whileLoop : ∀ results condition body origin, TypedWhileSimulation n cfg results condition body origin

theorem typedStatementFamily_zero (cfg : Cfg) : TypedStatementFamily 0 cfg := by
  exact {
    expressions := typedExpressionFamily_zero cfg,
    statement := typedStatementLoopSimulation_zero cfg,
    statements := typedStatementsLoopSimulation_zero cfg,
    block := typedBlockLoopSimulation_zero cfg,
    whileLoop := typedWhileSimulation_zero cfg }

private theorem statementFamily_succ {n : Nat} {cfg : Cfg}
    (earlier : ∀ k, k ≤ n → TypedStatementFamily k cfg)
    (shapes : ∀ results place, PlaceOwnerShape cfg results place) :
    ∀ results loop stmt, TypedStatementLoopSimulation (n + 1) cfg results loop stmt := by
  let smaller := earlier n (Nat.le_refl n)
  intro results loop stmt
  cases stmt with
  | letS x expr origin => exact typedStatementLoopSimulation_let (smaller.expressions.expr results expr)
  | rebind x expr origin => exact typedStatementLoopSimulation_rebind (smaller.expressions.expr results expr)
  | assign place expr origin =>
    exact typedStatementLoopSimulation_assign (smaller.expressions.place results place)
      (smaller.expressions.expr results expr)
  | assignOp op place expr origin =>
    exact typedStatementLoopSimulation_assignOp (smaller.expressions.place results place)
      (smaller.expressions.expr results expr)
  | expr expr origin => exact typedStatementLoopSimulation_expr (smaller.expressions.expr results expr)
  | append owner view origin =>
    exact typedStatementLoopSimulation_append (smaller.expressions.place results owner)
      (smaller.expressions.view results view)
  | popN owner count origin =>
    exact typedStatementLoopSimulation_popN (smaller.expressions.place results owner)
      (smaller.expressions.expr results count)
  | clear owner origin => exact typedStatementLoopSimulation_clear (smaller.expressions.place results owner)
  | resize owner size fill origin =>
    apply typedStatementLoopSimulation_resize (smaller.expressions.place results owner)
      (smaller.expressions.expr results size)
    cases fill with
    | none => trivial
    | some expr => exact smaller.expressions.expr results expr
  | assignWhole owner replacement origin =>
    exact typedStatementLoopSimulation_assignWhole (smaller.expressions.place results owner)
      (smaller.expressions.expr results replacement)
  | ifS condition yes no origin =>
    cases no with
    | none =>
      exact typedStatementLoopSimulation_if_none (smaller.expressions.expr results condition)
        (smaller.block results loop [] [] false yes)
    | some no =>
      exact typedStatementLoopSimulation_if_some (smaller.expressions.expr results condition)
        (smaller.block results loop [] [] false yes) (smaller.block results loop [] [] false no)
  | «while» condition body origin =>
    exact typedStatementLoopSimulation_while (smaller.whileLoop results condition body origin)
  | forRange x lo hi body origin =>
    exact typedStatementLoopSimulation_range (smaller.expressions.expr results lo)
      (smaller.expressions.expr results hi)
      (fun fuel bound context pre pre' => (earlier fuel (by omega)).block results
        (some context) pre pre' false body) loop
  | forEach x index view byRef body origin =>
    exact typedStatementLoopSimulation_each (n + 1) cfg results
      (fun fuel bound => (earlier fuel (by omega)).expressions)
      (fun fuel bound context pre pre' body => (earlier fuel (by omega)).block results
        (some context) pre pre' false body) (shapes results) loop x index view byRef body origin
  | ret value origin =>
    cases value with
    | none => exact typedStatementLoopSimulation_return_none (n + 1) cfg results loop origin
    | some expr => exact typedStatementLoopSimulation_return_some (smaller.expressions.expr results expr)
  | brk origin => exact typedStatementLoopSimulation_break (n + 1) cfg results loop origin
  | cont origin => exact typedStatementLoopSimulation_continue (n + 1) cfg results loop origin
  | print args origin =>
    cases n with
    | zero => exact typedStatementLoopSimulation_print_one cfg results loop args origin
    | succ k => exact typedStatementLoopSimulation_print_succ ((earlier k (by omega)).expressions.expr results)
  | assertS expr origin => exact typedStatementLoopSimulation_assert (smaller.expressions.expr results expr)
  | abort message origin => exact typedStatementLoopSimulation_abort message origin
  | exit expr origin => exact typedStatementLoopSimulation_exit (smaller.expressions.expr results expr)

private theorem typedStatementFamily_succ {n : Nat} {cfg : Cfg}
    (earlier : ∀ k, k ≤ n → TypedStatementFamily k cfg)
    (shapes : ∀ results place, PlaceOwnerShape cfg results place) :
    TypedStatementFamily (n + 1) cfg := by
  let smaller := earlier n (Nat.le_refl n)
  refine {
    expressions := typedExpressionFamily_succ smaller.expressions
      (fun fuel bound results pre pre' want body =>
        (earlier fuel bound).block results none pre pre' want body),
    statement := statementFamily_succ earlier shapes,
    statements := ?_, block := ?_, whileLoop := ?_ }
  · intro results loop stmts
    cases stmts with
    | nil => exact typedStatementsLoopSimulation_nil (n + 1) cfg results loop
    | cons stmt rest =>
      exact typedStatementsLoopSimulation_cons n cfg results loop stmt rest
        (smaller.statement results loop stmt) (smaller.statements results loop rest)
  · intro results loop pre pre' want block
    cases block with
    | mk scope stmts value =>
      apply typedBlockLoopSimulation_succ
      · exact smaller.statements results loop stmts
      · cases value with
        | none => trivial
        | some expr => exact smaller.expressions.expr results expr
  · intro results condition body origin
    exact typedWhileSimulation_succ (smaller.expressions.expr results condition)
      (fun context => smaller.block results (some context) [] [] false body)
      (smaller.whileLoop results condition body origin)

private theorem typedStatementFamily_of_ownerShapes (cfg : Cfg)
    (shapes : ∀ results place, PlaceOwnerShape cfg results place) :
    ∀ n, TypedStatementFamily n cfg := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n earlier =>
    cases n with
    | zero => exact typedStatementFamily_zero cfg
    | succ n =>
      exact typedStatementFamily_succ
        (fun fuel bound => earlier fuel (Nat.lt_succ_of_le bound)) shapes

theorem typedStatementFamily_all (cfg : Cfg) : ∀ n, TypedStatementFamily n cfg :=
  typedStatementFamily_of_ownerShapes cfg (placeOwnerShape_generated cfg)

private theorem typedModule_simulation_positive {cfg : Cfg} (n : Nat)
    (accepted : Core.validate cfg.mod = .ok ()) :
    EventualM (Core.runModule (n + 1) cfg)
      (fun fuel => GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩) St.initial := by
  have family := typedStatementFamily_all cfg
  exact typedModule_simulation_succ n accepted
    (fun _ global _ => (family (n + 1)).expressions.expr [global.ty] global.init)
    (fun _ impl _ _ => (family n).block impl.results.toList none (callPre impl) [] false impl.body)

theorem typedModule_simulation {cfg : Cfg} (fuel : Nat)
    (accepted : Core.validate cfg.mod = .ok ()) :
    EventualM (Core.runModule fuel cfg)
      (fun targetFuel => GIR.runModule targetFuel ⟨cfg.profile, lower cfg.mod⟩) St.initial := by
  have next := typedModule_simulation_positive fuel accepted
  have mono := Goose.Proofs.Fuel.MonoM.runModule fuel (fuel + 1) (Nat.le_succ fuel) cfg St.initial
  constructor
  · intro value after completed
    exact next.1 value after (mono.1 value after completed)
  · intro stop after completed final
    have completedNext := (mono.2 stop after completed).resolve_left (by
      cases stop <;> simp_all [Goose.Proofs.Fuel.isTimeout, IsFinal])
    exact next.2 stop after completedNext final

end Goose.Lower
