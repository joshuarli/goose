import Goose.Lower.Validation.SourceReplacementWriterLedgerChildTypesStatementsLoops

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem Fragment.child_span_types {fragment child : Fragment} {env : LEnv} {before start : LS} {index : Nat}
    (row : fragment.child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) (fragment.finish env before) := by
  cases fragment with
  | expression expression =>
    cases expression with
    | lit a b => exact Fragment.expression_child_span_types (by trivial) row
    | bool a => exact Fragment.expression_child_span_types (by trivial) row
    | read a => exact Fragment.expression_child_span_types (by trivial) row
    | ref a b => exact Fragment.expression_child_span_types (by trivial) row
    | slice a b c d e => exact Fragment.expression_child_span_types (by trivial) row
    | len a => exact Fragment.expression_child_span_types (by trivial) row
    | un a b c => exact Fragment.expression_child_span_types (by trivial) row
    | bin a b c d => exact Fragment.expression_child_span_types (by trivial) row
    | cmp a b c => exact Fragment.expression_child_span_types (by trivial) row
    | and a b => exact Fragment.shortCircuit_child_span_types true row
    | or a b => exact Fragment.shortCircuit_child_span_types false row
    | not a => exact Fragment.expression_child_span_types (by trivial) row
    | conv a b c d => exact Fragment.expression_child_span_types (by trivial) row
    | call a b c => exact Fragment.expression_child_span_types (by trivial) row
    | push a b c => exact Fragment.expression_child_span_types (by trivial) row
    | pop a b => exact Fragment.expression_child_span_types (by trivial) row
    | ifE a b c => exact Fragment.ifE_child_span_types row
    | blockE a => exact Fragment.blockE_child_span_types row
    | arrLit a b => exact Fragment.expression_child_span_types (by trivial) row
    | fill a b => exact Fragment.expression_child_span_types (by trivial) row
    | structLit a b => exact Fragment.expression_child_span_types (by trivial) row
  | place place => exact Fragment.place_child_span_types row
  | view view => exact Fragment.view_child_span_types row
  | bound bound => exact Fragment.bound_child_span_types row
  | statement loop statement =>
    cases statement with
    | letS a b c => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | assign a b c => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | assignOp a b c d => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | rebind a b c => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | expr a b => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | append a b c => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | popN a b c => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | resize a b c d => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | clear a b => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | assignWhole a b c => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | ifS a b c d => exact Fragment.ifS_child_span_types row
    | «while» a b c => exact Fragment.while_child_span_types row
    | forRange a b c d e => exact Fragment.forRange_child_span_types row
    | forEach a b c d e f => exact Fragment.forEach_child_span_types row
    | ret a b => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | brk a => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | cont a => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | print a b => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | assertS a b => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | abort a b => exact Fragment.statement_ordinary_child_span_types (by trivial) row
    | exit a b => exact Fragment.statement_ordinary_child_span_types (by trivial) row
  | block loop bindings want block => exact Fragment.block_child_span_types row

#print axioms Fragment.child_span_types

end Goose.Lower.Validation.SourceReplacementWriterLedger
