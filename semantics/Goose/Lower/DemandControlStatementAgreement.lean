import Goose.Lower.DemandClearStoppedFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem ScalarPrefixExpression.stopped {expression : Expr} (form : ScalarPrefixExpression expression) :
    ReadStoppedExpression expression := by
  induction form with
  | globalRead global => exact .read (.global global)
  | slotRead slot => exact .read (.slot slot)
  | literal type number => exact .control (.comparison (.numeric (.unary (.literal type number))))
  | boolean value => exact .control (.comparison (.numeric (.unary (.boolean value))))
  | not child ih => exact .not ih
  | unary operation origin child ih => exact .unary operation origin ih
  | convert kind target origin child ih => exact .convert kind target origin ih
  | binary operation origin first second firstIH secondIH => exact .binary operation origin firstIH secondIH
  | compare operation first second firstIH secondIH => exact .compare operation firstIH secondIH

theorem ControlPrefixExpression.stopped {expression : Expr} (form : ControlPrefixExpression expression) :
    ReadStoppedExpression expression := by
  induction form with
  | scalar form => exact form.stopped
  | not child ih => exact .not ih
  | unary operation origin child ih => exact .unary operation origin ih
  | convert kind target origin child ih => exact .convert kind target origin ih
  | binary operation origin first second firstIH secondIH => exact .binary operation origin firstIH secondIH
  | compare operation first second firstIH secondIH => exact .compare operation firstIH secondIH
  | and first second firstIH secondIH => exact .and firstIH secondIH
  | or first second firstIH secondIH => exact .or firstIH secondIH

theorem ControlStatements.stopped {statements : List Stmt} (fragment : ControlStatements statements) :
    StoppedControlStatements statements := by
  induction fragment with
  | nil => exact .nil
  | clear global origin tail ih => exact .clear global origin ih
  | expression origin form tail ih => exact .expression origin form.stopped ih

theorem accepted_generated_control_statements_agreement {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : ControlStatements statements) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements
        (@ControlStatementPrefixCursor cfg env cx results) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block statements := by
  constructor
  · intro state
    exact accepted_generated_control_statements_prefix selected before loop bindings want block fragment
  · intro state
    exact accepted_generated_control_statements_stopped selected before loop bindings want block fragment.stopped

#print axioms accepted_generated_control_statements_agreement

end Goose.Lower
