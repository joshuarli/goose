import Goose.Lower.DemandIntegerAssignmentExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive IntegerAssignmentStatementPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | control {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ControlStatementPrefixCursor cx results source before built initial start map required runtime) :
      IntegerAssignmentStatementPrefixCursor cx results source before built initial start map required runtime
  | assignment {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : IntegerAssignmentPrefixCursor cx results source before built initial start map required runtime) :
      IntegerAssignmentStatementPrefixCursor cx results source before built initial start map required runtime

inductive IntegerAssignmentStatements : List Stmt → Prop
  | nil : IntegerAssignmentStatements []
  | clear (global : GlobalId) (origin : OriginId) {rest : List Stmt} (tail : IntegerAssignmentStatements rest) :
      IntegerAssignmentStatements (.clear (.global global) origin :: rest)
  | expression {expression : Expr} (origin : OriginId) (form : ControlPrefixExpression expression)
      {rest : List Stmt} (tail : IntegerAssignmentStatements rest) : IntegerAssignmentStatements (.expr expression origin :: rest)
  | assignment {place : Place} (form : ScalarReadPlace place) {expression : Expr} (value : IntegerControlExpression expression) (origin : OriginId)
      {rest : List Stmt} (tail : IntegerAssignmentStatements rest) :
      IntegerAssignmentStatements (.assign place expression origin :: rest)

theorem accepted_generated_integer_assignment_statements_agreement {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : IntegerAssignmentStatements statements) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements
        (@IntegerAssignmentStatementPrefixCursor cfg env cx results) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block statements := by
  induction fragment with
  | nil =>
    exact ⟨fun {state} => accepted_generated_sequence_prefix_nil selected before loop bindings want block _,
      fun {state} => accepted_generated_stopped_sequence_nil selected before loop bindings want block⟩
  | clear global origin tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.clear (.global global) origin)
        (@IntegerAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor (accepted_generated_global_clear_prefix_family selected loop global origin)
      intro statement state source before built initial start map required runtime cursor
      exact .control (.clear cursor)
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ head ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_global_clear_stopped_family selected loop global origin) ih.2⟩
  | @expression expression origin form rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.expr expression origin)
        (@IntegerAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_expression_statement_prefix selected loop _ origin _
          (accepted_generated_control_prefix_family selected loop form))
      intro statement state source before built initial start map required runtime cursor
      exact .control (.expression cursor)
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ head ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_expression_statement_stopped_family selected loop expression origin
          (accepted_generated_read_stopped_expressions selected loop form.stopped)) ih.2⟩
  | @assignment place form expression value origin rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign place expression origin)
        (@IntegerAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor (accepted_generated_integer_assignment_prefix selected loop place form expression origin
          (fun source child _ => value.integer child) (accepted_generated_control_prefix_family selected loop value.control))
      intro statement state source before built initial start map required runtime cursor
      exact .assignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ head ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_integer_assignment_stopped selected loop place form expression origin
          (fun source child _ => value.integer child) (accepted_generated_read_stopped_expressions selected loop value.control.stopped)) ih.2⟩

theorem IntegerAssignmentStatementPrefixCursor.realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : IntegerAssignmentStatementPrefixCursor cx results source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | control cursor => exact cursor.realizes
  | assignment cursor => exact cursor.realizes

theorem GeneratedSequencePrefixCursor.integer_assignment_realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {initial runtime : DemandRuntimePoint}
    (cursor : GeneratedSequencePrefixCursor (@IntegerAssignmentStatementPrefixCursor cfg env cx results)
      map required cx results before loop bindings block selected source initial runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  induction cursor with
  | head canonical owned occurrence rows coverage demanded =>
    simpa only [canonical.world] using demanded.realizes
  | tail canonical evaluated prefixSteps post demanded ih =>
    simpa only [canonical.world] using ih

#print axioms accepted_generated_integer_assignment_statements_agreement
#print axioms IntegerAssignmentStatementPrefixCursor.realizes
#print axioms GeneratedSequencePrefixCursor.integer_assignment_realizes

end Goose.Lower
