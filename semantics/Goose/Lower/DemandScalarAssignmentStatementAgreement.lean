import Goose.Lower.DemandScalarAssignmentExpressions
import Goose.Lower.DemandReadAssignment
import Goose.Lower.DemandScalarClear
import Goose.Lower.DemandFieldAssignmentStopped
import Goose.Lower.DemandIndexAssignmentStopped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive ScalarAssignmentStatementPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | control {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ControlStatementPrefixCursor cx results source before built initial start map required runtime) :
      ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime
  | scalarClear {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarClearPrefixCursor cx source before built initial start map required runtime) :
      ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime
  | fieldAssignment {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : FieldAssignmentPrefixCursor cx results source before built initial start map required runtime) :
      ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime
  | indexAssignment {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : IndexAssignmentPrefixCursor cx results source before built initial start map required runtime) :
      ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime
  | assignment {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarAssignmentPrefixCursor cx results source before built initial start map required runtime) :
      ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime

inductive ScalarAssignmentStatements (cfg : Cfg) (env : Env) : List Stmt → Prop
  | nil : ScalarAssignmentStatements cfg env []
  | clear (global : GlobalId) (origin : OriginId) {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.clear (.global global) origin :: rest)
  | localClear (slot : VarId) (origin : OriginId) {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.clear (.var slot) origin :: rest)
  | expression {expression : Expr} (origin : OriginId) (form : ControlPrefixExpression expression)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) : ScalarAssignmentStatements cfg env (.expr expression origin :: rest)
  | assignment {place : Place} (form : ScalarReadPlace place) {expression : Expr} (value : ScalarControlExpression expression) (origin : OriginId)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.assign place expression origin :: rest)
  | indexAssignment {owner : Place} (form : ScalarReadPlace owner) {index : Expr} (indexForm : ControlPrefixExpression index)
      (indexOrigin : OriginId) {expression : Expr} (value : ScalarControlExpression expression) (origin : OriginId)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.assign (.elem (.of owner) index indexOrigin) expression origin :: rest)
  | fieldIndexAssignment {owner : Place} (field : Nat) (form : ScalarReadPlace owner) {index : Expr}
      (indexForm : ControlPrefixExpression index) (indexOrigin : OriginId) {expression : Expr}
      (value : ScalarControlExpression expression) (origin : OriginId)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.assign (.elem (.of (.field owner field)) index indexOrigin) expression origin :: rest)
  | fieldAssignment {owner : Place} (index : Nat) (form : ScalarReadPlace owner) {expression : Expr}
      (value : ScalarControlExpression expression) (origin : OriginId)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.assign (.field owner index) expression origin :: rest)
  | fieldIndexReadAssignment {owner read : Place} (field : Nat) (form : ScalarReadPlace owner) {index : Expr}
      (indexForm : ControlPrefixExpression index) (indexOrigin : OriginId) (readable : ScalarReadPlace read)
      (origin : OriginId) (target : ∀ {state after : St}
        (source : StmtSource cfg env (.assign (.elem (.of (.field owner field)) index indexOrigin) (.read read) origin) state)
        (child : ExprSource cfg env (.read read) after), source.AssignmentValueAt child → child.ty.refTarget = true)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.assign (.elem (.of (.field owner field)) index indexOrigin) (.read read) origin :: rest)
  | indexReadAssignment {owner read : Place} (form : ScalarReadPlace owner) {index : Expr}
      (indexForm : ControlPrefixExpression index) (indexOrigin : OriginId) (readable : ScalarReadPlace read)
      (origin : OriginId) (target : ∀ {state after : St}
        (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) (.read read) origin) state)
        (child : ExprSource cfg env (.read read) after), source.AssignmentValueAt child → child.ty.refTarget = true)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.assign (.elem (.of owner) index indexOrigin) (.read read) origin :: rest)
  | fieldReadAssignment {owner read : Place} (index : Nat) (destination : ScalarReadPlace owner) (readable : ScalarReadPlace read)
      (origin : OriginId) (target : ∀ {state after : St}
        (source : StmtSource cfg env (.assign (.field owner index) (.read read) origin) state)
        (child : ExprSource cfg env (.read read) after), source.AssignmentValueAt child → child.ty.refTarget = true)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.assign (.field owner index) (.read read) origin :: rest)
  | readAssignment {place read : Place} (destination : ScalarReadPlace place) (readable : ScalarReadPlace read)
      (origin : OriginId) (target : ∀ {state after : St}
        (source : StmtSource cfg env (.assign place (.read read) origin) state)
        (child : ExprSource cfg env (.read read) after), source.AssignmentValueAt child → child.ty.refTarget = true)
      {rest : List Stmt} (tail : ScalarAssignmentStatements cfg env rest) :
      ScalarAssignmentStatements cfg env (.assign place (.read read) origin :: rest)

theorem accepted_generated_scalar_assignment_statements_prepend {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements rest : List Stmt} (fragment : ScalarAssignmentStatements cfg env statements)
    (cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (convert : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime →
        cursor source before built initial start map required runtime)
    (tailFamily : GeneratedSequencePrefixFamily cx results selected before loop bindings want block rest cursor ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block rest) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block (statements ++ rest) cursor ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block (statements ++ rest) := by
  induction fragment with
  | nil => simpa using tailFamily
  | clear global origin tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.clear (.global global) origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor (accepted_generated_global_clear_prefix_family selected loop global origin)
      intro statement state source before built initial start map required runtime cursor
      exact .control (.clear cursor)
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_global_clear_stopped_family selected loop global origin) ih.2⟩
  | localClear slot origin tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.clear (.var slot) origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor (accepted_generated_scalar_clear_prefix_family selected loop (.slot slot) origin)
      intro statement state source before built initial start map required runtime cursor
      exact .scalarClear cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_scalar_clear_stopped_family selected loop (.slot slot) origin) ih.2⟩
  | @expression expression origin form rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.expr expression origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_expression_statement_prefix selected loop _ origin _
          (accepted_generated_control_progress_prefix_family selected loop form))
      intro statement state source before built initial start map required runtime cursor
      exact .control (.expression cursor)
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_expression_statement_stopped_family selected loop expression origin
          (accepted_generated_read_stopped_expressions selected loop form.stopped)) ih.2⟩
  | @assignment place form expression value origin rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign place expression origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor (accepted_generated_scalar_assignment_prefix selected loop place form expression origin
          (fun source child _ => by
            rcases value.scalar child with boolean | ⟨type, integer⟩
            · simp [boolean, Ty.refTarget]
            · simp [integer, Ty.refTarget]) (accepted_generated_control_prefix_family selected loop value.control))
      intro statement state source before built initial start map required runtime cursor
      exact .assignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_scalar_assignment_stopped selected loop place form expression origin
          (fun source child _ => by
            rcases value.scalar child with boolean | ⟨type, integer⟩
            · simp [boolean, Ty.refTarget]
            · simp [integer, Ty.refTarget]) (accepted_generated_read_stopped_expressions selected loop value.control.stopped)) ih.2⟩

  | @indexAssignment owner form index indexForm indexOrigin expression value origin rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign (.elem (.of owner) index indexOrigin) expression origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_index_assignment_prefix selected loop owner (.scalar form) index expression indexOrigin origin
          (fun source child _ => by
            rcases value.scalar child with boolean | ⟨type, integer⟩
            · simp [boolean, Ty.refTarget]
            · simp [integer, Ty.refTarget]) (accepted_generated_control_prefix_family selected loop indexForm)
          (accepted_generated_control_prefix_family selected loop value.control))
      intro statement state source before built initial start map required runtime cursor
      exact .indexAssignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_index_assignment_stopped selected loop owner (.scalar form) index expression indexOrigin origin
          (fun source child _ => by
            rcases value.scalar child with boolean | ⟨type, integer⟩
            · simp [boolean, Ty.refTarget]
            · simp [integer, Ty.refTarget]) (accepted_generated_read_stopped_expressions selected loop indexForm.stopped)
          (accepted_generated_read_stopped_expressions selected loop value.control.stopped)) ih.2⟩

  | @fieldIndexAssignment owner field form index indexForm indexOrigin expression value origin rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign (.elem (.of (.field owner field)) index indexOrigin) expression origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_index_assignment_prefix selected loop (.field owner field) (.field field form) index expression indexOrigin origin
          (fun source child _ => by
            rcases value.scalar child with boolean | ⟨type, integer⟩
            · simp [boolean, Ty.refTarget]
            · simp [integer, Ty.refTarget]) (accepted_generated_control_prefix_family selected loop indexForm)
          (accepted_generated_control_prefix_family selected loop value.control))
      intro statement state source before built initial start map required runtime cursor
      exact .indexAssignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_index_assignment_stopped selected loop (.field owner field) (.field field form) index expression indexOrigin origin
          (fun source child _ => by
            rcases value.scalar child with boolean | ⟨type, integer⟩
            · simp [boolean, Ty.refTarget]
            · simp [integer, Ty.refTarget]) (accepted_generated_read_stopped_expressions selected loop indexForm.stopped)
          (accepted_generated_read_stopped_expressions selected loop value.control.stopped)) ih.2⟩

  | @fieldAssignment owner index form expression value origin rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign (.field owner index) expression origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor (accepted_generated_field_assignment_prefix selected loop owner index form expression origin
          (fun source child _ => by
            rcases value.scalar child with boolean | ⟨type, integer⟩
            · simp [boolean, Ty.refTarget]
            · simp [integer, Ty.refTarget]) (accepted_generated_control_prefix_family selected loop value.control))
      intro statement state source before built initial start map required runtime cursor
      exact .fieldAssignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_field_assignment_stopped selected loop owner index form expression origin
          (fun source child _ => by
            rcases value.scalar child with boolean | ⟨type, integer⟩
            · simp [boolean, Ty.refTarget]
            · simp [integer, Ty.refTarget]) (accepted_generated_read_stopped_expressions selected loop value.control.stopped)) ih.2⟩

  | @indexReadAssignment owner read form index indexForm indexOrigin readable origin target rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign (.elem (.of owner) index indexOrigin) (.read read) origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_index_assignment_prefix selected loop owner (.scalar form) index (.read read) indexOrigin origin target
          (accepted_generated_control_prefix_family selected loop indexForm) (accepted_generated_read_prefix_family selected loop readable))
      intro statement state source before built initial start map required runtime cursor
      exact .indexAssignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_index_assignment_stopped selected loop owner (.scalar form) index (.read read) indexOrigin origin target
          (accepted_generated_read_stopped_expressions selected loop indexForm.stopped)
          (accepted_generated_read_stopped_family selected loop readable)) ih.2⟩

  | @fieldIndexReadAssignment owner read field form index indexForm indexOrigin readable origin target rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign (.elem (.of (.field owner field)) index indexOrigin) (.read read) origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_index_assignment_prefix selected loop (.field owner field) (.field field form) index (.read read) indexOrigin origin target
          (accepted_generated_control_prefix_family selected loop indexForm) (accepted_generated_read_prefix_family selected loop readable))
      intro statement state source before built initial start map required runtime cursor
      exact .indexAssignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_index_assignment_stopped selected loop (.field owner field) (.field field form) index (.read read) indexOrigin origin target
          (accepted_generated_read_stopped_expressions selected loop indexForm.stopped)
          (accepted_generated_read_stopped_family selected loop readable)) ih.2⟩

  | @fieldReadAssignment owner read index destination readable origin target rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign (.field owner index) (.read read) origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_field_assignment_prefix selected loop owner index destination (.read read) origin target
          (accepted_generated_read_prefix_family selected loop readable))
      intro statement state source before built initial start map required runtime cursor
      exact .fieldAssignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_field_assignment_stopped selected loop owner index destination (.read read) origin target
          (accepted_generated_read_stopped_family selected loop readable)) ih.2⟩

  | @readAssignment place read destination readable origin target rest tail ih =>
    have head : GeneratedStatementPrefixFamily cx results selected loop (.assign place (.read read) origin)
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) := by
      apply GeneratedStatementPrefixFamily.mapCursor
        (accepted_generated_read_assignment_prefix selected loop place destination read readable origin target)
      intro statement state source before built initial start map required runtime cursor
      exact .assignment cursor
    exact ⟨fun {state} => accepted_generated_sequence_prefix_cons selected before loop bindings want block _ (GeneratedStatementPrefixFamily.mapCursor head convert) ih.1,
      fun {state} => accepted_generated_stopped_sequence_cons selected before loop bindings want block
        (accepted_generated_read_assignment_stopped selected loop place destination read readable origin target) ih.2⟩

theorem accepted_generated_scalar_assignment_statements_agreement {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : ScalarAssignmentStatements cfg env statements) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block statements := by
  have empty : GeneratedSequencePrefixFamily cx results selected before loop bindings want block []
        (@ScalarAssignmentStatementPrefixCursor cfg env cx results) ∧
      GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block [] :=
    ⟨fun {state} => accepted_generated_sequence_prefix_nil selected before loop bindings want block _,
      fun {state} => accepted_generated_stopped_sequence_nil selected before loop bindings want block⟩
  simpa using accepted_generated_scalar_assignment_statements_prepend selected before loop bindings want block fragment _ (by
    intro statement state source before built initial start map required runtime cursor
    exact cursor) empty

theorem ScalarAssignmentStatementPrefixCursor.realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ScalarAssignmentStatementPrefixCursor cx results source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | control cursor => exact cursor.realizes
  | scalarClear cursor =>
    cases cursor with
    | clear demanded => cases demanded with
      | atFrame frame progress => exact frame.operands
  | indexAssignment cursor => exact cursor.realizes
  | fieldAssignment cursor => exact cursor.realizes
  | assignment cursor => exact cursor.realizes

theorem GeneratedSequencePrefixCursor.scalar_assignment_realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {initial runtime : DemandRuntimePoint}
    (cursor : GeneratedSequencePrefixCursor (@ScalarAssignmentStatementPrefixCursor cfg env cx results)
      map required cx results before loop bindings block selected source initial runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  induction cursor with
  | head canonical owned occurrence rows coverage demanded =>
    simpa only [canonical.world] using demanded.realizes
  | tail canonical evaluated prefixSteps post demanded ih =>
    simpa only [canonical.world] using ih

#print axioms accepted_generated_scalar_assignment_statements_agreement
#print axioms ScalarAssignmentStatementPrefixCursor.realizes
#print axioms GeneratedSequencePrefixCursor.scalar_assignment_realizes

end Goose.Lower
