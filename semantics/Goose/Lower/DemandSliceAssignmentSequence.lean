import Goose.Lower.DemandSliceAssignmentTyping
import Goose.Lower.DemandStoppedSequenceFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive SliceAssignmentCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | assignment {state : St} {reference : Expr} {mutability : Mutability} {global : GlobalId}
      {intType : IntTy} {number : Int} {sliceOrigin origin : OriginId}
      {source : StmtSource cfg env (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (inner : SliceAssignmentInterior source cx results before map runtime) :
      SliceAssignmentCursor cx results source before built initial start map required runtime

theorem SliceAssignmentCursor.realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : SliceAssignmentCursor cx results source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | assignment inner => exact inner.realizes

theorem SliceAssignmentCursor.nonterminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : SliceAssignmentCursor cx results source before built initial start map required runtime) :
    (∃ id op, instAt cx.fn runtime.point = some (.def id op)) ∨
      ∃ effect, instAt cx.fn runtime.point = some (.eff effect) := by
  cases cursor with
  | assignment inner => exact inner.nonterminal

theorem accepted_generated_slice_assignment_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (reference : Expr) (mutability : Mutability) (global : GlobalId)
    (intType : IntTy) (number : Int) (sliceOrigin origin : OriginId) :
    GeneratedStatementPrefixFamily cx results selected loop (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin)
      (@SliceAssignmentCursor cfg env cx results) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  obtain ⟨ty, slice⟩ := source.sliceAssignment_reference
  have progress := accepted_generated_slice_assignment_prefix source slice selected owned occurrence rows coverage admitted bounded realized input extended steps
  refine ⟨progress.sourceOwner, progress.coverage, ?_⟩
  cases progress.progress with
  | interior cursor => exact .interior (.assignment cursor)
  | complete count executed residual evaluated post => exact .complete count executed residual evaluated post

inductive SliceAssignmentStatements : List Stmt → Prop
  | nil : SliceAssignmentStatements []
  | assignment (reference : Expr) (mutability : Mutability) (global : GlobalId) (intType : IntTy) (number : Int)
      (sliceOrigin origin : OriginId) {rest : List Stmt} (tail : SliceAssignmentStatements rest) :
      SliceAssignmentStatements (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin :: rest)

theorem accepted_generated_slice_assignment_sequence_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : SliceAssignmentStatements statements) :
    GeneratedSequencePrefixFamily cx results selected before loop bindings want block statements
      (@SliceAssignmentCursor cfg env cx results) := by
  induction fragment with
  | nil => exact accepted_generated_sequence_prefix_nil selected before loop bindings want block _
  | assignment reference mutability global intType number sliceOrigin origin tail ih =>
    exact accepted_generated_sequence_prefix_cons selected before loop bindings want block _
      (accepted_generated_slice_assignment_prefix_family selected loop reference mutability global intType number sliceOrigin origin) ih

theorem accepted_generated_slice_assignment_sequence_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : SliceAssignmentStatements statements) :
    GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block statements := by
  induction fragment with
  | nil => exact accepted_generated_stopped_sequence_nil selected before loop bindings want block
  | assignment reference mutability global intType number sliceOrigin origin tail ih =>
    exact accepted_generated_stopped_sequence_cons selected before loop bindings want block
      (accepted_generated_slice_assignment_accepted_stopped_family selected loop reference mutability global intType number sliceOrigin origin) ih

#print axioms accepted_generated_slice_assignment_sequence_prefix
#print axioms accepted_generated_slice_assignment_sequence_stopped

#print axioms SliceAssignmentCursor.realizes
#print axioms SliceAssignmentCursor.nonterminal
#print axioms accepted_generated_slice_assignment_prefix_family
end Goose.Lower
