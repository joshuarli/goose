import Goose.Lower.DemandScalarAssignmentStopped
import Goose.Lower.DemandReadStoppedFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_read_assignment_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (place : Place) (destination : ScalarReadPlace place)
    (read : Place) (readable : ScalarReadPlace read) (origin : OriginId)
    (target : ∀ {state after : St} (source : StmtSource cfg env (.assign place (.read read) origin) state)
      (child : ExprSource cfg env (.read read) after), source.AssignmentValueAt child → child.ty.refTarget = true) :
    GeneratedStatementPrefixFamily cx results selected loop (.assign place (.read read) origin)
      (@ScalarAssignmentPrefixCursor cfg env cx results) :=
  accepted_generated_scalar_assignment_prefix selected loop place destination (.read read) origin target
    (accepted_generated_control_progress_prefix_family selected loop readable.control)

theorem accepted_generated_read_assignment_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (place : Place) (destination : ScalarReadPlace place)
    (read : Place) (readable : ScalarReadPlace read) (origin : OriginId)
    (target : ∀ {state after : St} (source : StmtSource cfg env (.assign place (.read read) origin) state)
      (child : ExprSource cfg env (.read read) after), source.AssignmentValueAt child → child.ty.refTarget = true) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.assign place (.read read) origin) :=
  accepted_generated_scalar_assignment_stopped selected loop place destination (.read read) origin target
    (accepted_generated_read_stopped_family selected loop readable)

#print axioms accepted_generated_read_assignment_prefix
#print axioms accepted_generated_read_assignment_stopped

end Goose.Lower
