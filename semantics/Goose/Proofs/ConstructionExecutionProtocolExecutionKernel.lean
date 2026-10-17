import Goose.Proofs.ConstructionExecutionProtocolKernel
import Goose.Construct.Runtime
import Goose.Proofs.Exit

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

def ExecutionInvariant (predicate : ConstructionState → Prop) (state : ExecutionState) : Prop :=
  predicate state.construction

def PreservesConstructionInvariant (predicate : ConstructionState → Prop) (action : EvalM α) : Prop :=
  ∀ state, ExecutionInvariant predicate state →
    ExecutionInvariant predicate (Goose.Proofs.Exit.stepState (action state))

end Goose.Proofs.ConstructionExecutionProtocol
