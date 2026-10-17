import Goose.Proofs.OwnershipEvaluationActions
import Goose.Proofs.OwnershipAmbientContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

theorem ownershipAmbient_timeout (state : ExecutionState) (ambient : OwnershipAmbient)
    (shape : OwnershipResultShape α) (valid : OwnershipAmbientInvariant state.construction ambient) :
    OwnershipAmbientOutcome ambient shape (timeout state) := valid.structural

theorem evaluation_zero_ownership (config : EvalConfig) (shape : OwnershipResultShape α)
    (action : EvalM α) (actual : OwnershipEvaluationAction 0 config shape action)
    (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipAmbientInvariant state.construction ambient) :
    OwnershipAmbientOutcome ambient shape (action state) := by
  cases actual <;>
    simpa only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
      buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
      execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
      execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
      OwnershipAmbientOutcome] using valid.structural

end Goose.Proofs.ConstructionExecutionOwnership
