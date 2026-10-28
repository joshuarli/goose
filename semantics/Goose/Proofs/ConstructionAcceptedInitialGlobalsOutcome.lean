import Goose.Proofs.ConstructionAcceptedGlobalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

def InitialGlobalsOutcome (fuel : Nat) (config : EvalConfig) : Prop :=
  ∃ completed types live ambient regions,
    let outcome := initGlobals fuel config (List.range config.module.globals.size) .initial
    let after := Goose.Proofs.Exit.stepState outcome
    completed ≤ config.module.globals.size ∧ AcceptedWorld config completed after ambient types live regions [] ∧
    (match outcome with
     | .ok _ _ => ambient = [] ∧ completed = config.module.globals.size ∧ regions = [] ∧ FutureGlobalsClear config completed after
     | .stop stop _ => completed < config.module.globals.size ∧ runModule fuel config .initial = .stop stop after
     | .escape .. | .jump .. => False)

end Goose.Proofs.ConstructionAcceptedExecution
