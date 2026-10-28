import Goose.Proofs.ConstructionExitDirectByteLoop

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecutionChecks

def recursiveDirectContinuation : Option (List Carrier × DestinationProgress) :=
  let config : EvalConfig := ⟨.release, recursiveDestinations⟩
  let checkpoint := Goose.Proofs.Exit.stepState (runModule 28 config .initial)
  match targetActivation config 0 checkpoint, recursiveByteExit with
  | .ok target _, .escape escapeTarget [.completed 1] escaped =>
    if escapeTarget.activation != target.act then none else
    match escaped.construction.exitReservations[0]? with
    | some ExitReservation.released =>
      match finishChannels config.layout target.channels [array] [.completed 1] 0 escaped with
      | .ok () finished =>
        match finished.construction.destinations[1]? with
        | some row => some ([.completed 1], row.progress)
        | none => none
      | _ => none
    | _ => none
  | _, _ => none

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in
theorem recursive_direct_cleanup_and_finish :
    recursiveDirectContinuation = some ([.completed 1], .built 1) := by
  cbv

#print axioms recursive_direct_cleanup_and_finish

end Goose.Proofs.ConstructionAcceptedExecution
