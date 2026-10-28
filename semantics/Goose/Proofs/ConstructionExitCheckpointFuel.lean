import Goose.Proofs.ConstructionExitCheckpointRead

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem recursive_checkpoint_restart_is_not_continuation :
    (Goose.Proofs.Exit.stepState (runModule 200 recursiveCheckpointConfig recursiveDirectCheckpoint)).nextAct = 8 ∧
    (Goose.Proofs.Exit.stepState (runModule 200 recursiveCheckpointConfig .initial)).nextAct = 4 ∧
    (Goose.Proofs.Exit.stepState (runModule 200 recursiveCheckpointConfig recursiveDirectCheckpoint)).nextAct ≠
      (Goose.Proofs.Exit.stepState (runModule 200 recursiveCheckpointConfig .initial)).nextAct := by
  constructor
  · cbv
  · constructor
    · cbv
    · have restarted : (Goose.Proofs.Exit.stepState (runModule 200 recursiveCheckpointConfig recursiveDirectCheckpoint)).nextAct = 8 := by cbv
      have original : (Goose.Proofs.Exit.stepState (runModule 200 recursiveCheckpointConfig .initial)).nextAct = 4 := by cbv
      rw [restarted, original]
      decide

#print axioms recursive_checkpoint_restart_is_not_continuation

end Goose.Proofs.ConstructionAcceptedExecution
