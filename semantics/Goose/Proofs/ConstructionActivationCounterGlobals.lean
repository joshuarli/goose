import Goose.Proofs.ConstructionActivationCounter
import Goose.Proofs.ConstructionGhostGlobalReplay

namespace Goose.Proofs.ConstructionActivationCounterGlobals
open Goose.Construct Goose.Proofs.ConstructionActivationCounter
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay

theorem counter_initGlobals (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId)
    (initializer : ∀ global, PreservesActivationCounter (globalInitializer fuel config global)) :
    PreservesActivationCounter (initGlobals fuel config globals) := by
  induction globals with
  | nil => simpa [initGlobals] using counter_pure ()
  | cons global rest ih =>
    rw [initGlobals_step]
    exact counter_bind _ _ (initializer global) (fun _ => ih)

theorem counter_runModule (fuel : Nat) (config : EvalConfig)
    (initializer : ∀ global, PreservesActivationCounter (globalInitializer fuel config global))
    (entry : PreservesActivationCounter (afterGlobals fuel config)) :
    PreservesActivationCounter (runModule fuel config) := by
  change PreservesActivationCounter (initGlobals fuel config (List.range config.module.globals.size) >>= fun _ => afterGlobals fuel config)
  exact counter_bind _ _ (counter_initGlobals fuel config _ initializer) (fun _ => entry)

#print axioms counter_initGlobals
#print axioms counter_runModule
end Goose.Proofs.ConstructionActivationCounterGlobals
