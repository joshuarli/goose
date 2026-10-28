import Goose.Proofs.ConstructionActivationCounterTheorem
import Goose.Proofs.ConstructionGhostGlobalReplay

namespace Goose.Proofs.ConstructionActivationCounterGlobalHistory
open Goose.Construct Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ConstructionActivationCounterEvaluation
open Goose.Proofs.ConstructionActivationCounterTheorem Goose.Proofs.ConstructionGhostGlobalStep
open Goose.Proofs.ConstructionActivationCounterGlobals

theorem globalInitializer_nextAct_strict (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (before : ExecutionState) (descriptor : Global) (found : config.module.globals[global]? = some descriptor) :
    before.nextAct < (Goose.Proofs.Exit.stepState (globalInitializer fuel config global before)).nextAct := by
  have strict := freshAct_bind_strict (globalInitializerTail fuel config global descriptor)
    (fun act => counter_globalInitializerTail fuel config global descriptor act (evaluation_preservesActivationCounter fuel config)) before
  simp only [globalInitializer, found]
  change before.nextAct < (Goose.Proofs.Exit.stepState ((freshAct >>= globalInitializerTail fuel config global descriptor) before)).nextAct
  exact strict

#print axioms globalInitializer_nextAct_strict
end Goose.Proofs.ConstructionActivationCounterGlobalHistory
