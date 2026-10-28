import Goose.Proofs.ConstructionActivationCounter
import Goose.Proofs.ConstructionGhostGlobalReplay

namespace Goose.Proofs.ConstructionActivationCounterGlobals
open Goose.Construct Goose.Proofs.ConstructionActivationCounter
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay

theorem counter_globalInitializer (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (previous : EvaluationPreservesActivationCounter fuel config) :
    PreservesActivationCounter (globalInitializer fuel config global) := by
  cases found : config.module.globals[global]? with
  | none => simpa [globalInitializer, found] using counter_fault Goose.Core.FaultKind.unbound
  | some descriptor =>
    simp only [globalInitializer, found]
    apply counter_bind
    · exact counter_freshAct
    · intro act
      split
      · apply counter_bind
        · apply counter_materializeProducer
          exact previous.value ⟨0, act, #[], [], []⟩ descriptor.init
        · intro materialized
          cases materialized with
          | none =>
            apply counter_bind
            · apply counter_constructLocal
              intro destination
              exact previous.build ⟨0, act, #[], [], []⟩ destination descriptor.init
            · intro carrier
              apply counter_bind
              · exact counter_stateQuery _ (Goose.Proofs.ExitExecution.stateQuery_carrierValue carrier)
              · intro value
                exact counter_bindRoot (.global global) value
          | some values =>
            apply counter_bind
            · exact counter_materializedDestination _ _ _ _ _ _ _
            · intro destination
              apply counter_bind
              · exact counter_publishCarriers _ _
              · intro ignored
                apply counter_bind
                · exact counter_pure _
                · intro carrier
                  apply counter_bind
                  · exact counter_stateQuery _ (Goose.Proofs.ExitExecution.stateQuery_carrierValue carrier)
                  · intro value
                    exact counter_bindRoot (.global global) value
      · apply counter_bind
        · exact previous.value ⟨0, act, #[], [], []⟩ descriptor.init
        · intro value
          exact counter_bindRoot (.global global) value

#print axioms counter_globalInitializer
theorem counter_fixedGlobal (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (previous : EvaluationPreservesActivationCounter fuel config)
    (fixed : ∀ descriptor, config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = false) :
    PreservesActivationCounter (globalInitializer fuel config global) :=
  counter_globalInitializer fuel config global previous

#print axioms counter_fixedGlobal
theorem counter_initGlobals (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId)
    (initializer : ∀ global, PreservesActivationCounter (globalInitializer fuel config global)) :
    PreservesActivationCounter (initGlobals fuel config globals) := by
  induction globals with
  | nil => simpa [initGlobals] using counter_pure ()
  | cons global rest ih =>
    rw [initGlobals_step]
    exact counter_bind _ _ (initializer global) (fun _ => ih)

theorem counter_globals (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId)
    (previous : EvaluationPreservesActivationCounter fuel config) :
    PreservesActivationCounter (initGlobals fuel config globals) :=
  counter_initGlobals fuel config globals (fun global => counter_globalInitializer fuel config global previous)

#print axioms counter_globals
theorem counter_fixedGlobals (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId)
    (previous : EvaluationPreservesActivationCounter fuel config)
    (fixed : ∀ (global : Goose.Core.GlobalId) (descriptor : Global), config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = false) :
    PreservesActivationCounter (initGlobals fuel config globals) :=
  counter_globals fuel config globals previous

#print axioms counter_fixedGlobals
theorem counter_runModule (fuel : Nat) (config : EvalConfig)
    (initializer : ∀ global, PreservesActivationCounter (globalInitializer fuel config global))
    (entry : PreservesActivationCounter (afterGlobals fuel config)) :
    PreservesActivationCounter (runModule fuel config) := by
  change PreservesActivationCounter (initGlobals fuel config (List.range config.module.globals.size) >>= fun _ => afterGlobals fuel config)
  exact counter_bind _ _ (counter_initGlobals fuel config _ initializer) (fun _ => entry)

#print axioms counter_initGlobals
#print axioms counter_runModule
end Goose.Proofs.ConstructionActivationCounterGlobals
