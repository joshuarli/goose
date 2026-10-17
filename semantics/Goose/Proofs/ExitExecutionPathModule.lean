import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionInvocationValuesNative

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem moduleInvocation_escape_inv (fuel : Nat) (config : EvalConfig)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : runModule fuel config initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitCallSite config (.module fuel) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  simp only [runModule] at escaped
  cases globalsDone : initGlobals fuel config (List.range config.module.globals.size) initial with
  | stop reason after | jump target kind after => simp only [bind, globalsDone] at escaped; cases escaped
  | escape target payload after =>
      simp only [bind, globalsDone] at escaped
      cases escaped
      exact ⟨Unit, .globals fuel (List.range config.module.globals.size), initial, .moduleGlobals fuel initial, globalsDone⟩
  | ok ignored globalsState =>
      cases ignored
      simp only [bind, globalsDone] at escaped
      cases lookup : getImplementation config config.module.entry globalsState with
      | stop reason after | jump target kind after => simp only [lookup] at escaped; cases escaped
      | escape target payload after =>
          exact False.elim (valueNeverEscapes_getImplementation _ _ _ _ _ _ lookup)
      | ok pair implementationState =>
          rcases pair with ⟨id, implementation⟩
          simp only [lookup] at escaped
          cases receiving : channelsFor config.layout 0 implementation.results.toList 0 implementationState with
          | stop reason after | jump target kind after => simp only [receiving] at escaped; cases escaped
          | escape target payload after =>
              exact False.elim (valueNeverEscapes_channelsFor _ _ _ _ _ _ _ _ receiving)
          | ok channels entryState =>
              simp only [receiving] at escaped
              cases invoked : invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 entryState with
              | stop reason after | jump target kind after => simp only [invoked] at escaped; cases escaped
              | escape target payload after =>
                  simp only [invoked] at escaped
                  cases escaped
                  exact ⟨List Carrier, .call fuel ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0, entryState,
                    .moduleEntry fuel initial globalsState implementationState entryState id implementation channels
                      globalsDone lookup receiving, invoked⟩
              | ok returned after =>
                  simp only [invoked] at escaped
                  exact False.elim (valueNeverEscapes_publishCarriers 0 returned _ _ _ _ escaped)

#print axioms moduleInvocation_escape_inv
end Goose.Proofs.ExitExecution
