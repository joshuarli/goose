import Goose.Proofs.ExitExecutionPathActivationFrames
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntime
import Goose.Proofs.ExitExecutionCleanupStorageFinish

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private def activationBodyHasParent (rootFuel : Nat) (config : EvalConfig)
    (context : List ExitLexicalFrame) : {α : Type} → ExitInvocation α → ExecutionState → Prop
  | _, .activationBody fuel activation pre body, initial =>
      ∃ origin implementation outer,
        ExitContextReached rootFuel config outer (.activation (fuel + 1) activation pre body origin) initial ∧
        context = .handler activation (implementation.results.toList.map (·.ty)) origin :: outer ∧
        config.module.impls[activation.implementation]? = some implementation
  | _, _, _ => True

private theorem reached_activationBody_hasParent {rootFuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {α : Type} {invocation : ExitInvocation α} {initial : ExecutionState}
    (reached : ExitContextReached rootFuel config context invocation initial) :
    activationBodyHasParent rootFuel config context invocation initial := by
  cases reached with
  | initial => trivial
  | call callerReached site frames =>
      cases site
      all_goals try trivial
      case activationBody =>
        dsimp only [ExitCallSite.frames, ExitInvocation.frames] at frames
        obtain ⟨frameImplementation, frameLookup, rfl⟩ := frames
        exact ⟨_, frameImplementation, _, callerReached, rfl, frameLookup⟩
      case values edge => cases edge <;> trivial
      case producer edge =>
        cases edge with
        | produce receiving body => cases body <;> trivial
        | build renewed body => cases body <;> trivial
        | elementBuild => trivial
        | elementValue => trivial
      case statements edge => cases edge <;> trivial

theorem ExitContextReached.activationBody_parent {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {activation : RuntimeActivation}
    {pre : List (Goose.Core.VarId × Value)} {body : Block} {initial : ExecutionState}
    (reached : ExitContextReached rootFuel config context (.activationBody fuel activation pre body) initial) :
    ∃ origin implementation outer,
      ExitContextReached rootFuel config outer (.activation (fuel + 1) activation pre body origin) initial ∧
      context = .handler activation (implementation.results.toList.map (·.ty)) origin :: outer ∧
      config.module.impls[activation.implementation]? = some implementation := by
  exact reached_activationBody_hasParent reached

theorem enterActivation_escape_dispatch (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (implementation : Impl) (initial before : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (lookup : config.module.impls[activation.implementation]? = some implementation)
    (evaluated : execActivationBody fuel config activation pre body initial = .escape address carriers before) :
    enterActivation (fuel + 1) config activation pre body origin initial =
      if address.activation == activation.act then
        match finishChannels config.layout activation.channels (implementation.results.toList.map (·.ty)) carriers origin
            { before with activations := before.activations.filter (fun current => current.act != activation.act) } with
        | .ok () final => .ok carriers final
        | .stop reason final => .stop reason final
        | .escape target payload final => .escape target payload final
        | .jump target kind final => .jump target kind final
      else .escape address carriers
        { before with activations := before.activations.filter (fun current => current.act != activation.act) } := by
  simp only [enterActivation, lookup, finishActivation, evaluated]
  rfl

theorem enterActivation_catch_or_stop (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (implementation : Impl) (initial before : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (lookup : config.module.impls[activation.implementation]? = some implementation)
    (evaluated : execActivationBody fuel config activation pre body initial = .escape address carriers before)
    (catches : address.activation = activation.act) :
    (∃ final, enterActivation (fuel + 1) config activation pre body origin initial = .ok carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) ∨
    (∃ reason final, enterActivation (fuel + 1) config activation pre body origin initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) := by
  have dispatch := enterActivation_escape_dispatch fuel config activation pre body origin implementation initial before
    address carriers lookup evaluated
  simp only [catches, beq_self_eq_true, ite_true] at dispatch
  have frame := enterActivation_after_body_frame fuel config activation pre body origin implementation initial lookup
  rw [evaluated] at frame
  cases finished : finishChannels config.layout activation.channels (implementation.results.toList.map (·.ty)) carriers origin
      { before with activations := before.activations.filter (fun current => current.act != activation.act) } with
  | ok value final =>
      cases value
      simp only [finished] at dispatch
      rw [dispatch] at frame
      exact Or.inl ⟨final, dispatch, frame⟩
  | stop reason final =>
      simp only [finished] at dispatch
      rw [dispatch] at frame
      exact Or.inr ⟨reason, final, dispatch, frame⟩
  | escape target payload final =>
      exact False.elim (finishChannels_no_escape _ _ _ _ _ _ _ _ _ finished)
  | jump target kind final =>
      exact False.elim (Goose.Proofs.ConstructionDelivery.neverJumps_finishChannels _ _ _ _ _ _ _ _ _ finished)

theorem enterActivation_after_body_storage (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (implementation : Impl) (initial : ExecutionState)
    (lookup : config.module.impls[activation.implementation]? = some implementation) :
    ∃ changes, CleanupStorageTrace changes
      (Goose.Proofs.Exit.stepState (execActivationBody fuel config activation pre body initial)).construction.storage
      (Goose.Proofs.Exit.stepState (enterActivation (fuel + 1) config activation pre body origin initial)).construction.storage := by
  simpa only [enterActivation, lookup] using finishActivation_after_action_storage config.layout activation
    (implementation.results.toList.map (·.ty)) origin (execActivationBody fuel config activation pre body) initial

theorem ExitContextReached.activationBody_catch {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {activation : RuntimeActivation}
    {pre : List (Goose.Core.VarId × Value)} {body : Block} {initial before : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitContextReached rootFuel config context (.activationBody fuel activation pre body) initial)
    (escaped : execActivationBody fuel config activation pre body initial = .escape address carriers before)
    (catches : address.activation = activation.act) :
    ∃ origin implementation outer,
      ExitContextReached rootFuel config outer (.activation (fuel + 1) activation pre body origin) initial ∧
      context = .handler activation (implementation.results.toList.map (·.ty)) origin :: outer ∧
      config.module.impls[activation.implementation]? = some implementation ∧
      ((∃ final changes,
        enterActivation (fuel + 1) config activation pre body origin initial = .ok carriers final ∧
        final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
        CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
      (∃ reason final changes,
        enterActivation (fuel + 1) config activation pre body origin initial = .stop reason final ∧
        final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
        CleanupStorageTrace changes before.construction.storage final.construction.storage)) := by
  obtain ⟨origin, implementation, outer, parent, frames, lookup⟩ := reached.activationBody_parent
  have result := enterActivation_catch_or_stop fuel config activation pre body origin implementation initial before
    address carriers lookup escaped catches
  obtain ⟨changes, storage⟩ := enterActivation_after_body_storage fuel config activation pre body origin implementation initial lookup
  rw [escaped] at storage
  refine ⟨origin, implementation, outer, parent, frames, lookup, ?_⟩
  rcases result with ⟨final, returned, stdout, objects⟩ | ⟨reason, final, stopped, stdout, objects⟩
  · rw [returned] at storage
    exact Or.inl ⟨final, changes, returned, stdout, objects, storage⟩
  · rw [stopped] at storage
    exact Or.inr ⟨reason, final, changes, stopped, stdout, objects, storage⟩

theorem enterActivation_escape_or_catch (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (implementation : Impl) (initial before : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (lookup : config.module.impls[activation.implementation]? = some implementation)
    (evaluated : execActivationBody fuel config activation pre body initial = .escape address carriers before) :
    (∃ final, enterActivation (fuel + 1) config activation pre body origin initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) ∨
    (∃ reason final, enterActivation (fuel + 1) config activation pre body origin initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) ∨
    (∃ final, address.activation = activation.act ∧
      enterActivation (fuel + 1) config activation pre body origin initial = .ok carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) := by
  by_cases catches : address.activation = activation.act
  · rcases enterActivation_catch_or_stop fuel config activation pre body origin implementation initial before
      address carriers lookup evaluated catches with ⟨final, returned, stdout, objects⟩ | ⟨reason, final, stopped, stdout, objects⟩
    · exact Or.inr (Or.inr ⟨final, catches, returned, stdout, objects⟩)
    · exact Or.inr (Or.inl ⟨reason, final, stopped, stdout, objects⟩)
  · have miss : (address.activation == activation.act) = false := by simp [catches]
    have actual := enterActivation_escape_dispatch fuel config activation pre body origin implementation initial before
      address carriers lookup evaluated
    simp only [miss, Bool.false_eq_true, ↓reduceIte] at actual
    exact Or.inl ⟨_, actual, rfl, rfl⟩

#print axioms enterActivation_escape_or_catch

#print axioms enterActivation_after_body_storage
#print axioms ExitContextReached.activationBody_catch

#print axioms ExitContextReached.activationBody_parent
#print axioms enterActivation_escape_dispatch
#print axioms enterActivation_catch_or_stop

end Goose.Proofs.ExitExecution
