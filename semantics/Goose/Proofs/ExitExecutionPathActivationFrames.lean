import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionUnwind

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem finishActivation_after_action_frame (layout : LayoutEnv) (activation : RuntimeActivation)
    (resultTypes : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (initial : ExecutionState) :
    let before := Goose.Proofs.Exit.stepState (action initial)
    let final := Goose.Proofs.Exit.stepState (finishActivation layout activation resultTypes origin action initial)
    final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  cases evaluated : action initial with
  | stop reason before | jump target kind before =>
      simp only [finishActivation, evaluated, Goose.Proofs.Exit.stepState, and_self]
  | ok carriers before =>
      have stdout := Goose.Proofs.Exit.runtime_finish_channels_frames_output layout activation.channels resultTypes
        carriers origin { before with activations := before.activations.filter (fun current => current.act != activation.act) }
      have objects := Goose.Proofs.Exit.runtime_finish_channels_frames_objects layout activation.channels resultTypes
        carriers origin { before with activations := before.activations.filter (fun current => current.act != activation.act) }
      simp only [finishActivation, evaluated]
      cases finished : finishChannels layout activation.channels resultTypes carriers origin
          { before with activations := before.activations.filter (fun current => current.act != activation.act) } <;>
        simpa only [finished, Goose.Proofs.Exit.stepState] using And.intro stdout objects
  | escape address carriers before =>
      by_cases catches : address.activation == activation.act
      · have same : address.activation = activation.act := by simpa using catches
        have dispatched : action initial = .escape ⟨activation.act, address.target⟩ carriers before := by
          cases address with
          | mk current target =>
              simp only at same ⊢
              subst current
              exact evaluated
        have stdout := Goose.Proofs.Exit.runtime_activation_landing_frames_output layout activation address.target
          resultTypes origin action initial before carriers dispatched
        have objects := Goose.Proofs.Exit.runtime_activation_landing_frames_objects layout activation address.target
          resultTypes origin action initial before carriers dispatched
        exact ⟨stdout, objects⟩
      · simp [finishActivation, evaluated, catches, Goose.Proofs.Exit.stepState]

theorem enterActivation_after_body_frame (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (implementation : Impl) (initial : ExecutionState)
    (lookup : config.module.impls[activation.implementation]? = some implementation) :
    let before := Goose.Proofs.Exit.stepState (execActivationBody fuel config activation pre body initial)
    let final := Goose.Proofs.Exit.stepState (enterActivation (fuel + 1) config activation pre body origin initial)
    final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  simpa only [enterActivation, lookup] using finishActivation_after_action_frame config.layout activation
    (implementation.results.toList.map (·.ty)) origin (execActivationBody fuel config activation pre body) initial

theorem ExitReached.activation_escape_frame {rootFuel fuel : Nat} {config : EvalConfig}
    {activation : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {body : Block}
    {origin : Goose.Core.OriginId} {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (.activation (fuel + 1) activation pre body origin) initial)
    (escaped : enterActivation (fuel + 1) config activation pre body origin initial = .escape address carriers final) :
    ∃ implementation before,
      config.module.impls[activation.implementation]? = some implementation ∧
      ExitReached rootFuel config (.activationBody fuel activation pre body) initial ∧
      execActivationBody fuel config activation pre body initial = .escape address carriers before ∧
      address.activation ≠ activation.act ∧
      final = { before with activations := before.activations.filter (fun current => current.act != activation.act) } ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects := by
  obtain ⟨implementation, before, lookup, evaluated, different, released⟩ :=
    enterActivation_escape_origin fuel config activation pre body origin initial final address carriers escaped
  refine ⟨implementation, before, lookup, .call reached (.activationBody fuel activation pre body origin initial implementation lookup),
    evaluated, different, released, ?_, ?_⟩ <;> rw [released] <;> rfl

#print axioms enterActivation_after_body_frame
#print axioms ExitReached.activation_escape_frame

end Goose.Proofs.ExitExecution
