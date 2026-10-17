import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem breakFrame_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (body : BreakFrameAction action) :
    BreakFrameAction (finishActivation layout activation types origin action) := by
  intro state bounded
  have checked := body state bounded
  cases evaluated : action state with
  | ok carriers middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      let pruned := { middle with activations := middle.activations.filter (fun current => current.act != activation.act) }
      have prune : BreakStackFrame middle pruned := ⟨Nat.le_refl _, rfl⟩
      have finishedFrame := breakFrame_finishChannels layout activation.channels types carriers origin
        pruned (prune.bounded (checked.bounded bounded))
      cases finished : finishChannels layout activation.channels types carriers origin pruned <;>
        simp only [finished] at finishedFrame
      all_goals change BreakStackFrame pruned _ at finishedFrame
      all_goals dsimp only [pruned] at finished
      all_goals simp only [finishActivation, evaluated, finished]
      all_goals change BreakStackFrame state _
      all_goals exact checked.trans (prune.trans finishedFrame)
  | stop reason middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      simp only [finishActivation, evaluated]
      change BreakStackFrame state middle
      exact checked
  | jump target kind middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      simp only [finishActivation, evaluated]
      change BreakStackFrame state middle
      exact checked
  | escape address carriers middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      simp only [finishActivation, evaluated]
      split
      · let pruned := { middle with activations := middle.activations.filter (fun current => current.act != activation.act) }
        have prune : BreakStackFrame middle pruned := ⟨Nat.le_refl _, rfl⟩
        have finishedFrame := breakFrame_finishChannels layout activation.channels types carriers origin
          pruned (prune.bounded (checked.bounded bounded))
        cases finished : finishChannels layout activation.channels types carriers origin pruned <;>
          simp only [finished] at finishedFrame
        all_goals change BreakStackFrame pruned _ at finishedFrame
        all_goals dsimp only [pruned] at finished
        all_goals dsimp only
        all_goals change BreakStackFrame state _
        all_goals exact checked.trans (prune.trans finishedFrame)
      · exact ⟨checked.counter, checked.stack⟩

#print axioms breakFrame_finishActivation

end Goose.Proofs.ConstructionDelivery
