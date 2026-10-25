import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesOwners

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem breakFrame_protectDestination (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId)
    (action : EvalM α) (body : BreakFrameAction action) :
    BreakFrameAction (protectDestination origin id action) := by
  intro state bounded
  have checked := body state bounded
  cases evaluated : action state with
  | ok value middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      simp only [protectDestination, evaluated]
      change BreakStackFrame state middle
      exact checked
  | stop reason middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      simp only [protectDestination, evaluated]
      change BreakStackFrame state middle
      exact checked
  | escape address carriers middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      have cleanupFrame := breakFrame_cleanupReceivingDestination origin id carriers middle (checked.bounded bounded)
      cases finished : cleanupReceivingDestination origin id carriers middle <;>
        simp only [finished] at cleanupFrame
      all_goals change BreakStackFrame middle _ at cleanupFrame
      all_goals simp only [protectDestination, evaluated, finished]
      all_goals change BreakStackFrame state _
      all_goals exact checked.trans cleanupFrame
  | jump target kind middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      cases kind with
      | breakValue carriers =>
          have cleanupFrame := breakFrame_cleanupReceivingDestination origin id carriers middle (checked.bounded bounded)
          cases finished : cleanupReceivingDestination origin id carriers middle <;>
            simp only [finished] at cleanupFrame
          all_goals change BreakStackFrame middle _ at cleanupFrame
          all_goals simp only [protectDestination, evaluated, finished]
          all_goals change BreakStackFrame state _
          all_goals exact checked.trans cleanupFrame
      | continueLoop =>
          have cleanupFrame := breakFrame_cleanupReceivingDestination origin id [] middle (checked.bounded bounded)
          cases finished : cleanupReceivingDestination origin id [] middle <;>
            simp only [finished] at cleanupFrame
          all_goals change BreakStackFrame middle _ at cleanupFrame
          all_goals simp only [protectDestination, evaluated, finished]
          all_goals change BreakStackFrame state _
          all_goals exact checked.trans cleanupFrame

#print axioms breakFrame_protectDestination

end Goose.Proofs.ConstructionDelivery
