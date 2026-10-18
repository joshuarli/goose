import Goose.Proofs.ExitExecutionPathUnwindFrames
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumpsExtension

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem ownerEscape_escape_or_stop {α : Type} (snapshot : Option PendingDestination) (destination : Nat)
    (address : ExitAddress) (carriers : List Carrier) (before : ExecutionState) :
    let outcome : ExecutionStep α := match snapshot with
      | none => .escape address carriers before
      | some parent => match restoreCompletedOwner parent destination
          (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) before with
        | .ok () final => .escape address carriers final
        | .stop reason final => .stop reason final
        | .escape target payload final => .escape target payload final
        | .jump target kind final => .jump target kind final
    (∃ final, outcome = .escape address carriers final) ∨
      ∃ reason final, outcome = .stop reason final := by
  cases snapshot with
  | none => exact Or.inl ⟨before, rfl⟩
  | some parent =>
      cases restored : restoreCompletedOwner parent destination
          (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) before with
      | ok value final => cases value; exact Or.inl ⟨final, by simp only [restored]⟩
      | stop reason final => exact Or.inr ⟨reason, final, by simp only [restored]⟩
      | escape target payload final =>
          exact False.elim (statementNeverEscapes_restoreCompletedOwner _ _ _ _ _ _ _ restored)
      | jump target kind final =>
          exact False.elim (Goose.Proofs.ConstructionDelivery.neverJumps_restoreCompletedOwner _ _ _ _ _ _ _ restored)

theorem StatementInvocationUnwinds.escape_or_stop {config : EvalConfig}
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    {edge : StatementInvocationEdge config parent initial child prepared} {outcome : ExecutionStep α}
    (unwinds : StatementInvocationUnwinds config address carriers before edge outcome) :
    (∃ final, outcome = .escape address carriers final) ∨
      ∃ reason final, outcome = .stop reason final := by
  cases unwinds <;> subst_vars
  all_goals first
    | exact Or.inl ⟨_, rfl⟩
    | exact ownerEscape_escape_or_stop _ _ _ _ _

theorem StatementInvocationEdge.escape_after_child {config : EvalConfig}
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (edge : StatementInvocationEdge config parent initial child prepared)
    (escaped : child.action config prepared = .escape address carriers before) :
    (∃ final, parent.action config initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) ∨
    (∃ reason final, parent.action config initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) := by
  have unwinds := edge.propagates config address carriers escaped
  have frame := unwinds.frame
  rcases unwinds.escape_or_stop with ⟨final, outcome⟩ | ⟨reason, final, outcome⟩
  · rw [outcome] at frame
    exact Or.inl ⟨final, outcome, frame⟩
  · rw [outcome] at frame
    exact Or.inr ⟨reason, final, outcome, frame⟩

#print axioms StatementInvocationUnwinds.escape_or_stop
#print axioms StatementInvocationEdge.escape_after_child

end Goose.Proofs.ExitExecution
