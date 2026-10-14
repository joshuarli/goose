import Goose.Construct.Eval
import Goose.Construct.Validate
import Goose.Proofs.Construct

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct

def EventPrefix (before after : List Goose.Core.ConstructionEvent) : Prop :=
  ∃ suffix, after = before ++ suffix

theorem eventPrefix_refl (events : List Goose.Core.ConstructionEvent) : EventPrefix events events :=
  ⟨[], by simp⟩

theorem eventPrefix_trans (before middle after : List Goose.Core.ConstructionEvent)
    (first : EventPrefix before middle) (second : EventPrefix middle after) :
    EventPrefix before after := by
  obtain ⟨left, rfl⟩ := first
  obtain ⟨right, rfl⟩ := second
  exact ⟨left ++ right, by simp [List.append_assoc]⟩

theorem rejected_publication_preserves_execution (state : ExecutionState)
    (destinations : List Goose.Core.DestinationId) (kind : ConstructionFault)
    (origin : Goose.Core.OriginId)
    (rejected : preflightPublication state.construction destinations = .error kind) :
    liftConstruction origin (publishOperation destinations) state =
      .stop (match kind with
        | .capacity => .abort .capacity origin
        | .storage => .fault .danglingRoot
        | .destination => .fault .unbound
        | .ownership | .protocol => .fault .flow) state := by
  rw [liftConstruction, Goose.Proofs.Construct.publication_rejection_keeps_prefix
    state.construction destinations kind rejected]
  cases kind <;> rfl

theorem terminal_receiver_scope_activation (layout : LayoutEnv) (activation : RuntimeActivation)
    (resultTypes : List Ty) (scope scopeInst : Nat) (origin : Goose.Core.OriginId)
    (destination : Goose.Core.DestinationId) (action : EvalM (List Carrier))
    (state terminal : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : action state = .stop reason terminal) :
    finishActivation layout activation resultTypes origin
      (withScope activation scope scopeInst (protectDestination origin destination action)) state =
        .stop reason terminal := by
  simp [finishActivation, withScope, protectDestination, stopped]

end Goose.Proofs.ConstructionExecution
