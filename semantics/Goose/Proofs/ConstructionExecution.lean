import Goose.Construct.Eval
import Goose.Construct.Validate
import Goose.Proofs.Construct
import Goose.Proofs.ExitExecution

set_option Elab.async false

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

def KeepsEventPrefix (action : EvalM α) : Prop :=
  ∀ state, EventPrefix state.construction.events
    (Goose.Proofs.Exit.stepState (action state)).construction.events

theorem stateQuery_keepsEventPrefix (action : EvalM α)
    (query : Goose.Proofs.ExitExecution.StateQuery action) : KeepsEventPrefix action := by
  intro state
  rw [query state]
  exact eventPrefix_refl _

theorem keepsEventPrefix_pure (value : α) : KeepsEventPrefix (pure value) :=
  stateQuery_keepsEventPrefix _ (Goose.Proofs.ExitExecution.stateQuery_pure value)

theorem keepsEventPrefix_stop (reason : Goose.Core.Stop) : KeepsEventPrefix (EvalM.stop (α := α) reason) :=
  stateQuery_keepsEventPrefix _ (Goose.Proofs.ExitExecution.stateQuery_stop reason)

theorem keepsEventPrefix_get : KeepsEventPrefix EvalM.get :=
  stateQuery_keepsEventPrefix _ Goose.Proofs.ExitExecution.stateQuery_get

theorem keepsEventPrefix_bind (action : EvalM α) (next : α → EvalM β)
    (first : KeepsEventPrefix action) (remaining : ∀ value, KeepsEventPrefix (next value)) :
    KeepsEventPrefix (action >>= next) := by
  intro state
  have keptPrefix := first state
  cases result : action state with
  | ok value final =>
      simp only [bind, result]
      exact eventPrefix_trans _ _ _
        (by simpa only [result, Goose.Proofs.Exit.stepState] using keptPrefix)
        (remaining value final)
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using keptPrefix
  | escape address carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using keptPrefix
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using keptPrefix

theorem keepsEventPrefix_listMapM (action : α → EvalM β) (items : List α)
    (kept : ∀ item, KeepsEventPrefix (action item)) : KeepsEventPrefix (items.mapM action) := by
  induction items with
  | nil => exact keepsEventPrefix_pure []
  | cons head tail remaining =>
      rw [List.mapM_cons]
      apply keepsEventPrefix_bind
      · exact kept head
      · intro value
        apply keepsEventPrefix_bind
        · exact remaining
        · intro _; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_listForIn (action : α → β → EvalM (ForInStep β)) (items : List α)
    (initial : β) (kept : ∀ item current, KeepsEventPrefix (action item current)) :
    KeepsEventPrefix (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact keepsEventPrefix_pure _
  | cons head tail remaining =>
      simp only [List.forIn_cons]
      apply keepsEventPrefix_bind
      · exact kept head initial
      · intro step
        cases step with
        | done value => exact keepsEventPrefix_pure _
        | yield value => exact remaining value

theorem keepsEventPrefix_arrayForIn (action : α → β → EvalM (ForInStep β)) (items : Array α)
    (initial : β) (kept : ∀ item current, KeepsEventPrefix (action item current)) :
    KeepsEventPrefix (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact keepsEventPrefix_listForIn action items.toList initial kept

theorem keepsEventPrefix_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (kept : ∀ item current, KeepsEventPrefix (action item current)) :
    KeepsEventPrefix (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact keepsEventPrefix_listForIn action _ initial kept

theorem wholeRun_terminal_skips_continuation (fuel : Nat) (config : EvalConfig)
    (initial terminal : ExecutionState) (reason : Goose.Core.Stop) (next : Unit → EvalM α)
    (stopped : runModule fuel config initial = .stop reason terminal) :
    (runModule fuel config >>= next) initial = .stop reason terminal := by
  simp only [bind, stopped]

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
