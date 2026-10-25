import Goose.Proofs.ConstructionExecutionProtocolReservationFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

def ReservationProgressPreserves (before after : DestinationProgress) : Prop :=
  ReservationStableProgress before →
    ReservationStableProgress after ∧
      ∀ count selected, after = .exiting count selected →
        ∃ oldCount oldSelected, before = .exiting oldCount oldSelected

theorem ReservationProgressPreserves.refl (progress : DestinationProgress) :
    ReservationProgressPreserves progress progress :=
  fun stable => ⟨stable, fun count selected same => ⟨count, selected, same⟩⟩

theorem ReservationProgressPreserves.suspended (count before after : Nat) :
    ReservationProgressPreserves (.suspended count before) (.suspended count after) := by
  intro stable
  simp [ReservationStableProgress] at stable

theorem ReservationProgressPreserves.exiting (count before after : Nat) :
    ReservationProgressPreserves (.exiting count before) (.exiting count after) := by
  intro _
  exact ⟨trivial, fun _ _ _ => ⟨count, before, rfl⟩⟩

theorem reservationMetadataFrame_replace_progress (state : ConstructionState) (id : DestinationId)
    (before after : PendingDestination) (present : state.destinations[id]? = some before)
    (progress : ReservationProgressPreserves before.progress after.progress) :
    ReservationMetadataFrame state { state with destinations := state.destinations.set! id after } := by
  have update := reservationMetadataFrame_replace_events state id before after state.storage [] present
    (Nat.le_refl _) (by intro queried different; rfl)
  simp only [List.append_nil] at update
  apply update
  intro stable
  obtain ⟨afterStable, prior⟩ := progress stable
  exact ⟨afterStable, fun count selected exiting =>
    let ⟨oldCount, oldSelected, beforeExiting⟩ := prior count selected exiting
    ⟨oldCount, oldSelected, beforeExiting, by simp⟩⟩

end Goose.Proofs.ConstructionExecutionProtocol
