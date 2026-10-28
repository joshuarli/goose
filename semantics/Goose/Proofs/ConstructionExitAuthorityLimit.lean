import Goose.Proofs.ConstructionExitLandingOldRows

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem receivingProtection_receiver_only (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion)
    (protection : ReceivingProtection layout state live region) :
    ReceivingProtection layout state live { region with mutableDestinations := [region.destination] } := by
  refine ⟨protection.present, protection.observations, protection.cutoff, protection.landing, by simp, ?_, ?_⟩
  · intro id member
    simp only [List.mem_singleton] at member
    subst id
    exact protection.authorityBound region.destination protection.authority
  · intro root active immutable value present stored occurrence id named
    have original := protection.names root active immutable value present stored occurrence id named
    simp only [List.mem_singleton]
    intro same
    subst id
    exact original protection.authority

theorem receivingProtection_does_not_cover_selected_descendant (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (incoming selected : Nat)
    (destination : region.destination = incoming)
    (protection : ReceivingProtection layout state live region)
    (row : PendingDestination) (member : row ∈ protectedRows state.construction incoming selected)
    (distinct : row.capability.id ≠ incoming) :
    ∃ reduced : ReceivingRegion, ReceivingProtection layout state live reduced ∧
      reduced.destination = incoming ∧ row.capability.id ∉ reduced.mutableDestinations := by
  refine ⟨{ region with mutableDestinations := [region.destination] },
    receivingProtection_receiver_only layout state live region protection, destination, ?_⟩
  simp only [List.mem_singleton, destination]
  exact distinct

theorem receivingProtection_receiver_and_replacement_only (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (selected : Nat)
    (protection : ReceivingProtection layout state live region)
    (selectedAuthority : selected ∈ region.mutableDestinations) :
    ReceivingProtection layout state live
      { region with mutableDestinations := [selected, region.destination] } := by
  refine ⟨protection.present, protection.observations, protection.cutoff, protection.landing, by simp, ?_, ?_⟩
  · intro id member
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with first | second
    · rw [first]
      exact protection.authorityBound selected selectedAuthority
    · rw [second]
      exact protection.authorityBound region.destination protection.authority
  · intro root active immutable value present stored occurrence id named
    have original := protection.names root active immutable value present stored occurrence id named
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or, not_false_eq_true, and_true]
    constructor
    · intro same
      subst id
      exact original selectedAuthority
    · intro same
      subst id
      exact original protection.authority

theorem receivingProtection_selected_descendant_gap (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (incoming selected : Nat)
    (destination : region.destination = incoming)
    (protection : ReceivingProtection layout state live region)
    (selectedAuthority : selected ∈ region.mutableDestinations)
    (row : PendingDestination) (member : row ∈ protectedRows state.construction incoming selected)
    (distinct : row.capability.id ≠ incoming) :
    ∃ reduced : ReceivingRegion, ReceivingProtection layout state live reduced ∧
      reduced.destination = incoming ∧ selected ∈ reduced.mutableDestinations ∧
      row.capability.id ∉ reduced.mutableDestinations := by
  have notSelected := ((protectedRows_exact_selection state.construction incoming selected row).mp member).2.1
  refine ⟨{ region with mutableDestinations := [selected, region.destination] },
    receivingProtection_receiver_and_replacement_only layout state live region selected protection selectedAuthority,
    destination, by simp, ?_⟩
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or, not_false_eq_true, and_true, destination]
  exact ⟨notSelected, distinct⟩

#print axioms receivingProtection_receiver_and_replacement_only
#print axioms receivingProtection_selected_descendant_gap
#print axioms receivingProtection_receiver_only
#print axioms receivingProtection_does_not_cover_selected_descendant

end Goose.Proofs.ConstructionAcceptedExecution
