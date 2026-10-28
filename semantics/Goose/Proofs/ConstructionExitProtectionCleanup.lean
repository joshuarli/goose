import Goose.Proofs.ConstructionExitByteReservationPrefix
import Goose.Proofs.ConstructionExitOutsideUnwind

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct Goose.Core
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem receivingProtection_release_ticket (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (token : Nat)
    (protection : ReceivingProtection layout state live region) :
    ReceivingProtection layout { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } } live region := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have prefixes : StoragePrefixesEqual region.limit state.construction.storage cleaned.construction.storage := by
    intro id
    rfl
  have observations := rootedBackingObservations_storagePrefixes layout state cleaned _ region.limit
    protection.observations prefixes rfl rfl (by intros; rfl)
  exact ⟨protection.present, observations, protection.cutoff, protection.landing,
    protection.authority, protection.authorityBound, protection.names⟩

theorem receivingProtection_actual_ticket_cleanup (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (token incoming selected : Nat)
    (snapshot : PendingDestination) (origin : OriginId) (carriers : List Goose.Construct.Carrier)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (protection : ReceivingProtection layout state live region) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      ReceivingProtection layout cleaned live region := by
  let cleaned := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token .released } }
  have released := releaseExitReservation_active state.construction token .fresh incoming selected snapshot ticket
  have actual : exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  exact ⟨cleaned, actual, receivingProtection_release_ticket layout state live region token protection⟩

theorem receivingProtection_root_frame (layout : LayoutEnv) (before after : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion)
    (construction : after.construction = before.construction)
    (objects : ∀ root, live root → ¬ region.mutableRoots root → after.objects.lookup root = before.objects.lookup root)
    (ordinals : ∀ root, live root → ¬ region.mutableRoots root → after.objectOrdinals.lookup root = before.objectOrdinals.lookup root)
    (protection : ReceivingProtection layout before live region) : ReceivingProtection layout after live region := by
  refine ⟨?_, ?_, ?_, ?_, protection.authority, ?_, ?_⟩
  · simpa only [construction] using protection.present
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro root retained value present
      rw [objects root retained.1 retained.2] at present
      exact (protection.observations.backing.values root retained value present).construction_frame construction
    · intro root retained stored present
      rw [objects root retained.1 retained.2] at present
      rw [ordinals root retained.1 retained.2]
      exact protection.observations.backing.identities root retained stored present
    · intro root retained value present stored occurrence
      rw [objects root retained.1 retained.2] at present
      exact (protection.observations.observations root retained value present stored occurrence).construction_frame
        layout before after region.limit stored construction
  · intro row present
    exact protection.cutoff row (by simpa only [construction] using present)
  · intro row present
    exact protection.landing row (by simpa only [construction] using present)
  · intro id member
    simpa only [construction] using protection.authorityBound id member
  · intro root active immutable value present stored occurrence id named
    rw [objects root active immutable] at present
    exact protection.names root active immutable value present stored occurrence id named

theorem scope_filter_lookup_any {α : Type} (roots : List RootInst) (entries : List (RootInst × α))
    (root : RootInst) (outside : roots.contains root = false) :
    (entries.filter (fun entry => !roots.contains entry.1)).lookup root = entries.lookup root := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : key = root
      · subst key
        simp only [List.filter, List.lookup, outside, Bool.not_false, beq_self_eq_true]
      · have mismatch : (root == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
        cases kept : roots.contains key <;>
          simp only [List.filter, List.lookup, kept, Bool.not_false, Bool.not_true, mismatch, ih]

theorem receivingProtection_release_scope (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (environment : RuntimeActivation)
    (scope scopeInst : Nat)
    (outside : ∀ root, live root → ¬ region.mutableRoots root →
      (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false)
    (protection : ReceivingProtection layout state live region) :
    ReceivingProtection layout (releaseScopeState environment scope scopeInst state) live region := by
  apply receivingProtection_root_frame layout state (releaseScopeState environment scope scopeInst state) live region rfl
  · intro root active immutable
    exact releaseScopeState_root_lookup environment scope scopeInst state root (outside root active immutable)
  · intro root active immutable
    exact scope_filter_lookup_any _ _ root (outside root active immutable)
  · exact protection

theorem receivingProtection_cleanup_two_scopes (layout : LayoutEnv) (state : ExecutionState)
    (live : RootInst → Prop) (region : ReceivingRegion) (token incoming selected : Nat)
    (snapshot : PendingDestination) (origin : OriginId) (carriers : List Goose.Construct.Carrier)
    (inner outer : RuntimeActivation) (innerScope outerScope : Nat) (innerInst outerInst : ScopeInst)
    (ticket : state.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot))
    (innerOutside : ∀ root, live root → ¬ region.mutableRoots root →
      (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerInst).contains root = false)
    (outerOutside : ∀ root, live root → ¬ region.mutableRoots root →
      (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInst).contains root = false)
    (protection : ReceivingProtection layout state live region) :
    ∃ cleaned, exitChannelCleanupBorrowed origin [] [token] false carriers state = .ok () cleaned ∧
      let first := releaseScopeState inner innerScope innerInst cleaned
      let crossed := { first with activations := first.activations.filter (fun current => current.act != inner.act) }
      let second := releaseScopeState outer outerScope outerInst crossed
      let final := { second with activations := second.activations.filter (fun current => current.act != outer.act) }
      ReceivingProtection layout final live region := by
  obtain ⟨cleaned, actual, cleanedProtection⟩ := receivingProtection_actual_ticket_cleanup
    layout state live region token incoming selected snapshot origin carriers ticket protection
  let first := releaseScopeState inner innerScope innerInst cleaned
  let crossed := { first with activations := first.activations.filter (fun current => current.act != inner.act) }
  let second := releaseScopeState outer outerScope outerInst crossed
  let final := { second with activations := second.activations.filter (fun current => current.act != outer.act) }
  have firstProtection := receivingProtection_release_scope layout cleaned live region inner innerScope innerInst innerOutside cleanedProtection
  have crossedProtection : ReceivingProtection layout crossed live region :=
    receivingProtection_root_frame layout first crossed live region rfl (by intros; rfl) (by intros; rfl) firstProtection
  have secondProtection := receivingProtection_release_scope layout crossed live region outer outerScope outerInst outerOutside crossedProtection
  have finalProtection : ReceivingProtection layout final live region :=
    receivingProtection_root_frame layout second final live region rfl (by intros; rfl) (by intros; rfl) secondProtection
  exact ⟨cleaned, actual, finalProtection⟩

#print axioms receivingProtection_cleanup_two_scopes
#print axioms receivingProtection_root_frame
#print axioms scope_filter_lookup_any
#print axioms receivingProtection_release_scope
#print axioms receivingProtection_release_ticket
#print axioms receivingProtection_actual_ticket_cleanup

end Goose.Proofs.ConstructionAcceptedExecution
