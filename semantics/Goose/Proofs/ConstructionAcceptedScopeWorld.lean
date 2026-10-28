import Goose.Proofs.ConstructionAcceptedFreshness
import Goose.Proofs.ExitExecutionPathOutsideScopeReads

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem ownershipExecutionContext_releaseScope (environment : RuntimeActivation) (scope scopeInst : Nat)
    (state : ExecutionState) (ambient : OwnershipAmbient) (valid : OwnershipExecutionContext state ambient) :
    OwnershipExecutionContext (releaseScopeState environment scope scopeInst state) ambient :=
  ⟨valid.source, valid.retention, ownershipRuntimeFrames_releaseScope environment scope scopeInst state ambient valid.runtime,
    valid.reservations, valid.receiving, valid.bounds,
    ownershipRuntimeIdentities_releaseScope valid.identities environment scope scopeInst⟩

private theorem scope_filter_lookup {α : Type} (roots : List RootInst) (entries : List (RootInst × α))
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

theorem releaseScopeState_ordinal_lookup (environment : RuntimeActivation) (scope scopeInst : Nat)
    (state : ExecutionState) (root : RootInst)
    (outside : (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false) :
    (releaseScopeState environment scope scopeInst state).objectOrdinals.lookup root = state.objectOrdinals.lookup root :=
  scope_filter_lookup _ _ _ outside

private theorem scope_filter_found {α : Type} (roots : List RootInst) (entries : List (RootInst × α))
    (root : RootInst) (value : α)
    (found : (entries.filter (fun entry => !roots.contains entry.1)).lookup root = some value) :
    roots.contains root = false ∧ entries.lookup root = some value := by
  induction entries with
  | nil => simp at found
  | cons entry rest ih =>
    rcases entry with ⟨key, item⟩
    by_cases same : key = root
    · subst key
      cases kept : roots.contains root <;> simp_all [List.filter, List.lookup]
    · have mismatch : (root == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
      cases kept : roots.contains key <;>
        simp only [List.filter, List.lookup, kept, Bool.not_false, Bool.not_true, mismatch] at found ⊢ <;>
        exact ih found

theorem AcceptedWorld.releaseScope (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (environment : RuntimeActivation) (scope scopeInst : Nat)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    AcceptedWorld config initialized (releaseScopeState environment scope scopeInst state) ambient types
      (fun root => live root ∧ (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false)
      regions pending := by
  have globalsOutside : ∀ id, (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains (.global id) = false := by
    intro id
    apply Bool.eq_false_iff.mpr
    intro contains
    have member := List.contains_iff_mem.mp contains
    simp only [Goose.Proofs.Exit.runtimeScopeRoots, List.mem_filterMap] at member
    obtain ⟨entry, _, found⟩ := member
    split at found <;> simp_all
  let roots := Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst
  let after := releaseScopeState environment scope scopeInst state
  have objectLookup : ∀ root, roots.contains root = false → after.objects.lookup root = state.objects.lookup root :=
    fun root outside => Goose.Proofs.ExitExecution.releaseScopeState_root_lookup environment scope scopeInst state root outside
  have ordinalLookup : ∀ root, roots.contains root = false → after.objectOrdinals.lookup root = state.objectOrdinals.lookup root :=
    fun root outside => releaseScopeState_ordinal_lookup environment scope scopeInst state root outside
  have objectFound : ∀ root value, after.objects.lookup root = some value →
      roots.contains root = false ∧ state.objects.lookup root = some value :=
    fun root value found => scope_filter_found roots state.objects root value found
  have ordinalFound : ∀ root value, after.objectOrdinals.lookup root = some value →
      roots.contains root = false ∧ state.objectOrdinals.lookup root = some value :=
    fun root value found => scope_filter_found roots state.objectOrdinals root value found
  refine ⟨⟨ownershipExecutionContext_releaseScope environment scope scopeInst state ambient world.ownership,
    ?_, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨world.globals.1, ?_⟩
    intro id bound
    obtain ⟨descriptor, value, declared, found, represented⟩ := world.globals.2 id bound
    exact ⟨descriptor, value, declared, (objectLookup _ (globalsOutside id)).trans found, represented⟩
  · intro root ty value typed found
    exact world.heap root ty value typed (objectFound root value found).2
  · intro root value found
    exact world.objectsRegistered root value (objectFound root value found).2
  · intro root value found
    exact world.ordinalsRegistered root value (ordinalFound root value found).2
  · constructor
    · intro root retained value found
      exact (world.backing.values root retained.1 value (objectFound root value found).2).construction_frame (before := state) (after := after) rfl
    · intro root retained stored found
      rw [ordinalLookup root retained.2]
      exact world.backing.identities root retained.1 stored (objectFound root _ found).2
  · intro region member
    have valid := world.protections region member
    refine ⟨valid.present, ⟨⟨?_, ?_⟩, ?_⟩, valid.cutoff, valid.landing, valid.authority, valid.authorityBound, ?_⟩
    · intro root retained value found
      exact (valid.observations.backing.values root ⟨retained.1.1, retained.2⟩ value
        (objectFound root value found).2).construction_frame (before := state) (after := after) rfl
    · intro root retained stored found
      rw [ordinalLookup root retained.1.2]
      exact valid.observations.backing.identities root ⟨retained.1.1, retained.2⟩ stored (objectFound root _ found).2
    · intro root retained value found stored occurrence
      exact (valid.observations.observations root ⟨retained.1.1, retained.2⟩ value
        (objectFound root value found).2 stored occurrence).construction_frame config.layout state after region.limit stored rfl
    · intro root retained outside value found stored occurrence id named
      exact valid.names root retained.1 outside value (objectFound root value found).2 stored occurrence id named
  · intro frame member
    obtain ⟨ready, backing⟩ := world.carriers frame member
    exact ⟨⟨ready.lengths, fun channel carrier pair =>
      carrierReady_construction_frame state after rfl channel carrier (ready.pairs channel carrier pair)⟩,
      fun carrier present => carrierBacking_construction_frame config.layout state after rfl carrier (backing carrier present)⟩
  · intro id bound
    exact ⟨world.globalLive id bound, globalsOutside id⟩

#print axioms AcceptedWorld.releaseScope

end Goose.Proofs.ConstructionAcceptedExecution
