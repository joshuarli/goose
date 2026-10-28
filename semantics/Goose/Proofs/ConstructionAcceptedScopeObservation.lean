import Goose.Proofs.ConstructionAcceptedScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem releaseScopeState_outsideActivation (environment : RuntimeActivation) (scope scopeInst : Nat)
    (state : ExecutionState) (root : Goose.Core.RootInst)
    (outside : ∀ localScope id, root ≠ .local environment.act localScope id) :
    (releaseScopeState environment scope scopeInst state).objects.lookup root = state.objects.lookup root ∧
    (releaseScopeState environment scope scopeInst state).objectOrdinals.lookup root = state.objectOrdinals.lookup root := by
  have absent : (Goose.Proofs.Exit.runtimeScopeRoots environment scope scopeInst).contains root = false := by
    apply Bool.eq_false_iff.mpr
    intro contains
    have member := List.contains_iff_mem.mp contains
    simp only [Goose.Proofs.Exit.runtimeScopeRoots, List.mem_filterMap] at member
    obtain ⟨entry, _, found⟩ := member
    split at found
    · simp only [Option.some.injEq] at found
      exact outside scopeInst entry.2 found.symm
    · cases found
  exact ⟨Goose.Proofs.ExitExecution.releaseScopeState_root_lookup environment scope scopeInst state root absent,
    releaseScopeState_ordinal_lookup environment scope scopeInst state root absent⟩

#print axioms releaseScopeState_outsideActivation
end Goose.Proofs.ConstructionAcceptedExecution
