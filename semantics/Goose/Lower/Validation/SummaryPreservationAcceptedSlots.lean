import Goose.Lower.Validation.SummaryPreservationAcceptedSummaries
import Goose.Lower.Validation.SummaryPreservationDeclaredCeilings

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem accepted_context_provenance_slots_declared {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {candidate : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : RootsBelow candidate (moduleTypedResultUpper module)) (rootCount : Nat) :
    ∀ row ∈ (lowerContextAt module ctx impl).roots.slots.getD #[],
      ∀ root ∈ rootsAt ((lowerContextAt module ctx impl).provenance candidate
        ((lowerContextAt module ctx impl).valueTypes (lower module)) rootCount).slots row.1,
        root ∈ row.2 := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained⟩ :=
    accepted_context_replay_produced accepted contextRow implementationRow bounded
  have actual := ready.finished_provenance (cfg_context_blocks module ctx impl)
    (accepted_context_provenance_seed accepted contextRow implementationRow ready.slotsEq ready.recipes retained) rootCount
  obtain ⟨found, row, checked⟩ := (validate_modOk module accepted).ctx context ctx contextRow
  rw [implementationRow] at row
  cases row
  intro entry member root rootMember
  apply typedContextSlotUpper_below_declared_row accepted implementationRow checked.annotationShape member root
  rw [← ready.slotsEq]
  exact actual.slots entry.1 root rootMember

theorem accepted_function_provenance_slots_declared {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ∀ row ∈ (lowerContextAt module ctx impl).roots.slots.getD #[],
      ∀ root ∈ rootsAt ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount).slots row.1,
        root ∈ row.2 :=
  accepted_context_provenance_slots_declared accepted contextRow implementationRow
    (accepted_resultRoots_implTypes_below accepted) _

#print axioms accepted_context_provenance_slots_declared
#print axioms accepted_function_provenance_slots_declared

end Goose.Lower.Validation.SummaryPreservation
