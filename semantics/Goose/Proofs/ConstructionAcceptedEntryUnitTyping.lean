import Goose.Proofs.ConstructionAcceptedPositions

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedEntry_bodyUnit (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (phase : frame.phase = .implementation config.module.entry)
    (compatible : SourceFrameCompatible accepted frame) :
    ∃ declared, typeBlock (implementationBodyFrame config frame).typingFuel
      (implementationBodyFrame config frame).typing frame.source.impl.body
      (implementationBodyFrame config frame).typingCounter = .ok ([.unit], declared) := by
  have origin := compatible.origin
  simp only [SourceOrigin, phase] at origin
  obtain ⟨original, calls, entryAt, implementationAt, rest⟩ := origin
  obtain ⟨entry, implementation, entryFound, implementationFound, parameters, results⟩ :=
    validated_entry config.module accepted.accepted
  have sameEntry : original = entry := Option.some.inj (entryAt.symm.trans entryFound)
  subst entry
  have sameImplementation : frame.source.impl = implementation := Option.some.inj (implementationAt.symm.trans implementationFound)
  have empty : frame.source.impl.results = #[] := by simpa only [sameImplementation] using results
  obtain ⟨declared, checked⟩ := validated_implementation_unit_typing config.module original.impl frame.source.impl
    accepted.accepted implementationAt empty
  exact ⟨declared, checked⟩

#print axioms acceptedEntry_bodyUnit
end Goose.Proofs.ConstructionAcceptedExecution
