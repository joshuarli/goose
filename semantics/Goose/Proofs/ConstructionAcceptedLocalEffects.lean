import Goose.Proofs.ConstructionAcceptedSource

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem GlobalEffectsAvailable.of_metadataIncluded {interpretation : RootInterpretation} {initialized : Nat}
    {localEffects accumulated : Eff} (included : EffectMetadataIncluded localEffects accumulated)
    (available : GlobalEffectsAvailable interpretation initialized accumulated) :
    GlobalEffectsAvailable interpretation initialized localEffects := by
  intro target member global rooted
  exact available target (included.accessTargets member) global rooted

#print axioms GlobalEffectsAvailable.of_metadataIncluded
end Goose.Proofs.ConstructionAcceptedExecution
