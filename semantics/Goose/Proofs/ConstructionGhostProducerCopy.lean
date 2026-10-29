import Goose.Proofs.ConstructionGhostProducerSyntax

namespace Goose.Proofs.ConstructionGhostProducerCopy
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerSyntax

theorem copyProducerSyntax (config : EvalConfig) (ty : Ty) (place : Place) (origin : Goose.Core.OriginId)
    (child : PlaceSyntax config place) : ProducerSyntax config (.copy ty place origin) :=
  .constructed (.copy ty place origin) (.copy ty place origin) (.copy ty place origin child) (.copy ty place origin child)

theorem copyProducer_history (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Ty) (place : Place) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (child : PlaceSyntax config place) :
    SourceHistory config fuel [] (.producerWith environment channels (.copy ty place origin)) before
      (evalProduce fuel config environment channels (.copy ty place origin) before) :=
  producerSyntax_history fuel config closed environment channels (.copy ty place origin) before (copyProducerSyntax config ty place origin child)

#print axioms copyProducerSyntax
#print axioms copyProducer_history
end Goose.Proofs.ConstructionGhostProducerCopy
