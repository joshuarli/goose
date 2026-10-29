import Goose.Proofs.ConstructionGhostProducerSyntax

namespace Goose.Proofs.ConstructionGhostProducerString
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerSyntax

theorem stringProducerSyntax (config : EvalConfig) (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId)
    (children : ∀ argument ∈ arguments, PrintArgumentSyntax config argument) : ProducerSyntax config (.str ty arguments origin) :=
  .constructed (.str ty arguments origin) (.string ty arguments origin)
    (.string ty arguments origin children) (.string ty arguments origin children)

theorem stringProducer_history (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (channels : List Channel) (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (children : ∀ argument ∈ arguments, PrintArgumentSyntax config argument) :
    SourceHistory config fuel [] (.producerWith environment channels (.str ty arguments origin)) before
      (evalProduce fuel config environment channels (.str ty arguments origin) before) :=
  producerSyntax_history fuel config closed environment channels (.str ty arguments origin) before
    (stringProducerSyntax config ty arguments origin children)

#print axioms stringProducerSyntax
#print axioms stringProducer_history
end Goose.Proofs.ConstructionGhostProducerString
