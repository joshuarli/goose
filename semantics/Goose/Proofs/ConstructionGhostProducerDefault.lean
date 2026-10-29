import Goose.Proofs.ConstructionGhostProducerSyntax

namespace Goose.Proofs.ConstructionGhostProducerDefault
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostScalarProducer
open Goose.Proofs.ConstructionGhostProducerSyntax

theorem defaultProducerSyntax (config : EvalConfig) (expression : Expr)
    (shape : DefaultBuilderExpression expression) (value : ValueSyntax config expression) : ProducerSyntax config expression :=
  .constructed expression (.default shape) value (.default expression shape value)

theorem defaultProducer_history (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (channels : List Channel) (expression : Expr) (before : ExecutionState)
    (shape : DefaultBuilderExpression expression) (value : ValueSyntax config expression) :
    SourceHistory config fuel [] (.producerWith environment channels expression) before
      (evalProduce fuel config environment channels expression before) :=
  producerSyntax_history fuel config closed environment channels expression before (defaultProducerSyntax config expression shape value)

#print axioms defaultProducerSyntax
#print axioms defaultProducer_history
end Goose.Proofs.ConstructionGhostProducerDefault
