import Goose.Proofs.ConstructionGhostProducerOperands
import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostProducerSyntax
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerOperands
open Goose.Proofs.ConstructionGhostScalarProducer


theorem producerSyntax_fuel (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (channels : List Channel) (expression : Expr)
    (derivation : ProducerSyntax config expression) : FuelSupport config fuel (.producerWith environment channels expression) :=
  (syntaxFuel_existsWithTails fuel config closed).producer environment channels expression derivation

theorem producerSyntax_history (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (channels : List Channel) (expression : Expr) (before : ExecutionState)
    (derivation : ProducerSyntax config expression) :
    SourceHistory config fuel [] (.producerWith environment channels expression) before
      (evalProduce fuel config environment channels expression before) :=
  fuelHistory_exists fuel config _ [] before (producerSyntax_fuel fuel config closed environment channels expression derivation)

#print axioms producerSyntax_fuel
#print axioms producerSyntax_history
end Goose.Proofs.ConstructionGhostProducerSyntax
