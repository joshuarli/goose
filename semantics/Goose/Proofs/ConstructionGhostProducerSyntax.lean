import Goose.Proofs.ConstructionGhostProducerOperands
import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostProducerSyntax
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostProducerOperands
open Goose.Proofs.ConstructionGhostScalarProducer

inductive ProducerSyntax (config : EvalConfig) : Expr → Prop
  | constructed (expression : Expr) (shape : ValueProducerExpression expression)
      (value : ValueSyntax config expression) (builder : DeclarationBuilderSyntax config expression) :
      ProducerSyntax config expression
  | call (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (argumentsSyntax : ∀ id implementation start ready,
        getImplementation config context start = .ok (id, implementation) ready →
        ArgumentSyntax config implementation.params.toList arguments) :
      ProducerSyntax config (.call context arguments origin)
  | block (block : Block) (origin : Goose.Core.OriginId) (child : ResultBlockSyntax config block) :
      ProducerSyntax config (.blockE block origin)
  | conditional (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId)
      (conditionChild : ValueSyntax config condition) (yesChild : ResultBlockSyntax config yes) (noChild : ResultBlockSyntax config no) :
      ProducerSyntax config (.ifE condition yes no origin)
  | values (operands : List Expr) (children : ∀ operand ∈ operands, ProducerSyntax config operand) :
      ProducerSyntax config (.values operands)

theorem producerSyntax_fuel (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (channels : List Channel) (expression : Expr)
    (derivation : ProducerSyntax config expression) : FuelSupport config fuel (.producerWith environment channels expression) := by
  induction fuel using Nat.strongRecOn generalizing environment channels expression with
  | ind fuel ih =>
      cases derivation with
      | constructed expression shape value builder =>
          exact (syntaxFuel_existsWithTails fuel config closed).constructedProducer environment channels expression shape value builder
      | call context arguments origin argumentsSyntax =>
          exact (syntaxFuel_existsWithTails fuel config closed).producerCall environment channels context arguments origin argumentsSyntax
      | block block origin child =>
          exact (syntaxFuel_existsWithTails fuel config closed).blockProducer environment channels block origin child
      | conditional condition yes no origin conditionChild yesChild noChild =>
          exact (syntaxFuel_existsWithTails fuel config closed).conditionalProducer environment channels condition yes no origin conditionChild yesChild noChild
      | values operands children =>
          apply valuesFuel fuel config environment channels operands
          intro childFuel channel operand lower member
          exact ih childFuel lower environment [channel] operand (children operand member)

theorem producerSyntax_history (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config)
    (environment : RuntimeActivation) (channels : List Channel) (expression : Expr) (before : ExecutionState)
    (derivation : ProducerSyntax config expression) :
    SourceHistory config fuel [] (.producerWith environment channels expression) before
      (evalProduce fuel config environment channels expression before) :=
  fuelHistory_exists fuel config _ [] before (producerSyntax_fuel fuel config closed environment channels expression derivation)

#print axioms producerSyntax_fuel
#print axioms producerSyntax_history
end Goose.Proofs.ConstructionGhostProducerSyntax
