import Goose.Proofs.ConstructionGhostSourceFuel

namespace Goose.Proofs.ConstructionGhostProducerOperands
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel

theorem operandFuel (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr)
    (supported : ∀ childFuel channel operand, childFuel < fuel → operand ∈ operands →
      FuelSupport config childFuel (.producerWith environment [channel] operand)) :
    FuelSupport config fuel (.producerOperands environment channels operands) := by
  induction fuel generalizing channels operands with
  | zero => exact .timeout _
  | succ fuel ih =>
      cases channels with
      | nil =>
          cases operands with
          | nil => exact .producerOperandsEmpty fuel environment
          | cons operand operands => exact .producerOperandsNoChannels fuel environment operand operands
      | cons channel channels =>
          cases operands with
          | nil => exact .producerOperandsNoValues fuel environment channel channels
          | cons operand operands =>
              refine .producerOperandsCons fuel environment channel channels operand operands ?_ ?_
              · exact supported fuel channel operand (Nat.lt_succ_self _) (by simp)
              · apply ih channels operands
                intro childFuel selected value lower member
                exact supported childFuel selected value (Nat.lt_trans lower (Nat.lt_succ_self _)) (by simp [member])

theorem valuesFuel (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr)
    (supported : ∀ childFuel channel operand, childFuel < fuel → operand ∈ operands →
      FuelSupport config childFuel (.producerWith environment [channel] operand)) :
    FuelSupport config fuel (.producerWith environment channels (.values operands)) := by
  cases fuel with
  | zero => exact .timeout _
  | succ fuel =>
      apply FuelSupport.producerValues
      intro planned
      apply operandFuel fuel config environment planned operands
      intro childFuel channel operand lower member
      exact supported childFuel channel operand (Nat.lt_trans lower (Nat.lt_succ_self _)) member

#print axioms operandFuel
#print axioms valuesFuel
end Goose.Proofs.ConstructionGhostProducerOperands
