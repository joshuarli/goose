import Goose.Proofs.ExitExecutionInvocationProducersEscapeSupport

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem bind_escape_arguments (action : EvalM α) (next : α → EvalM β)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (cannotEscape : ProducerNeverEscapes action)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    ∃ first middle, action initial = .ok first middle ∧ next first middle = .escape address carriers final := by
  cases evaluated : action initial <;> simp only [bind, evaluated] at escaped
  case ok first middle => exact ⟨first, middle, rfl, escaped⟩
  case escape target returned after => exact False.elim (cannotEscape _ _ _ _ evaluated)
  all_goals cases escaped

private theorem argumentsNeverEscapes_publish (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    ProducerNeverEscapes (publishCarriers origin carriers) := by
  unfold publishCarriers
  producer_never_escapes_base

theorem constructLocal_escape_call (declarations : DeclarationEnv) (owner : Goose.Core.ActId) (ty : Ty)
    (origin : Goose.Core.OriginId) (expression : Expr) (construct : Nat → EvalM Unit)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : constructLocal declarations owner ty origin expression construct initial = .escape address carriers final) :
    ∃ destination prepared,
      newDestination (LayoutEnv.ofModule declarations.module) owner ty .value origin none
        (producerCount? declarations expression) initial = .ok destination prepared ∧
      construct destination prepared = .escape address carriers final := by
  unfold constructLocal at escaped
  obtain ⟨destination, prepared, allocated, rest⟩ := bind_escape_arguments _ _ initial final address carriers
    (producerNeverEscapes_newDestination _ _ _ _ _ _ _) escaped
  refine ⟨destination, prepared, allocated, ?_⟩
  cases built : construct destination prepared with
  | escape target returned after =>
      simp only [bind, built] at rest
      cases rest
      rfl
  | stop reason after | jump target kind after =>
      simp only [bind, built] at rest
      cases rest
  | ok value after =>
      simp only [bind, built] at rest
      obtain ⟨completed, published, done, rest⟩ := bind_escape_arguments _ _ after final address carriers
        (producerNeverEscapes_completedReceivingDestination _) rest
      obtain ⟨unitValue, finished, publication, rest⟩ := bind_escape_arguments _ _ published final address carriers
        (argumentsNeverEscapes_publish _ _) rest
      cases rest

theorem materializeProducer_escape_value (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operand : Expr) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : materializeProducer fuel ⟨config.module, environment.vars⟩ operand
      (evalValue fuel config environment operand) initial = .escape address carriers final) :
    ∃ count, ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = some count ∧
      evalValue fuel config environment operand initial = .escape address carriers final := by
  cases count : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand with
  | none =>
      simp only [materializeProducer, count, pure] at escaped
      cases escaped
  | some countValue =>
      refine ⟨countValue, rfl, ?_⟩
      simp only [materializeProducer, count, bind] at escaped
      cases evaluated : evalValue fuel config environment operand initial with
      | escape target returned after =>
          simp only [evaluated] at escaped
          cases escaped
          rfl
      | ok value after =>
          cases value <;> simp only [evaluated, pure, fault, EvalM.stop] at escaped <;> cases escaped
      | stop reason after | jump target kind after =>
          simp only [evaluated] at escaped
          cases escaped

#print axioms constructLocal_escape_call
#print axioms materializeProducer_escape_value

end Goose.Proofs.ExitExecution
