import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionInvocationProducersInversion

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem reached_produce_escape_inv {rootFuel fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} (channels : List Channel) (expression : Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (.produce fuel environment channels expression) initial)
    (escaped : evalProduce fuel config environment channels expression initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (ready before : ExecutionState),
      ExitReached rootFuel config child ready ∧
      ProducerEscapeResult config (.produce fuel environment channels expression) initial child ready carriers before final ∧
      child.action config ready = .escape address carriers before := by
  obtain ⟨β, child, ready, before, result, childEscape⟩ :=
    produceInvocation_escape_inv fuel config environment channels expression initial address carriers final escaped
  exact ⟨β, child, ready, before, .call reached (.producer result.site), result, childEscape⟩

theorem reached_build_escape_inv {rootFuel fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} (destination : Nat) (expression : Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (.build fuel environment destination expression) initial)
    (escaped : buildExpr fuel config environment destination expression initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (ready before : ExecutionState),
      ExitReached rootFuel config child ready ∧
      ProducerEscapeResult config (.build fuel environment destination expression) initial child ready carriers before final ∧
      child.action config ready = .escape address carriers before := by
  obtain ⟨β, child, ready, before, result, childEscape⟩ :=
    buildInvocation_escape_inv fuel config environment destination expression initial address carriers final escaped
  exact ⟨β, child, ready, before, .call reached (.producer result.site), result, childEscape⟩

theorem reached_element_escape_inv {rootFuel fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} (destination : Nat) (element : Ty) (operand : Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (.element fuel environment destination element operand) initial)
    (escaped : buildElement fuel config environment destination element operand initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (ready before : ExecutionState),
      ExitReached rootFuel config child ready ∧
      ProducerEscapeResult config (.element fuel environment destination element operand) initial child ready carriers before final ∧
      child.action config ready = .escape address carriers before := by
  obtain ⟨β, child, ready, before, result, childEscape⟩ :=
    elementInvocation_escape_inv fuel config environment destination element operand initial address carriers final escaped
  exact ⟨β, child, ready, before, .call reached (.producer result.site), result, childEscape⟩

#print axioms reached_produce_escape_inv
#print axioms reached_build_escape_inv
#print axioms reached_element_escape_inv

end Goose.Proofs.ExitExecution
