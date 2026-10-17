import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionInvocationValuesEscape

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem reached_value_escape_inv (rootFuel fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (expression : Expr) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (reached : ExitReached rootFuel config (.value fuel environment expression) initial)
    (escaped : ExitInvocation.action config (.value fuel environment expression) initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      ValueInvocationEdge config (.value fuel environment expression) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  obtain ⟨β, child, prepared, site, childEscape⟩ :=
    valueInvocation_escape_inv fuel config environment expression initial address carriers final escaped
  exact ⟨β, child, prepared, .call reached (.values site), site, childEscape⟩

theorem reached_bound_escape_inv (rootFuel fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (reached : ExitReached rootFuel config (.bound fuel environment count defaultValue operand) initial)
    (escaped : ExitInvocation.action config (.bound fuel environment count defaultValue operand) initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      ValueInvocationEdge config (.bound fuel environment count defaultValue operand) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  obtain ⟨β, child, prepared, site, childEscape⟩ :=
    boundInvocation_escape_inv fuel config environment count defaultValue operand initial address carriers final escaped
  exact ⟨β, child, prepared, .call reached (.values site), site, childEscape⟩

theorem reached_place_escape_inv (rootFuel fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operand : Place) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (reached : ExitReached rootFuel config (.place fuel environment operand) initial)
    (escaped : ExitInvocation.action config (.place fuel environment operand) initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      ValueInvocationEdge config (.place fuel environment operand) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  obtain ⟨β, child, prepared, site, childEscape⟩ :=
    placeInvocation_escape_inv fuel config environment operand initial address carriers final escaped
  exact ⟨β, child, prepared, .call reached (.values site), site, childEscape⟩

theorem reached_view_escape_inv (rootFuel fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operand : View) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (reached : ExitReached rootFuel config (.view fuel environment operand) initial)
    (escaped : ExitInvocation.action config (.view fuel environment operand) initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      ValueInvocationEdge config (.view fuel environment operand) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  obtain ⟨β, child, prepared, site, childEscape⟩ :=
    viewInvocation_escape_inv fuel config environment operand initial address carriers final escaped
  exact ⟨β, child, prepared, .call reached (.values site), site, childEscape⟩

theorem reached_print_escape_inv (rootFuel fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operand : PrintArg) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (reached : ExitReached rootFuel config (.printArgument fuel environment operand) initial)
    (escaped : ExitInvocation.action config (.printArgument fuel environment operand) initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      ValueInvocationEdge config (.printArgument fuel environment operand) initial child prepared ∧
      child.action config prepared = .escape address carriers final := by
  obtain ⟨β, child, prepared, site, childEscape⟩ :=
    printInvocation_escape_inv fuel config environment operand initial address carriers final escaped
  exact ⟨β, child, prepared, .call reached (.values site), site, childEscape⟩

end Goose.Proofs.ExitExecution
