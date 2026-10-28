import Goose.Proofs.ConstructionAcceptedNestedArgumentList
import Goose.Proofs.ConstructionAcceptedEffectfulArgumentList

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem EffectfulScalarArguments.nested {expressions : List Expr} (forms : EffectfulScalarArguments expressions) :
    NestedEffectfulArguments expressions := by
  induction forms with
  | nil => exact .nil
  | cons form tail ih => exact .cons (.flat form) ih

theorem EffectfulScalarArguments.member {expressions : List Expr} (forms : EffectfulScalarArguments expressions)
    {expression : Expr} (member : expression ∈ expressions) : EffectfulScalarArgument expression := by
  induction forms with
  | nil => cases member
  | cons form tail ih =>
    simp only [List.mem_cons] at member
    rcases member with same | member
    · subst expression; exact form
    · exact ih member

theorem EffectfulScalarArgument.notNested {value : Expr} (form : EffectfulScalarArgument value)
    (outerScope innerScope id origin innerOrigin outerOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) :
    value ≠ .blockE ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin := by
  intro equal
  subst value
  cases form with
  | scalar form =>
    cases form with
    | numeric form =>
      cases form with
      | scalar form =>
        cases form with
        | scalar form => cases form

theorem EffectfulScalarArgument.nestedSafe {config : EvalConfig} {frame : ConstructionSourceFrame} {value : Expr}
    (form : EffectfulScalarArgument value) (safe : ArgumentBlockSafe config frame value) :
    NestedArgumentSafe config frame value := by
  refine ⟨safe, ?_⟩
  intro outerScope innerScope id origin innerOrigin outerOrigin expression intTy literal equal
  subst value
  cases form with
  | scalar form =>
    cases form with
    | numeric form =>
      cases form with
      | scalar form =>
        cases form with
        | scalar form => cases form

#print axioms EffectfulScalarArguments.nested
#print axioms EffectfulScalarArguments.member
#print axioms EffectfulScalarArgument.nestedSafe
#print axioms EffectfulScalarArgument.notNested
end Goose.Proofs.ConstructionAcceptedExecution
