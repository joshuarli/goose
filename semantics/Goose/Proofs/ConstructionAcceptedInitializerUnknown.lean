import Goose.Proofs.ConstructionAcceptedGlobalFrame
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def initializerHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_initializer_capacity" : tactic => do
  let capacity := Lean.mkIdent (initializerHelperName "noteReceivingCapacity")
  let shape := Lean.mkIdent (initializerHelperName "receivingCapacity")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $capacity $shape at *))

theorem initializerRootFacts_scalar_noUnknown (config : EvalConfig) (id : Nat) (descriptor : Global)
    (names : Array (List RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (present : config.module.globals[id]? = some descriptor)
    (facts : InitializerRootFactsAt config.module id calls names)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (roots : List RootRef) (after : RState)
    (rooted : rpExpr (initializerSource config names) descriptor.init ⟨0, {}, []⟩ = .ok (roots, after)) :
    after.eff.unknown = false := by
  obtain ⟨effects, checked, callsEq⟩ := facts
  unfold_initializer_root_checker
  simp only [present] at checked
  simp only [initializerSource] at rooted
  unfold_initializer_capacity
  rcases scalar with ⟨integer, shape⟩ | shape <;> rw [shape] at checked <;>
    simp only [StateT.run, rooted, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked <;>
    cases unknown : after.eff.unknown <;> simp_all [Goose.Core.reject]

theorem validated_scalar_initializer_noUnknown (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) :
    ∃ names roots after, rpExpr (initializerSource config names) descriptor.init ⟨0, {}, []⟩ = .ok (roots, after) ∧
      after.eff.unknown = false := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  obtain ⟨calls, ⟨names, facts⟩, _⟩ := (Classical.choose_spec accepted.roots).2.2 id inside
  obtain ⟨roots, after, rooted⟩ := initializerRootFacts_operand config id descriptor names calls present facts
  exact ⟨names, roots, after, rooted, initializerRootFacts_scalar_noUnknown config id descriptor names calls present facts scalar roots after rooted⟩

#print axioms validated_scalar_initializer_noUnknown
#print axioms initializerRootFacts_scalar_noUnknown
end Goose.Proofs.ConstructionAcceptedExecution
