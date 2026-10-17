import Goose.GIR.ReplacementContentFlowProofsCanonicalQueries

namespace Goose.GIR

open Goose.Core ReplacementContentFlow.Model

theorem ReplacementContentFlow.forFunction_value_within_provenance {module : Module}
    {provenances : Array Prov} {results : Array (List RootRef)}
    {func : Func} {types : Array (Option VTy)} {provenance : Prov} {value : ValueId} {roots : List RootRef}
    (facts : FunctionCanonicalFacts module func (func.valueTypes module) provenance results)
    (moduleFacts : ModuleCanonicalFacts module (module.funcs.map (·.valueTypes module)) provenances results)
    (annotations : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee →
      annotationsValid module callee = true)
    (entries : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee →
      ∀ entry : Block, callee.blocks[0]? = some entry → entry.params.length ≤ callee.params.length)
    (addresses : ∀ (index : Nat) (callee : Func), module.funcs[index]? = some callee →
      FunctionAddressesBounded module callee)
    (known : ((replacementContentFlow module).forFunction func types).value value = some roots) :
    roots ⊆ (rootsAt provenance.vals value).flatMap func.expandParameterRoot := by
  rw [ReplacementFunctionFlow.value_model] at known
  cases stateAt : ((replacementContentFlow module).forFunction func types).model with
  | none => simp [stateAt] at known
  | some state =>
    simp only [stateAt, Option.bind_some] at known
    have canonical := ReplacementContentFlow.forFunction_canonicalWithin facts moduleFacts
      annotations entries addresses stateAt
    have bounded := normalize_flowAt_bounded known
    have ready : flowAt state.values value ≠ .pending := by
      intro pending
      simp [pending, normalize] at known
    obtain ⟨actual, actualAt, included⟩ :=
      SymbolicRootsRefine.actual facts.roots.closed (canonical.values value bounded) ready
    have same : actual = roots := Option.some.inj (actualAt.symm.trans known)
    simpa only [same] using included

#print axioms ReplacementContentFlow.forFunction_value_within_provenance

end Goose.GIR
