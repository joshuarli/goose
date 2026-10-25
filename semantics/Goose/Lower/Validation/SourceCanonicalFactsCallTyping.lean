import Goose.Evidence.TypingValidation
import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem canonical_call_type_facts {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {function : FnId} {arguments : List ValueId}
    {origin : Option OriginId} {result : VTy}
    (typed : (Op.call function arguments origin).resultTy
      {module.tyEnv func with vals := types} = .ok result)
    (bounded : ∀ argument ∈ arguments, argument < func.numValues) :
    ∃ callee, module.funcs[function]? = some callee ∧
      callee.params.length = arguments.length ∧
      (∀ index, index < callee.params.length →
        ∃ argument, arguments[index]? = some argument ∧ argument < func.numValues) ∧
      ∀ (index : Nat) (outer : Mutability) (payload : Ty), callee.params[index]? = some (.ref outer payload) →
        ∃ argument actualMutability, arguments[index]? = some argument ∧
          types[argument]? = some (some (.data (.ref actualMutability payload))) ∧
          argument < func.numValues := by
  obtain ⟨params, results, signature, arity, argumentsTyped, _⟩ := call_resultTy_metadata typed
  change (module.funcs.map (fun f => (f.params, f.results)))[function]? = some (params, results) at signature
  cases calleeAt : module.funcs[function]? with
  | none => simp [calleeAt] at signature
  | some callee =>
    have same : (callee.params, callee.results) = (params, results) := by
      simpa [calleeAt] using signature
    cases same
    refine ⟨callee, rfl, arity, ?_, ?_⟩
    · intro index indexBound
      have argumentBound : index < arguments.length := arity ▸ indexBound
      have argumentAt : arguments[index]? = some arguments[index] :=
        List.getElem?_eq_getElem argumentBound
      exact ⟨_, argumentAt, bounded _ (List.mem_of_getElem? argumentAt)⟩
    · intro index outer payload parameterAt
      have indexBound : index < callee.params.length := (List.getElem?_eq_some_iff.mp parameterAt).1
      have argumentBound : index < arguments.length := arity ▸ indexBound
      have argumentAt : arguments[index]? = some arguments[index] :=
        List.getElem?_eq_getElem argumentBound
      have pairMember : (.ref outer payload, arguments[index]) ∈ callee.params.zip arguments :=
        List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨parameterAt, argumentAt⟩)
      obtain ⟨actual, row, passable⟩ := argumentsTyped _ pairMember
      have actualReference : ∃ mutability, actual = .ref mutability payload := by
        cases actual with
        | ref mutability referent =>
          have same : referent = payload := eq_of_beq (Bool.and_eq_true_iff.mp passable).1
          exact ⟨mutability, same ▸ rfl⟩
        | _ => simp [Ty.passableTo] at passable
      obtain ⟨mutability, rfl⟩ := actualReference
      exact ⟨_, mutability, argumentAt, row, bounded _ (List.mem_of_getElem? argumentAt)⟩

#print axioms canonical_call_type_facts

end Goose.Lower.Validation
