import Goose.Lower.Validation.SourceCanonicalFactsInstructions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem typed_call_results {module : GIR.Module} {func callee : Func}
    {types : Array (Option VTy)} {value : ValueId} {fn : FnId} {args : List ValueId} {origin : Option OriginId}
    (typed : InstructionTyping module func types (.def value (.call fn args origin)))
    (calleeAt : module.funcs[fn]? = some callee) :
    (callee.results = [] ∧ types[value]? = some (some (.data .unit))) ∨
      ∃ type, callee.results = [type] ∧ types[value]? = some (some (.data type)) := by
  cases typed with
  | definition _ _ type successful canonical =>
    have signature : ({module.tyEnv func with vals := types} : TyEnv).sigs[fn]? = some (callee.params, callee.results) := by
      change (module.funcs.map fun function => (function.params, function.results))[fn]? = some (callee.params, callee.results)
      simp [Array.getElem?_map, calleeAt]
    simp only [Op.resultTy, signature] at successful
    by_cases arity : callee.params.length = args.length
    · simp only [if_pos arity] at successful
      obtain ⟨_, _, result⟩ := (ex_bind_ok _ _ _).mp successful
      cases results : callee.results with
      | nil =>
        have same : type = .data .unit := by simpa [results, pure, Except.pure] using result.symm
        exact Or.inl ⟨rfl, same ▸ canonical⟩
      | cons first rest =>
        cases rest with
        | nil =>
          have same : type = .data first := by simpa [results, pure, Except.pure] using result.symm
          exact Or.inr ⟨first, rfl, same ▸ canonical⟩
        | cons second rest => simp [results, tyErr] at result
    · simp [arity, tyErr, bind, Except.bind] at successful

theorem lowerContext_canonical_callResults_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Core.Impl}
    (contextAt : module.contexts[index]? = some context) (implAt : module.impls[context.impl]? = some impl)
    (block : GIR.Block) (blockMember : block ∈ (lowerContextAt module context impl).blocks.toList)
    (value : ValueId) (fn : FnId) (args : List ValueId) (origin : Option OriginId)
    (instruction : Inst.def value (.call fn args origin) ∈ block.insts) (callee : Func)
    (calleeAt : (lower module).funcs[fn]? = some callee) :
    (callee.results = [] ∧ ((lowerContextAt module context impl).valueTypes (lower module))[value]? = some (some (.data .unit))) ∨
      ∃ type, callee.results = [type] ∧ ((lowerContextAt module context impl).valueTypes (lower module))[value]? = some (some (.data type)) :=
  typed_call_results (lowerContext_instructionCanonicalFacts_of_accepted accepted contextAt implAt block blockMember _ instruction) calleeAt

theorem lowerGlobal_canonical_callResults_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global)
    (block : GIR.Block) (blockMember : block ∈ (lowerGlobal module global).init.blocks.toList)
    (value : ValueId) (fn : FnId) (args : List ValueId) (origin : Option OriginId)
    (instruction : Inst.def value (.call fn args origin) ∈ block.insts) (callee : Func)
    (calleeAt : (lower module).funcs[fn]? = some callee) :
    (callee.results = [] ∧ ((lowerGlobal module global).init.valueTypes (lower module))[value]? = some (some (.data .unit))) ∨
      ∃ type, callee.results = [type] ∧ ((lowerGlobal module global).init.valueTypes (lower module))[value]? = some (some (.data type)) :=
  typed_call_results (lowerGlobal_instructionCanonicalFacts_of_accepted accepted globalAt block blockMember _ instruction) calleeAt

#print axioms lowerContext_canonical_callResults_of_accepted
#print axioms lowerGlobal_canonical_callResults_of_accepted

end Goose.Lower.Validation
