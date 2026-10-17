import Goose.Lower.Validation.ValidationTypedModuleEntry
import Goose.Lower.Validation.ValidationTypedModuleTables
import Goose.Lower.Validation.ReplacementParameterRoots
import Goose.Lower.Validation.SourceCanonicalFactsParameterModes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem finished_parameters {func : Func} {state : LS} {types : Array (Option VTy)}
    (blocks : func.blocks = finishBlocks state.blocks) (values : types = state.vals)
    (typed : EmittedParametersTyped state)
    (signature : ∀ entry : GIR.Block, func.blocks[0]? = some entry → entry.params.map Prod.snd = func.params.map VTy.data)
    (entry : GIR.Block) (entryAt : func.blocks[0]? = some entry)
    (pair : ValueId × VTy) (index : Nat) (member : (pair, index) ∈ entry.params.zipIdx) :
    ∃ type, pair.2 = .data type ∧ types[pair.1]? = some (some (.data type)) ∧ func.params[index]? = some type := by
  have parameterAt : entry.params[index]? = some pair := List.mk_mem_zipIdx_iff_getElem?.mp member
  have aligned := congrArg (fun list => list[index]?) (signature entry entryAt)
  simp only [List.getElem?_map, parameterAt, Option.map_some] at aligned
  cases formalAt : func.params[index]? with
  | none => simp [formalAt] at aligned
  | some type =>
    have same : pair.2 = .data type := by simpa [formalAt] using aligned
    refine ⟨type, same, ?_, rfl⟩
    rw [blocks, finishBlocks, Array.getElem?_map] at entryAt
    obtain ⟨body, row, bodyEq⟩ := Option.map_eq_some_iff.mp entryAt
    have pairMember : pair ∈ body.params := by
      rw [← bodyEq] at parameterAt
      exact List.mem_of_getElem? parameterAt
    have sourceRow := typed 0 body row pair.1 pair.2 pairMember
    simpa only [values, same] using sourceRow

theorem lowerContext_canonical_parameters_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {context : Context} {impl : Core.Impl} {index : ImplId}
    (implAt : module.impls[index]? = some impl) :
    ∀ entry : GIR.Block, (lowerContextAt module context impl).blocks[0]? = some entry →
      ∀ pair index, (pair, index) ∈ entry.params.zipIdx →
      ∃ type, pair.2 = .data type ∧
        ((lowerContextAt module context impl).valueTypes (lower module))[pair.1]? = some (some (.data type)) ∧
        (lowerContextAt module context impl).params[index]? = some type :=
  finished_parameters (cfg_context_blocks module context impl)
    (lowerContext_valueTypes_of_accepted accepted implAt)
    (lowerImpl_emittedBuilder_of_accepted accepted implAt).checkpoint.parameters
    (by
      intro entry entryAt
      obtain ⟨actual, actualAt, signature⟩ := lowerContext_entry_types module context impl
      have same : actual = entry := Option.some.inj (actualAt.symm.trans entryAt)
      subst entry
      exact signature)

theorem lowerGlobal_canonical_parameters_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : GlobalId}
    (globalAt : module.globals[index]? = some global) :
    ∀ entry : GIR.Block, (lowerGlobal module global).init.blocks[0]? = some entry →
      ∀ pair index, (pair, index) ∈ entry.params.zipIdx →
      ∃ type, pair.2 = .data type ∧
        ((lowerGlobal module global).init.valueTypes (lower module))[pair.1]? = some (some (.data type)) ∧
        (lowerGlobal module global).init.params[index]? = some type :=
  finished_parameters (cfg_global_blocks module global)
    (lowerGlobal_valueTypes_of_accepted accepted globalAt)
    (lowerGlobal_emittedBuilder_of_accepted accepted globalAt).checkpoint.parameters
    (by
      intro entry entryAt
      obtain ⟨actual, actualAt, signature⟩ := lowerGlobal_entry_types module global
      have same : actual = entry := Option.some.inj (actualAt.symm.trans entryAt)
      subst entry
      exact signature)

theorem lowerContext_canonical_parameter_seeds (module : Core.Module) (context : Context) (impl : Core.Impl)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat)
    (entry : GIR.Block) (entryAt : (lowerContextAt module context impl).blocks[0]? = some entry)
    (pair : ValueId × VTy) (index : Nat) (member : (pair, index) ∈ entry.params.zipIdx)
    (reference : valRefLike types pair.1 = true) :
    RootRef.param index ∈ rootsAt ((lowerContextAt module context impl).provenance results types rootCount).vals pair.1 := by
  exact provenance_ref_parameter_of_dense results types (lowerContextAt module context impl) rootCount (lowerImpl_dense_definitions module impl)
    entryAt (List.mk_mem_zipIdx_iff_getElem?.mp member) reference

theorem lowerGlobal_canonical_parameter_seeds (module : Core.Module) (global : Core.Global)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat)
    (entry : GIR.Block) (entryAt : (lowerGlobal module global).init.blocks[0]? = some entry)
    (pair : ValueId × VTy) (index : Nat) (member : (pair, index) ∈ entry.params.zipIdx)
    (reference : valRefLike types pair.1 = true) :
    RootRef.param index ∈ rootsAt ((lowerGlobal module global).init.provenance results types rootCount).vals pair.1 := by
  exact provenance_ref_parameter_of_dense results types (lowerGlobal module global).init rootCount (lowerGlobal_dense_definitions module global)
    entryAt (List.mk_mem_zipIdx_iff_getElem?.mp member) reference


#print axioms lowerContext_canonical_parameters_of_accepted
#print axioms lowerGlobal_canonical_parameters_of_accepted

end Goose.Lower.Validation
