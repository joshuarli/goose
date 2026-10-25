import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts
import Goose.Lower.Validation.ValidationTypedModuleInstructions
import Goose.Lower.Validation.CfgSourceEdgeFunctions
import Goose.Lower.Validation.EmittedMetadataAcceptance

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem definition_typing {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {value : ValueId} {op : Op}
    (checked : checkInstTypes func {module.tyEnv func with vals := types} types (.def value op) = .ok ()) :
    InstructionTyping module func types (.def value op) := by
  cases result : op.resultTy {module.tyEnv func with vals := types} with
  | error message => simp [checkInstTypes, result, bind, Except.bind] at checked
  | ok type =>
    by_cases canonical : types[value]? = some (some type)
    · exact .definition value op type result canonical
    · simp [checkInstTypes, result, canonical, bind, Except.bind] at checked

private theorem effect_typing {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {le : LEnv} {state : LS} {effect : Effect}
    (slots : func.slots = le.slots) (values : types = state.vals)
    (typed : EmittedEffectTyped le state effect) : InstructionTyping module func types (.eff effect) := by
  cases typed
  case slotInit slotAt valueAt => exact .slotInit _ _ _ _ (slots ▸ slotAt) (values ▸ valueAt)
  case store ownerAt valueAt => exact .store _ _ _ _ _ (values ▸ ownerAt) (values ▸ valueAt)
  all_goals exact .effect _ (by intro slot value origin same; cases same) (by intro address value origin same; cases same)

private theorem finished_edge {state : LS} {func : Func} {types : Array (Option VTy)}
    {target : BlockId} {args : List ValueId}
    (blocks : func.blocks = finishBlocks state.blocks) (values : types = state.vals)
    (size : func.numValues = state.vals.size) (parameters : EmittedParametersTyped state)
    (edge : EdgeArguments state target args) :
    ∃ block, func.blocks[target]? = some block ∧
      (∀ parameter argument, (parameter, argument) ∈ block.params.zip args →
        types[parameter.1]? = types[argument]? ∧ argument < func.numValues) ∧
      ∀ parameter ∈ block.params, parameter.1 < func.numValues := by
  obtain ⟨block, row, arity, typed⟩ := edge
  refine ⟨⟨block.params, block.insts.toList⟩, ?_, ?_, ?_⟩
  · simp [blocks, finishBlocks, Array.getElem?_map, row]
  · intro parameter argument member
    have argumentAt := typed (parameter, argument) member
    have parameterMember : parameter ∈ block.params := (List.of_mem_zip member).1
    have parameterAt := parameters target block row parameter.1 parameter.2 parameterMember
    exact ⟨by rw [values, parameterAt, argumentAt], size ▸ (Array.getElem?_eq_some_iff.mp argumentAt).1⟩
  · intro parameter member
    have parameterAt := parameters target block row parameter.1 parameter.2 member
    exact size ▸ (Array.getElem?_eq_some_iff.mp parameterAt).1

private theorem term_typing {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {le : LEnv} {state : LS} {term : Term}
    (blocks : func.blocks = finishBlocks state.blocks) (values : types = state.vals)
    (size : func.numValues = state.vals.size) (results : func.results = le.results)
    (parameters : EmittedParametersTyped state) (edge : BuilderTermArguments state term)
    (typed : EmittedTermTyped le.results state term) : InstructionTyping module func types (.term term) := by
  cases typed with
  | br target args =>
    obtain ⟨block, row, typed, bounds⟩ := finished_edge blocks values size parameters edge
    exact .branch target args block row typed bounds
  | condbr conditionAt =>
    obtain ⟨thenBlock, thenAt, thenTypes, thenBounds⟩ := finished_edge blocks values size parameters edge.1
    obtain ⟨elseBlock, elseAt, elseTypes, elseBounds⟩ := finished_edge blocks values size parameters edge.2
    exact .conditional _ _ _ _ _ thenBlock elseBlock thenAt elseAt thenTypes elseTypes thenBounds elseBounds
  | ret typed =>
    rename_i returned origin
    cases returned with
    | nil => exact .terminal _ (by intro a b same; cases same) (by intro a b c d e same; cases same) (by intro a b same; cases same)
    | cons value rest =>
      cases rest with
      | nil =>
        generalize resultEq : le.results = resultTypes at typed
        cases typed with
        | cons row tail =>
          cases tail
          exact .returned value origin _ (results.trans resultEq) (values ▸ row)
      | cons second rest =>
        exact .terminal _ (by intro a b same; cases same) (by intro a b c d e same; cases same) (by intro a b same; cases same)
  | exit valueAt => exact .terminal _ (by intro a b same; cases same) (by intro a b c d e same; cases same) (by intro a b same; cases same)
  | abort kind origin => exact .terminal _ (by intro a b same; cases same) (by intro a b c d e same; cases same) (by intro a b same; cases same)
  | unreachable => exact .terminal _ (by intro a b same; cases same) (by intro a b c d e same; cases same) (by intro a b same; cases same)

private theorem finished_instruction_typing {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {le : LEnv} {state : LS}
    (blocks : func.blocks = finishBlocks state.blocks) (values : types = state.vals)
    (size : func.numValues = state.vals.size) (results : func.results = le.results) (slots : func.slots = le.slots)
    (builder : EmittedParametersTyped state) (edges : BuilderEdgeArguments state)
    (metadata : EmittedMetadata le state)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      checkInstTypes func {module.tyEnv func with vals := types} types (.def value op) = .ok ()) :
    ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts, InstructionTyping module func types instruction := by
  intro block member instruction instructionMember
  cases instruction with
  | «def» value op => exact definition_typing (definitions block member value op instructionMember)
  | eff effect => exact effect_typing slots values (metadata.finishedInst blocks member instructionMember)
  | term term =>
    have sourceMember := member
    rw [blocks, finishBlocks, Array.toList_map] at sourceMember
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp sourceMember
    obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp originalMember)
    have edge := edges index original row (.term term) (by simpa only [← same] using instructionMember)
    exact term_typing blocks values size results builder edge (metadata.finishedInst blocks member instructionMember)

theorem lowerContext_instructionCanonicalFacts_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Core.Impl}
    (contextAt : module.contexts[index]? = some context) (implAt : module.impls[context.impl]? = some impl) :
    ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ instruction ∈ block.insts,
      InstructionTyping (lower module) (lowerContextAt module context impl)
        ((lowerContextAt module context impl).valueTypes (lower module)) instruction := by
  apply finished_instruction_typing (state := cfg_implState module impl) (le := lowerEnv module impl.vars impl.results.toList)
    (cfg_context_blocks module context impl) (lowerContext_valueTypes_of_accepted accepted implAt) (by
      rw [Func.numValues_eq_definition_count, cfg_context_blocks, finishBlocks_defs]
      exact (lowerImpl_emittedBuilder_of_accepted accepted implAt).checkpoint.dense.length) rfl rfl
    (lowerImpl_emittedBuilder_of_accepted accepted implAt).checkpoint.parameters
    (lowerImpl_builderEdges_of_accepted accepted implAt) (lowerContext_metadata_of_accepted accepted contextAt implAt)
  intro block member value op instructionMember
  exact lowerContext_definition_typed_of_accepted accepted implAt member instructionMember

theorem lowerGlobal_instructionCanonicalFacts_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global) :
    ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ instruction ∈ block.insts,
      InstructionTyping (lower module) (lowerGlobal module global).init
        ((lowerGlobal module global).init.valueTypes (lower module)) instruction := by
  apply finished_instruction_typing (state := cfg_globalState module global) (le := lowerEnv module #[] [global.ty])
    (cfg_global_blocks module global) (lowerGlobal_valueTypes_of_accepted accepted globalAt) (by
      rw [Func.numValues_eq_definition_count, cfg_global_blocks, finishBlocks_defs]
      exact (lowerGlobal_emittedBuilder_of_accepted accepted globalAt).checkpoint.dense.length) rfl rfl
    (lowerGlobal_emittedBuilder_of_accepted accepted globalAt).checkpoint.parameters
    (lowerGlobal_builderEdges_of_accepted accepted globalAt) (lowerGlobal_metadata_of_accepted accepted globalAt)
  intro block member value op instructionMember
  exact lowerGlobal_definition_typed_of_accepted accepted globalAt member instructionMember

#print axioms lowerContext_instructionCanonicalFacts_of_accepted
#print axioms lowerGlobal_instructionCanonicalFacts_of_accepted

end Goose.Lower.Validation
