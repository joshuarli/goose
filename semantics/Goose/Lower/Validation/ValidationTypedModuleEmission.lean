import Goose.Lower.Validation.ValidationTypedModuleReturns
import Goose.Lower.Validation.EmittedMetadataSource
import Goose.Lower.Validation.EmittedMetadataParameters

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerGlobal_metadata_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) :
    EmittedMetadata (lowerEnv module #[] [global.ty]) (cfg_globalState module global) := by
  obtain ⟨finish, source⟩ := ((validate_modOk module accepted).glob index global row).init
  let le := lowerEnv module #[] [global.ty]
  let allocated := newBlock [] le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let output := lowerExpr global.init le selected.2
  have allocatedMetadata := (EmittedMetadata.initState le).newBlock []
  have allocatedGenerated : GeneratedBuilderState allocated.2 :=
    GeneratedBuilderState.initState.newBlock (env := le) [] rfl
  have fresh : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
  have selectedBound : ∀ block, some allocated.1.1 = some block → block < allocated.2.blocks.size := by
    intro block same
    cases Option.some.inj same
    exact fresh
  have selectedMetadata := allocatedMetadata.setCur (some allocated.1.1)
  have selectedGenerated : GeneratedBuilderState selected.2 :=
    allocatedGenerated.setCur (env := le) _ selectedBound rfl
  have outputMetadata := metadata_source_expression global.init (initEnv module index) [global.ty]
    (by intro impl same; simp [initEnv] at same) source selected.2 output.1 output.2
    selectedGenerated trivial trivial rfl selectedMetadata
  have finished := outputMetadata.emitTerm (.ret [output.1] (some global.org)) (by
    intro live
    exact .ret (.cons (lowerExpr_generated_typed global.init source rfl live selectedGenerated) .nil))
  simpa only [cfg_globalState, cfg_globalAction, bind_run, initEnv, le, allocated, selected, output] using finished

theorem lowerContext_metadata_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {context : Context} {contextIndex : Nat}
    (contextAt : module.contexts[contextIndex]? = some context) {impl : Core.Impl}
    (implAt : module.impls[context.impl]? = some impl) :
    EmittedMetadata (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl) := by
  obtain ⟨type, finish, source, _⟩ := ((validate_modOk module accepted).impl context.impl impl implAt).body
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let allocated := newBlock types le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let pre : List (SlotId × ValueId × OriginId) := (impl.params.toList.zip allocated.1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
  let output := lowerBlock none pre false impl.body le selected.2
  have allocatedMetadata := (EmittedMetadata.initState le).newBlock types
  have allocatedGenerated : GeneratedBuilderState allocated.2 :=
    GeneratedBuilderState.initState.newBlock (env := le) types rfl
  have fresh : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
  have selectedBound : ∀ block, some allocated.1.1 = some block → block < allocated.2.blocks.size := by
    intro block same
    cases Option.some.inj same
    exact fresh
  have selectedMetadata := allocatedMetadata.setCur (some allocated.1.1)
  have selectedGenerated : GeneratedBuilderState selected.2 :=
    allocatedGenerated.setCur (env := le) _ selectedBound rfl
  have preTyped : EmittedPreTyped le selected.2 pre := lowerImpl_entry_pretyped_of_accepted accepted implAt
  have outputMetadata := metadata_source_block impl.body (implEnv module impl) impl.results.toList
    (by intro found same; cases Option.some.inj same; rfl) source none pre false selected.2 output.1 output.2
    selectedGenerated trivial trivial preTyped rfl selectedMetadata
  have finished := outputMetadata.finishFunction impl output.1 rfl
    (fun tail live => lowerContext_tail_values_of_accepted accepted contextAt implAt pre false rfl live selectedGenerated tail)
    (accepted_implementation_no_tail accepted implAt)
  simpa only [cfg_implState, cfg_implAction, bind_run, implEnv, le, types, allocated, selected, pre, output] using finished

end Goose.Lower.Validation
