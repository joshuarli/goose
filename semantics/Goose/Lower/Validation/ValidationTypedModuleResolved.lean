import Goose.Lower.Validation.EmittedMetadataStaticLowering
import Goose.Lower.Validation.EmittedMetadataStaticTyping
import Goose.Lower.Validation.ValidationTypedModuleTables
import Goose.Lower.Validation.ResolvedTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem resolved_finishFunction {module : Core.Module} {le : LEnv}
    (tables : EmittedStaticTables module le) (impl : Core.Impl) (value : ValueId) :
    EmittedResolvedRun module le (finishFunction impl value) := by
  unfold finishFunction
  refine EmittedResolvedRun.bind (resolved_read module le) fun env => ?_
  refine EmittedResolvedRun.bind (resolved_isLive tables) fun live => ?_
  split
  · split
    · refine EmittedResolvedRun.bind (resolved_newBlock [] (by simp)) fun allocated => ?_
      refine EmittedResolvedRun.bind (resolved_emitTerm _) fun _ => ?_
      refine EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => ?_
      exact resolved_emitTerm _
    · exact resolved_emitTerm _
  · exact EmittedResolvedRun.pure module le _

private theorem lowerImpl_resolved_of_annotations {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) (annotations : ResolvedBlockAnnotations module impl.body) :
    EmittedResolvedState module (cfg_implState module impl) := by
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let allocated := newBlock types le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let pre : List (SlotId × ValueId × OriginId) := (impl.params.toList.zip allocated.1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
  let output := lowerBlock none pre false impl.body le selected.2
  have structTables := (validate_modOk module accepted).structTables
  have variables := (checkStructTables_impl_resolved structTables
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row))).1
  have tables : EmittedStaticTables module le := static_lowerEnv_tables structTables variables _
  have parameterTypes : ∀ type ∈ types, EmittedVTyResolved module type := by
    intro type member
    obtain ⟨parameter, parameterMember, rfl⟩ := List.mem_map.mp member
    apply lowerImpl_interface_resolved accepted row
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨parameter, parameterMember, rfl⟩
  have allocatedResolved : EmittedResolvedState module allocated.2 :=
    resolved_newBlock (le := le) types parameterTypes _ _ _ rfl (EmittedResolvedState.initState module)
  have selectedResolved : EmittedResolvedState module selected.2 :=
    resolved_setCur module le _ _ _ _ rfl allocatedResolved
  have outputResolved : EmittedResolvedState module output.2 :=
    resolved_lowerBlock tables none pre false impl.body annotations _ _ _ rfl selectedResolved
  let final := finishFunction impl output.1 le output.2
  have finished : EmittedResolvedState module final.2 :=
    resolved_finishFunction tables impl output.1 output.2 final.1 final.2 rfl outputResolved
  simpa only [cfg_implState, cfg_implAction, bind_run, le, types, allocated, selected, pre, output, final] using finished

private theorem lowerGlobal_resolved_of_annotations {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) (annotations : ResolvedExprAnnotations module global.init) :
    EmittedResolvedState module (cfg_globalState module global) := by
  let le := lowerEnv module #[] [global.ty]
  let allocated := newBlock [] le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let output := lowerExpr global.init le selected.2
  have tables : EmittedStaticTables module le := static_lowerEnv_tables (vars := #[]) (validate_modOk module accepted).structTables
    (by intro localVar member; cases member) _
  have allocatedResolved : EmittedResolvedState module allocated.2 :=
    resolved_newBlock (le := le) [] (by simp) _ _ _ rfl (EmittedResolvedState.initState module)
  have selectedResolved : EmittedResolvedState module selected.2 :=
    resolved_setCur module le _ _ _ _ rfl allocatedResolved
  have outputResolved : EmittedResolvedState module output.2 :=
    resolved_lowerExpr tables global.init annotations _ _ _ rfl selectedResolved
  let final := emitTerm (.ret [output.1] (some global.org)) le output.2
  have finished : EmittedResolvedState module final.2 :=
    resolved_emitTerm (le := le) (.ret [output.1] (some global.org)) output.2 final.1 final.2 rfl outputResolved
  simpa only [cfg_globalState, cfg_globalAction, bind_run, le, allocated, selected, output, final] using finished

theorem lowerImpl_resolved_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    EmittedResolvedState module (cfg_implState module impl) := by
  obtain ⟨type, finish, source, _⟩ := ((validate_modOk module accepted).impl index impl row).body
  exact lowerImpl_resolved_of_annotations accepted row
    (static_tyBlock_annotations impl.body (implEnv module impl) source (validate_modOk module accepted).structTables)

theorem lowerGlobal_resolved_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) :
    EmittedResolvedState module (cfg_globalState module global) := by
  obtain ⟨finish, source⟩ := ((validate_modOk module accepted).glob index global row).init
  exact lowerGlobal_resolved_of_annotations accepted row
    (static_tyExpr_annotations global.init (initEnv module index) source (validate_modOk module accepted).structTables)

end Goose.Lower.Validation
