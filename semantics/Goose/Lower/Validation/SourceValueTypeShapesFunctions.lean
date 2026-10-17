import Goose.Lower.Validation.SourceValueTypeShapesLowering
import Goose.Lower.Validation.SourceValueTypeShapesTyping
import Goose.Lower.Validation.ValidationTypedModuleTables
import Goose.Lower.Validation.SourceValueTypeShapesTables

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem shaped_finishFunction {module : Core.Module} {le : LEnv}
    (tables : ShapeTables module le) (impl : Core.Impl) (value : ValueId) :
    EmittedShapeRun module le (finishFunction impl value) := by
  unfold finishFunction
  refine EmittedShapeRun.bind (shaped_read module le) fun env => ?_
  refine EmittedShapeRun.bind (shaped_isLive tables) fun live => ?_
  split
  · split
    · refine EmittedShapeRun.bind (shaped_newBlock [] (by simp)) fun allocated => ?_
      refine EmittedShapeRun.bind (shaped_emitTerm _) fun _ => ?_
      refine EmittedShapeRun.bind (shaped_setCur module le _) fun _ => ?_
      exact shaped_emitTerm _
    · exact shaped_emitTerm _
  · exact EmittedShapeRun.pure module le _

private theorem lowerImpl_shaped_of_annotations {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) (annotations : ShapeBlockAnnotations module impl.body) :
    EmittedShapeState module (cfg_implState module impl) := by
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let allocated := newBlock types le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let pre : List (SlotId × ValueId × OriginId) := (impl.params.toList.zip allocated.1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
  let output := lowerBlock none pre false impl.body le selected.2
  have structTables := (validate_modOk module accepted).structTables
  have readable : SourceReadableEnvironment (implEnv module impl) :=
    SourceReadableEnvironment.implementation accepted row rfl
  have variables : ∀ localVar ∈ impl.vars.toList, localVar.ty.paramOk = true := by
    intro localVar member
    obtain ⟨position, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact readable.variables position localVar lookup
  have tables : ShapeTables module le := shaped_lowerEnv_tables accepted variables _
  have parameterTypes : ∀ type ∈ types, ValueTypeShape type := by
    intro type member
    obtain ⟨parameter, parameterMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨position, lookup⟩ := List.mem_iff_getElem?.mp parameterMember
    have lookup : impl.params[position]? = some parameter := by simpa only [Array.getElem?_toList] using lookup
    obtain ⟨identity, localVar, variableAt, _, allowed⟩ :=
      ((validate_modOk module accepted).impl index impl row).params position parameter lookup
    apply dataTypeShape_of_paramOk
    simpa only [tyOfVar, identity, variableAt, Option.map_some, Option.getD_some] using allowed
  have allocatedShape : EmittedShapeState module allocated.2 :=
    shaped_newBlock (le := le) types parameterTypes _ _ _ rfl (EmittedShapeState.initState module)
  have selectedShape : EmittedShapeState module selected.2 :=
    shaped_setCur module le _ _ _ _ rfl allocatedShape
  have outputShape : EmittedShapeState module output.2 :=
    shaped_lowerBlock tables none pre false impl.body annotations _ _ _ rfl selectedShape
  let final := finishFunction impl output.1 le output.2
  have finished : EmittedShapeState module final.2 :=
    shaped_finishFunction tables impl output.1 output.2 final.1 final.2 rfl outputShape
  simpa only [cfg_implState, cfg_implAction, bind_run, le, types, allocated, selected, pre, output, final] using finished

private theorem lowerGlobal_shaped_of_annotations {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) (annotations : ShapeExprAnnotations module global.init) :
    EmittedShapeState module (cfg_globalState module global) := by
  let le := lowerEnv module #[] [global.ty]
  let allocated := newBlock [] le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let output := lowerExpr global.init le selected.2
  have tables : ShapeTables module le := shaped_lowerEnv_tables (vars := #[]) accepted
    (by intro localVar member; cases member) _
  have allocatedShape : EmittedShapeState module allocated.2 :=
    shaped_newBlock (le := le) [] (by simp) _ _ _ rfl (EmittedShapeState.initState module)
  have selectedShape : EmittedShapeState module selected.2 :=
    shaped_setCur module le _ _ _ _ rfl allocatedShape
  have outputShape : EmittedShapeState module output.2 :=
    shaped_lowerExpr tables global.init annotations _ _ _ rfl selectedShape
  let final := emitTerm (.ret [output.1] (some global.org)) le output.2
  have finished : EmittedShapeState module final.2 :=
    shaped_emitTerm (le := le) (.ret [output.1] (some global.org)) output.2 final.1 final.2 rfl outputShape
  simpa only [cfg_globalState, cfg_globalAction, bind_run, le, allocated, selected, output, final] using finished

theorem lowerImpl_shaped_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    EmittedShapeState module (cfg_implState module impl) := by
  obtain ⟨type, finish, source, _⟩ := ((validate_modOk module accepted).impl index impl row).body
  exact lowerImpl_shaped_of_annotations accepted row
    (shape_tyBlock_annotations impl.body (implEnv module impl) source (validate_modOk module accepted).structTables)

theorem lowerGlobal_shaped_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) :
    EmittedShapeState module (cfg_globalState module global) := by
  obtain ⟨finish, source⟩ := ((validate_modOk module accepted).glob index global row).init
  exact lowerGlobal_shaped_of_annotations accepted row
    (shape_tyExpr_annotations global.init (initEnv module index) source (validate_modOk module accepted).structTables)

theorem lowerImpl_valueTypeShapes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    ValueTypeShapes ((lowerImpl module impl).valueTypes (lower module)) := by
  rw [lowerImpl_valueTypes_of_accepted accepted row]
  exact (lowerImpl_shaped_of_accepted accepted row).values

theorem lowerContext_valueTypeShapes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {context : Context} {impl : Core.Impl} {index : Nat}
    (row : module.impls[index]? = some impl) :
    ValueTypeShapes ((lowerContextAt module context impl).valueTypes (lower module)) := by
  rw [lowerContext_valueTypes_of_accepted accepted row]
  exact (lowerImpl_shaped_of_accepted accepted row).values

theorem lowerGlobal_valueTypeShapes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (row : module.globals[index]? = some global) :
    ValueTypeShapes ((lowerGlobal module global).init.valueTypes (lower module)) := by
  rw [lowerGlobal_valueTypes_of_accepted accepted row]
  exact (lowerGlobal_shaped_of_accepted accepted row).values

#print axioms lowerContext_valueTypeShapes_of_accepted
#print axioms lowerGlobal_valueTypeShapes_of_accepted

end Goose.Lower.Validation
