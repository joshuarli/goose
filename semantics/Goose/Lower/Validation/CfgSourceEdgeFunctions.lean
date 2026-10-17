import Goose.Lower.Validation.CfgSourceEdges
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem edge_newBlock_types (types : List VTy) : EdgeRun (newBlock types) := by
  intro env before result after run checked
  have extension : EdgeExtension before after := by
    refine ⟨?_, types_newBlock types env before result after run⟩
    rw [newBlock_run_general] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact (LS.Adv.newBlk before _ (by simp [array_size_pushParamTypes])).ext
  refine ⟨extension, ?_⟩
  intro index body row inst member
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  simp only [Array.getElem?_push] at row
  split at row
  · obtain rfl := Option.some.inj row
    simp at member
  · exact (checked index body row inst member).extend extension

theorem generated_edge_functionStart (env : LEnv) (types : List VTy) {body : List ValueId → B Unit}
    (bodyEdges : ∀ parameters, GeneratedEdgeRun env none (body parameters)) :
    GeneratedEdgeRun env none (do
      let (entry, parameters) ← newBlock types
      setCur (some entry)
      body parameters) := by
  intro before result after run generated loop checked
  simp only [bind_eq] at run
  obtain ⟨⟨entry, parameters⟩, allocated, allocateRun, ignored, selected, selectRun, bodyRun⟩ := run
  obtain ⟨allocatedExtension, allocatedChecked⟩ := edge_newBlock_types types env before _ allocated allocateRun checked
  have allocatedGenerated := generated.newBlock types allocateRun
  have bound : entry < allocated.blocks.size := by
    rw [newBlock_run_general] at allocateRun
    obtain ⟨equal, state⟩ := Prod.mk.inj allocateRun
    have entryEq := congrArg Prod.fst equal
    dsimp only at entryEq
    rw [state.symm, ← entryEq]
    simp
  obtain ⟨selectedGenerated, selectedExtension, selectedChecked⟩ :=
    generated_edge_setCur_at (some entry) env allocated selected ignored selectRun allocatedGenerated allocatedChecked
      (by intro target same; have equal := Option.some.inj same; simpa [← equal] using bound)
  obtain ⟨afterGenerated, bodyExtension, afterChecked⟩ := bodyEdges parameters selected result after bodyRun selectedGenerated trivial selectedChecked
  exact ⟨afterGenerated, allocatedExtension.trans (selectedExtension.trans bodyExtension), afterChecked⟩

theorem generated_edge_finishFunction (env : LEnv) (impl : Core.Impl) (value : ValueId) :
    GeneratedEdgeRun env none (finishFunction impl value) := by
  unfold finishFunction
  refine (generated_edge_read _ _).bind fun reader => (generated_edge_isLive _ _).bind fun live => ?_
  cases live
  · exact generated_edge_pure _ _ _
  · simp only [ite_true]
    split
    · apply generated_edge_emptyHeader _ none (body := fun sink => emitTerm (.br sink []))
      intro sink before result after run generated loop checked edge
      exact generated_edge_emitTerm_at (.br sink []) env before after result run generated checked edge
    · exact generated_edge_emitTerm _ _ _ (fun _ => trivial)

theorem BuilderEdgeArguments.initState : BuilderEdgeArguments initState := by
  intro index body row
  simp [Goose.Lower.initState] at row

theorem lowerImpl_builderEdges {module : Core.Module} {impl : Core.Impl} {type : Ty} {finish : Nat}
    (typed : Core.tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish)) :
    BuilderEdgeArguments (cfg_implState module impl) := by
  let env := lowerEnv module impl.vars impl.results.toList
  have actionEdges : GeneratedEdgeRun env none (cfg_implAction impl) := by
    apply generated_edge_functionStart env _ (body := fun parameters => do
      let pre := (impl.params.toList.zip parameters).map fun (param, value) =>
        (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
      let value ← lowerBlock none pre false impl.body
      finishFunction impl value)
    intro parameters
    exact (cfg_source_block_all impl.body (implEnv module impl) impl.results.toList typed none _ false).bind fun value =>
      generated_edge_finishFunction env impl value
  exact (actionEdges initState _ _ rfl .initState trivial .initState).2.2

theorem lowerGlobal_builderEdges {module : Core.Module} {global : Core.Global} {index finish : Nat}
    (typed : Core.tyExpr (initEnv module index) global.init 0 = .ok (global.ty, finish)) :
    BuilderEdgeArguments (cfg_globalState module global) := by
  let env := lowerEnv module #[] [global.ty]
  have actionEdges : GeneratedEdgeRun env none (cfg_globalAction global) := by
    apply generated_edge_functionStart env [] (body := fun _ => do
      let value ← lowerExpr global.init
      emitTerm (.ret [value] (some global.org)))
    intro parameters
    exact (cfg_source_expression global.init (initEnv module index) [global.ty] typed).bind fun value =>
      generated_edge_emitTerm _ _ (.ret [value] (some global.org)) (fun _ => trivial)
  exact (actionEdges initState _ _ rfl .initState trivial .initState).2.2

theorem lowerImpl_builderEdges_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {impl : Core.Impl} {index : Nat} (row : module.impls[index]? = some impl) :
    BuilderEdgeArguments (cfg_implState module impl) := by
  obtain ⟨type, finish, typed, _⟩ := ((validate_modOk module accepted).impl index impl row).body
  exact lowerImpl_builderEdges typed

theorem lowerGlobal_builderEdges_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {global : Core.Global} {index : Nat} (row : module.globals[index]? = some global) :
    BuilderEdgeArguments (cfg_globalState module global) := by
  obtain ⟨finish, typed⟩ := ((validate_modOk module accepted).glob index global row).init
  exact lowerGlobal_builderEdges typed

end Goose.Lower.Validation
