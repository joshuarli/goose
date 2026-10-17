import Goose.Lower.Validation.ValueTypeReconstructionSourceReadiness
import Goose.Lower.Validation.ValueTypeReconstructionGenerated
import Goose.Lower.Validation.EmittedTypingCheckpoints
import Goose.Lower.Validation.FunctionTables

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def MutableSnapshotGraphs (module : GIR.Module) (func : Func) (state : LS) : Prop :=
  ∀ value mode owner, .def value (.snapshot mode owner) ∈ state.insts →
    ∀ element, emittedValueType state value = .view .mutable element →
    ∃ authorized, ContentsClosed (module.globals.map (·.kind)) module.structs
      func state.vals authorized ∧ authorized owner ∧
      ∀ candidate, authorized candidate → candidate < value

private theorem emittedValueType_lookup {state : LS} (present : EmittedTypesPresent state)
    {value : ValueId} (bound : value < state.vals.size) :
    state.vals[value]? = some (some (emittedValueType state value)) := by
  obtain ⟨type, row⟩ := present value bound
  simp only [emittedValueType, row, Option.getD_some]

private theorem snapshot_mutable_of_contents {env : TyEnv} {mode : SnapshotMode}
    {owner : ValueId} {type : VTy}
    (typed : (Op.snapshot mode owner).resultTy env = .ok type)
    (allowed : env.contentsWritable owner = some true) :
    ∃ element, type = .view .mutable element := by
  simp only [Op.resultTy, allowed, Option.getD_some, ite_true] at typed
  cases reference : env.refTy owner with
  | error error => simp [reference, bind, Except.bind] at typed
  | ok pair =>
    simp only [reference, bind, Except.bind] at typed
    cases shape : arrayElem? pair.2 with
    | none => simp [shape, tyErr] at typed
    | some element =>
      simp only [shape, pure, Except.pure] at typed
      exact ⟨element, (Except.ok.inj typed).symm⟩

def ReconstructionEmissionSite (le : LEnv) (state : LS) (module : GIR.Module)
    (func : Func) (value : ValueId) (op : Op) : Prop :=
  ∃ site block, EmittedTrace le initState site ∧ EmittedCheckpoint site ∧ site.Ext state ∧
    site.cur = some block ∧ value = site.vals.size ∧
    op.resultTy (tyEnv le site) = .ok (emittedValueType state value) ∧
    (∀ operand, operand < site.vals.size →
      site.vals[operand]? = some (some (emittedValueType state operand))) ∧
    (∀ mode owner, op = .snapshot mode owner →
      (tyEnv le site).contentsWritable owner = some true →
      SnapshotAuthorityRetained site module func owner)

theorem reconstructionEmissionSite_nonsnapshot
    {le : LEnv} {state : LS} {module : GIR.Module} {func : Func}
    {value : ValueId} {op : Op}
    (witness : EmittedCheckedSite le initState state value op)
    (nonsnapshot : ∀ mode owner, op ≠ .snapshot mode owner) :
    ReconstructionEmissionSite le state module func value op := by
  obtain ⟨site, block, trace, checkpoint, extension, live, fresh, success, recorded, prefixTypes⟩ :=
    witness.operation (by intro value bound; exact (Nat.not_lt_zero value bound).elim)
  exact ⟨site, block, trace, checkpoint, extension, live, fresh, success, prefixTypes,
    fun mode owner snapshot _ => (nonsnapshot mode owner snapshot).elim⟩

private theorem readonly_snapshot_forbids_contents {env : TyEnv} {mode : SnapshotMode}
    {owner : ValueId} {element : Ty}
    (typed : (Op.snapshot mode owner).resultTy env = .ok (.view .readOnly element)) :
    env.contentsWritable owner ≠ some true := by
  intro allowed
  simp only [Op.resultTy, allowed, Option.getD_some, ite_true] at typed
  cases reference : env.refTy owner with
  | error error => simp [reference, bind, Except.bind] at typed
  | ok pair =>
    simp only [reference, bind, Except.bind] at typed
    cases shape : arrayElem? pair.2 with
    | none => simp [shape, tyErr] at typed
    | some actual => simp [shape, pure, Except.pure] at typed

theorem reconstructionEmissionSite_readonly_snapshot
    {le : LEnv} {state : LS} {module : GIR.Module} {func : Func}
    {value : ValueId} {mode : SnapshotMode} {owner : ValueId} {element : Ty}
    (witness : EmittedCheckedSite le initState state value (.snapshot mode owner))
    (expected : emittedValueType state value = .view .readOnly element) :
    ReconstructionEmissionSite le state module func value (.snapshot mode owner) := by
  obtain ⟨site, block, trace, checkpoint, extension, live, fresh, success, recorded, prefixTypes⟩ :=
    witness.operation (by intro value bound; exact (Nat.not_lt_zero value bound).elim)
  refine ⟨site, block, trace, checkpoint, extension, live, fresh, success, prefixTypes, ?_⟩
  intro actualMode actualOwner snapshot contents
  obtain ⟨rfl, rfl⟩ := Op.snapshot.inj snapshot
  exact (readonly_snapshot_forbids_contents (by simpa only [expected] using success) contents).elim

theorem reconstructionEmissionSite_of_source_graph
    {le : LEnv} {state : LS} {module : GIR.Module} {func : Func}
    (builder : EmittedBuilder le initState state)
    (graphs : MutableSnapshotGraphs module func state)
    {value : ValueId} {op : Op} (definition : .def value op ∈ state.insts) :
    ReconstructionEmissionSite le state module func value op := by
  have initialPresent : EmittedTypesPresent initState := by
    intro value bound
    exact (Nat.not_lt_zero value bound).elim
  obtain ⟨site, block, trace, checkpoint, extension, live, fresh, success, recorded, prefixTypes⟩ :=
    (builder.sites value op definition).operation initialPresent
  refine ⟨site, block, trace, checkpoint, extension, live, fresh, success, prefixTypes, ?_⟩
  intro mode owner snapshot writable
  have snapshotTyped : (Op.snapshot mode owner).resultTy (tyEnv le site) =
      .ok (emittedValueType state value) := by rwa [snapshot] at success
  obtain ⟨element, shape⟩ := snapshot_mutable_of_contents snapshotTyped writable
  obtain ⟨authorized, closed, member, bounded⟩ :=
    graphs value mode owner (by rwa [snapshot] at definition) element shape
  apply snapshotAuthorityRetained_of_graph closed
    (fun candidate allowed => by rw [← fresh]; exact bounded candidate allowed) ?_ member
  intro candidate allowed
  have oldBound : candidate < site.vals.size := by rw [← fresh]; exact bounded candidate allowed
  have finalBound := Nat.lt_trans (bounded candidate allowed) (Array.getElem?_eq_some_iff.mp recorded).1
  exact (emittedValueType_lookup (builder.present initialPresent) finalBound).trans (prefixTypes candidate oldBound).symm

theorem valueTypes_eq_retained_of_emission_sites
    {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun g => (g.ty, g.kind)) = le.globals)
    (sigs : (module.funcs.map fun h => (h.params, h.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (sites : ∀ value op, .def value op ∈ state.insts →
      ReconstructionEmissionSite le state module func value op) :
    func.valueTypes module = state.vals := by
  have count : func.numValues = state.vals.size := by
    rw [Func.numValues_eq_definition_count, blocks, finishBlocks_defs]
    exact builder.checkpoint.dense.length
  have dense := dense_finishBlocks builder.checkpoint.dense blocks
  have present : EmittedTypesPresent state := builder.present (by
    intro value bound
    change value < 0 at bound
    exact (Nat.not_lt_zero _ bound).elim)
  have recorded : ∀ value, value < state.vals.size →
      state.vals[value]? = some (some (emittedValueType state value)) := by
    intro value bound
    obtain ⟨type, row⟩ := present value bound
    simp only [emittedValueType, row, Option.getD_some]
  have extended : ExtT state func.blocks := by
    rw [blocks]
    refine ⟨by simp [finishBlocks], ?_⟩
    intro index block row
    refine ⟨⟨block.params, block.insts.toList⟩, ?_, rfl, [], by simp⟩
    simp [finishBlocks, Array.getElem?_map, row]
  apply valueTypes_ranked_eq_recorded (rankedReconstruction_of_dense dense ?_ ?_) count.symm recorded
  · intro block member value ty parameter
    rw [blocks, finishBlocks, Array.toList_map] at member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨index, sourceRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp sourceMember)
    have row := builder.checkpoint.parameters index source sourceRow value ty parameter
    simp only [emittedValueType, row, Option.getD_some]
  · intro block member value op definition
    rw [blocks, finishBlocks, Array.toList_map] at member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    have rawDefinition : .def value op ∈ state.insts := List.mem_flatMap.mpr
      ⟨source, sourceMember, definition⟩
    obtain ⟨site, current, trace, checkpoint, grows, live, fresh, typed, prefixTypes, authority⟩ :=
      sites value op rawDefinition
    have valueBound : value < func.numValues := by
      rw [count]
      apply builder.checkpoint.dense.mem_lt
      exact List.mem_flatMap.mpr ⟨source, sourceMember, List.mem_append_right _
        (List.mem_filterMap.mpr ⟨.def value op, definition, rfl⟩)⟩
    exact reconstructionReady_of_source_emission slots globals sigs structs profile
      checkpoint.dense (extended.of_ext grows) checkpoint.operands.uses fresh valueBound
      prefixTypes typed (builder.checkpoint.operands.definitions value op rawDefinition) authority

theorem valueTypes_eq_retained_of_source_graphs
    {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun g => (g.ty, g.kind)) = le.globals)
    (sigs : (module.funcs.map fun h => (h.params, h.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state) :
    func.valueTypes module = state.vals :=
  valueTypes_eq_retained_of_emission_sites builder blocks slots globals sigs structs profile
    (fun _ _ definition => reconstructionEmissionSite_of_source_graph builder graphs definition)

theorem lowerImpl_valueTypes_eq_retained
    {module : Core.Module} {impl : Core.Impl} {state : LS}
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState state)
    (blocks : (lowerImpl module impl).blocks = finishBlocks state.blocks)
    (graphs : MutableSnapshotGraphs (lower module) (lowerImpl module impl) state) :
    (lowerImpl module impl).valueTypes (lower module) = state.vals :=
  valueTypes_eq_retained_of_source_graphs builder blocks rfl
    (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl graphs

theorem lowerContextAt_valueTypes_eq_retained
    {module : Core.Module} {ctx : Context} {impl : Core.Impl} {state : LS}
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState state)
    (blocks : (lowerContextAt module ctx impl).blocks = finishBlocks state.blocks)
    (graphs : MutableSnapshotGraphs (lower module) (lowerContextAt module ctx impl) state) :
    (lowerContextAt module ctx impl).valueTypes (lower module) = state.vals :=
  valueTypes_eq_retained_of_source_graphs builder blocks rfl
    (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl graphs

theorem lowerGlobal_valueTypes_eq_retained
    {module : Core.Module} {global : Core.Global} {state : LS}
    (builder : EmittedBuilder (lowerEnv module #[] [global.ty]) initState state)
    (blocks : (lowerGlobal module global).init.blocks = finishBlocks state.blocks)
    (graphs : MutableSnapshotGraphs (lower module) (lowerGlobal module global).init state) :
    (lowerGlobal module global).init.valueTypes (lower module) = state.vals :=
  valueTypes_eq_retained_of_source_graphs builder blocks rfl
    (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl graphs

end Goose.Lower.Validation
