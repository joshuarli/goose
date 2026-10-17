import Goose.Lower.Validation.StorageSourceAccepted
import Goose.Lower.Validation.StorageSourceReconstruction
import Goose.Lower.Validation.Entry
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

attribute [local irreducible] StorageAt

theorem StorageBuilder.initState (profile : ArtifactProfile) : StorageBuilder profile Goose.Lower.initState := by
  intro instruction member
  simp [Goose.Lower.initState, LS.insts] at member

theorem StorageAt.startBlock_generated {le : LEnv} {before : LS} (types : List VTy)
    {tail : BlockId → List ValueId → B α} (generated : GeneratedBuilderState before)
    (child : ∀ block parameters state, GeneratedBuilderState state → block < state.blocks.size →
      StorageAt le state (tail block parameters)) :
    StorageAt le before (do
      let (block, parameters) ← Goose.Lower.newBlock types
      Goose.Lower.setCur (some block)
      tail block parameters) := by
  let allocated := Goose.Lower.newBlock types le before
  let entered := Goose.Lower.setCur (some allocated.1.1) le allocated.2
  have allocatedGenerated := generated.newBlock types
    (show Goose.Lower.newBlock types le before = allocated from rfl)
  have id : allocated.1.1 = before.blocks.size := by simp [allocated, newBlock_run_general]
  have size : allocated.2.blocks.size = before.blocks.size + 1 := by simp [allocated, newBlock_run_general]
  have bound : allocated.1.1 < allocated.2.blocks.size := by rw [id, size]; nat_omega
  have enteredGenerated := allocatedGenerated.setCur (some allocated.1.1)
    (by intro current same; cases same; exact bound)
    (show Goose.Lower.setCur _ le allocated.2 = entered from rfl)
  apply (StorageAt.newBlock _ _ _).bind
  apply (StorageAt.setCur _ _ _).bind
  exact child allocated.1.1 allocated.1.2 entered.2 enteredGenerated bound

theorem StorageAt.finishFunction (le : LEnv) (before : LS) (impl : Core.Impl) (value : ValueId) :
    StorageAt le before (Goose.Lower.finishFunction impl value) := by
  unfold Goose.Lower.finishFunction
  apply (StorageAt.read _ _).bind
  apply (StorageAt.isLive _ _).bind
  split
  · split
    · exact (StorageAt.newBlock _ _ _).bind ((StorageAt.emitTerm _ _ _).bind
        ((StorageAt.setCur _ _ _).bind (StorageAt.emitTerm _ _ _)))
    · exact StorageAt.emitTerm _ _ _
  · exact StorageAt.pure _ _ _

def implementationStorageState (module : Core.Module) (impl : Core.Impl) : LS :=
  let action : B Unit := do
    let (entry, parameters) ← newBlock (impl.params.toList.map fun parameter => .data (tyOfVar impl parameter.var))
    setCur (some entry)
    let pre := (impl.params.toList.zip parameters).map fun (parameter, value) =>
      (parameter.var, value, (impl.vars[parameter.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  (action (lowerEnv module impl.vars impl.results.toList) initState).2

def globalStorageState (module : Core.Module) (global : Core.Global) : LS :=
  let action : B Unit := do
    let (entry, _) ← newBlock []
    setCur (some entry)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  (action (lowerEnv module #[] [global.ty]) initState).2

theorem lowerImpl_storage_builder {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (lookup : module.impls[index]? = some impl) :
    StorageBuilder module.profile (implementationStorageState module impl) := by
  have implementation := validate_implementation_checks accepted (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  obtain ⟨bodyType, finish, bodySource, _⟩ := (checkImpl_ok module impl implementation).body
  have sourceTypes : SourceReadableEnvironment (implEnv module impl) :=
    .implementation accepted lookup rfl
  have action : StorageAt (lowerEnv module impl.vars impl.results.toList) initState (do
      let (entry, parameters) ← newBlock (impl.params.toList.map fun parameter => .data (tyOfVar impl parameter.var))
      setCur (some entry)
      let pre := (impl.params.toList.zip parameters).map fun (parameter, value) =>
        (parameter.var, value, (impl.vars[parameter.var]?.map (·.org)).getD 0)
      let value ← lowerBlock none pre false impl.body
      finishFunction impl value) := by
    let le := lowerEnv module impl.vars impl.results.toList
    let allocated := newBlock (impl.params.toList.map fun parameter => .data (tyOfVar impl parameter.var)) le initState
    let entered := setCur (some allocated.1.1) le allocated.2
    have allocatedGenerated : GeneratedBuilderState allocated.2 := GeneratedBuilderState.initState.newBlock _
      (show newBlock _ le initState = allocated from rfl)
    have entryBound : allocated.1.1 < allocated.2.blocks.size := by
      simp [allocated, newBlock_run_general, initState]
    have current : GeneratedBuilderState entered.2 := allocatedGenerated.setCur (some allocated.1.1)
      (by intro target same; cases same; exact entryBound)
      (show setCur _ le allocated.2 = entered from rfl)
    apply (StorageAt.newBlock _ _ _).bind
    apply (StorageAt.setCur _ _ _).bind
    exact (storage_lowerBlock impl.body sourceTypes bodySource impl.results.toList none _ false current trivial).bind
      (StorageAt.finishFunction _ _ _ _)
  unfold StorageAt at action
  exact action (StorageBuilder.initState _)

theorem lowerGlobal_storage_builder {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (lookup : module.globals[index]? = some global) :
    StorageBuilder module.profile (globalStorageState module global) := by
  obtain ⟨_, finish, source⟩ := checkGlobal_ok module index global (validate_global_checks accepted lookup)
  have sourceTypes : SourceReadableEnvironment (initEnv module index) := .empty accepted rfl
  have action : StorageAt (lowerEnv module #[] [global.ty]) initState (do
      let (entry, _) ← newBlock []
      setCur (some entry)
      let value ← lowerExpr global.init
      emitTerm (.ret [value] (some global.org))) := by
    refine StorageAt.startBlock_generated (α := Unit)
      (le := lowerEnv module #[] [global.ty]) (before := initState)
      (tail := fun _ _ => do
        let value ← lowerExpr global.init
        emitTerm (.ret [value] (some global.org))) [] GeneratedBuilderState.initState ?_
    intro entry parameters state current bound
    exact (storage_lowerExpr global.init sourceTypes source [global.ty] current).bind (StorageAt.emitTerm _ _ _)
  unfold StorageAt at action
  exact action (StorageBuilder.initState _)

theorem lowerImpl_source_storage_rules {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (lookup : module.impls[index]? = some impl) :
    ∀ block ∈ (lowerImpl module impl).blocks.toList, ∀ instruction ∈ block.insts,
      StorageRule module.profile (implementationStorageState module impl).vals instruction :=
  (lowerImpl_storage_builder accepted lookup).finishBlocks
    (le := lowerEnv module impl.vars impl.results.toList) rfl

theorem lowerContextAt_source_storage_rules {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (lookup : module.impls[index]? = some impl) (context : Context) :
    ∀ block ∈ (lowerContextAt module context impl).blocks.toList, ∀ instruction ∈ block.insts,
      StorageRule module.profile (implementationStorageState module impl).vals instruction :=
  lowerImpl_source_storage_rules accepted lookup

theorem lowerGlobal_source_storage_rules {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (lookup : module.globals[index]? = some global) :
    ∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ instruction ∈ block.insts,
      StorageRule module.profile (globalStorageState module global).vals instruction :=
  (lowerGlobal_storage_builder accepted lookup).finishBlocks
    (le := lowerEnv module #[] [global.ty]) rfl

theorem lowerImpl_source_checkStorage {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (lookup : module.impls[index]? = some impl)
    (emitted : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState
      (implementationStorageState module impl))
    (graphs : MutableSnapshotGraphs (lower module) (lowerImpl module impl) (implementationStorageState module impl))
    (label : String) : checkStorage (lower module) label (lowerImpl module impl)
      ((lowerImpl module impl).valueTypes (lower module)) = .ok () :=
  lowerImpl_checkStorage_of_source_graphs (lowerImpl_storage_builder accepted lookup) emitted rfl graphs label

theorem lowerContextAt_source_checkStorage {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (lookup : module.impls[index]? = some impl) (context : Context)
    (emitted : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState
      (implementationStorageState module impl))
    (graphs : MutableSnapshotGraphs (lower module) (lowerContextAt module context impl) (implementationStorageState module impl))
    (label : String) : checkStorage (lower module) label (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () :=
  (lowerImpl_storage_builder accepted lookup).checkStorage
    (le := lowerEnv module impl.vars impl.results.toList) rfl rfl
    (lowerContextAt_valueTypes_eq_retained emitted rfl graphs) label

theorem lowerGlobal_source_checkStorage {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (lookup : module.globals[index]? = some global)
    (emitted : EmittedBuilder (lowerEnv module #[] [global.ty]) initState (globalStorageState module global))
    (graphs : MutableSnapshotGraphs (lower module) (lowerGlobal module global).init (globalStorageState module global))
    (label : String) : checkStorage (lower module) label (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () :=
  (lowerGlobal_storage_builder accepted lookup).checkStorage
    (le := lowerEnv module #[] [global.ty]) rfl rfl
    (lowerGlobal_valueTypes_eq_retained emitted rfl graphs) label

#print axioms lowerImpl_storage_builder
#print axioms lowerGlobal_storage_builder
#print axioms lowerImpl_source_storage_rules
#print axioms lowerGlobal_source_storage_rules
#print axioms lowerImpl_source_checkStorage
#print axioms lowerContextAt_source_checkStorage
#print axioms lowerGlobal_source_checkStorage

end Goose.Lower.Validation
