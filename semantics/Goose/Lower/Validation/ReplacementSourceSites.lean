import Goose.Lower.Validation.ReplacementSourceSitesAccepted
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Lower.Validation.Entry
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {targets : List BlockId}

attribute [local irreducible] ReplacementSitesAt

theorem ReplacementSitesBuilder.initState (le : LEnv) : ReplacementSitesBuilder (targets := targets) le Goose.Lower.initState := by
  intro block body row
  simp [Goose.Lower.initState] at row

theorem ReplacementSitesAt.startBlock_generated {le : LEnv} {before : LS} (types : List VTy)
    {tail : BlockId → List ValueId → B α} (generated : GeneratedBuilderState before)
    (child : ∀ block parameters state, GeneratedBuilderState state → block < state.blocks.size →
      ReplacementSitesAt (targets := targets) le state (tail block parameters)) :
    ReplacementSitesAt (targets := targets) le before (do
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
  apply (ReplacementSitesAt.newBlock _ _ _).bind
  apply (ReplacementSitesAt.setCur _ _ _).bind
  exact child allocated.1.1 allocated.1.2 entered.2 enteredGenerated bound

theorem ReplacementSitesAt.finishFunction (le : LEnv) (before : LS) (impl : Core.Impl) (value : ValueId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.finishFunction impl value) :=
  (ReplacementSitesFree.finishFunction le before impl value).at

theorem lowerImpl_replacement_sites {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : ImplId} {impl : Core.Impl} (lookup : module.impls[index]? = some impl) :
    ReplacementSitesBuilder (targets := []) (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl) := by
  have implementation := validate_implementation_checks accepted (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  obtain ⟨bodyType, finish, bodySource, _⟩ := (checkImpl_ok module impl implementation).body
  have sourceTypes : SourceReadableEnvironment (implEnv module impl) :=
    .implementation accepted lookup rfl
  have action : ReplacementSitesAt (targets := []) (lowerEnv module impl.vars impl.results.toList) initState (do
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
    apply (ReplacementSitesAt.newBlock _ _ _).bind
    apply (ReplacementSitesAt.setCur _ _ _).bind
    exact (replacementSites_lowerBlock impl.body sourceTypes bodySource impl.results.toList none _ false current trivial (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets])).bind
      (ReplacementSitesAt.finishFunction _ _ _ _)
  unfold ReplacementSitesAt at action
  exact (action (by simp [ReplacementTargetsBound]) (ReplacementSitesBuilder.initState _)).2

theorem lowerGlobal_replacement_sites {module : Core.Module} (accepted : Core.validate module = .ok ())
    {index : GlobalId} {global : Core.Global} (lookup : module.globals[index]? = some global) :
    ReplacementSitesBuilder (targets := []) (lowerEnv module #[] [global.ty]) (cfg_globalState module global) := by
  obtain ⟨_, finish, source⟩ := checkGlobal_ok module index global (validate_global_checks accepted lookup)
  have sourceTypes : SourceReadableEnvironment (initEnv module index) := .empty accepted rfl
  have action : ReplacementSitesAt (targets := []) (lowerEnv module #[] [global.ty]) initState (do
      let (entry, _) ← newBlock []
      setCur (some entry)
      let value ← lowerExpr global.init
      emitTerm (.ret [value] (some global.org))) := by
    refine ReplacementSitesAt.startBlock_generated (α := Unit)
      (le := lowerEnv module #[] [global.ty]) (before := initState)
      (tail := fun _ _ => do
        let value ← lowerExpr global.init
        emitTerm (.ret [value] (some global.org))) [] GeneratedBuilderState.initState ?_
    intro entry parameters state current bound
    exact (replacementSites_lowerExpr global.init sourceTypes source [global.ty] current).bind (ReplacementSitesAt.emitTerm _ _ _)
  unfold ReplacementSitesAt at action
  exact (action (by simp [ReplacementTargetsBound]) (ReplacementSitesBuilder.initState _)).2

theorem ReplacementSitesBuilder.finishBlocks {le : LEnv} {state : LS} {func : Func}
    (checked : ReplacementSitesBuilder (targets := targets) le state)
    (blocks : func.blocks = Goose.Lower.finishBlocks state.blocks)
    {blockIndex : Nat} {block : GIR.Block} (row : func.blocks[blockIndex]? = some block)
    {position : Nat} {owner value : ValueId} {origin : Option OriginId}
    (present : block.insts[position]? = some (.eff (.replace owner value origin))) :
    ∃ sourceOrigin, origin = some sourceOrigin ∧
      Nonempty (ReplacementSiteAt le state blockIndex position owner value sourceOrigin) := by
  rw [blocks, Goose.Lower.finishBlocks, Array.getElem?_map] at row
  cases bodyRow : state.blocks[blockIndex]? with
  | none => simp [bodyRow] at row
  | some body =>
    simp only [bodyRow, Option.map_some, Option.some.injEq] at row
    subst block
    have authority := checked blockIndex body bodyRow position (.eff (.replace owner value origin))
      (by simpa using present)
    cases origin with
    | none => exact False.elim authority
    | some sourceOrigin =>
      obtain ⟨witness⟩ := authority
      exact ⟨sourceOrigin, rfl, ⟨witness.site⟩⟩

theorem lowerImpl_source_replacement_sites {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ImplId} {impl : Core.Impl}
    (lookup : module.impls[index]? = some impl)
    {blockIndex : Nat} {block : GIR.Block} (row : (lowerImpl module impl).blocks[blockIndex]? = some block)
    {position : Nat} {owner value : ValueId} {origin : Option OriginId}
    (present : block.insts[position]? = some (.eff (.replace owner value origin))) :
    ∃ sourceOrigin, origin = some sourceOrigin ∧
      Nonempty (ReplacementSiteAt (lowerEnv module impl.vars impl.results.toList)
        (cfg_implState module impl) blockIndex position owner value sourceOrigin) :=
  (lowerImpl_replacement_sites accepted lookup).finishBlocks rfl row present

theorem lowerContextAt_source_replacement_sites {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ImplId} {impl : Core.Impl}
    (lookup : module.impls[index]? = some impl) (context : Context)
    {blockIndex : Nat} {block : GIR.Block} (row : (lowerContextAt module context impl).blocks[blockIndex]? = some block)
    {position : Nat} {owner value : ValueId} {origin : Option OriginId}
    (present : block.insts[position]? = some (.eff (.replace owner value origin))) :
    ∃ sourceOrigin, origin = some sourceOrigin ∧
      Nonempty (ReplacementSiteAt (lowerEnv module impl.vars impl.results.toList)
        (cfg_implState module impl) blockIndex position owner value sourceOrigin) :=
  (lowerImpl_replacement_sites accepted lookup).finishBlocks rfl row present

theorem lowerGlobal_source_replacement_sites {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (lookup : module.globals[index]? = some global)
    {blockIndex : Nat} {block : GIR.Block} (row : (lowerGlobal module global).init.blocks[blockIndex]? = some block)
    {position : Nat} {owner value : ValueId} {origin : Option OriginId}
    (present : block.insts[position]? = some (.eff (.replace owner value origin))) :
    ∃ sourceOrigin, origin = some sourceOrigin ∧
      Nonempty (ReplacementSiteAt (lowerEnv module #[] [global.ty])
        (cfg_globalState module global) blockIndex position owner value sourceOrigin) :=
  (lowerGlobal_replacement_sites accepted lookup).finishBlocks rfl row present

#print axioms lowerImpl_source_replacement_sites
#print axioms lowerContextAt_source_replacement_sites
#print axioms lowerGlobal_source_replacement_sites

end Goose.Lower.Validation
