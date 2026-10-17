import Goose.Lower.Validation.ProvenanceConvergenceFinite
import Goose.Lower.Validation.SymbolTables

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ProvenanceConvergence

theorem ProvenanceConvergence.RootBounds.with_results {module : GIR.Module} {func : Func}
    {before after : Array (List RootRef)}
    (bounds : RootBounds before func module.globals.size)
    (results : ∀ callee global, RootRef.global global ∈ rootsAt after callee → global < module.globals.size) :
    RootBounds after func module.globals.size :=
  { bounds with results := results }

theorem SymbolTableFacts.provenance_bounds {module : GIR.Module} {func : Func} {env : LEnv}
    (facts : SymbolTableFacts module func)
    (entry : ∀ block, func.blocks[0]? = some block → block.params.length ≤ func.params.length)
    (instructions : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      Inst.SymbolsWithin env func.scopes.size func.numValues func.blocks.size inst)
    (slots : env.slots.size = func.slots.size) (globals : env.globals.size = module.globals.size) :
    RootBounds #[] func module.globals.size := by
  constructor
  · exact entry
  · intro block blockAt value slot present
    have bounded := (instructions block blockAt _ present).slots slot (by simp [instSlotRefs])
    simpa only [slots] using bounded
  · intro block blockAt value global present
    have bounded := (instructions block blockAt _ present).globals global (by simp [instGlobalRefs])
    simpa only [globals] using bounded
  · intro row rowAt root rootAt
    have bound := (facts.contents row.1 row.2 (Array.mem_toList_iff.mpr rowAt)).2.2 root rootAt
    cases root <;> simp_all [RootRef.ExternalWithin, ValidRoot]
  · intro row rowAt root rootAt
    have bound := (facts.slotRoots row.1 row.2 (Array.mem_toList_iff.mpr rowAt)).2 root rootAt
    cases root <;> exact bound
  · intro row rowAt root rootAt
    have bound := (facts.valueRoots row.1 row.2 (Array.mem_toList_iff.mpr rowAt)).2 root rootAt
    cases root <;> exact bound
  · intro callee global member
    simp [rootsAt] at member

theorem returnedRoots_subset {func : Func} {provenance : Prov} {roots : List RootRef}
    (values : ∀ value, rootsAt provenance.vals value ⊆ roots) :
    func.returnedRoots provenance ⊆ roots := by
  unfold Func.returnedRoots
  rw [← Array.foldl_toList]
  apply List.foldlRecOn (motive := fun current => current ⊆ roots)
  · exact List.nil_subset _
  · intro current currentBound block blockAt
    apply List.foldlRecOn (motive := fun current => current ⊆ roots)
    · exact currentBound
    · intro found foundBound inst instAt
      cases inst with
      | «def» value op => exact foundBound
      | eff effect => exact foundBound
      | term term =>
        cases term <;> try exact foundBound
        case ret values' origin =>
          cases values' with
          | nil => exact foundBound
          | cons value rest =>
            cases rest with
            | nil =>
              intro root member
              exact (Core.Sound.unionRoots_mem _ _ _ member).elim (fun member => foundBound member) (fun member => values value member)
            | cons next tail => exact foundBound

theorem resultRoots_global_bounds {module : GIR.Module} {types : Array (Array (Option VTy))}
    (functions : ∀ func ∈ module.funcs.toList, RootBounds #[] func module.globals.size)
    (initial : ∀ index global, RootRef.global global ∈ rootsAt module.declaredResultRoots index →
      global < module.globals.size) :
    ∀ index global, RootRef.global global ∈ rootsAt (resultRoots module types) index →
      global < module.globals.size := by
  let bounded := fun table : Array (List RootRef) =>
    ∀ index global, RootRef.global global ∈ rootsAt table index → global < module.globals.size
  let one := fun candidate : Array (List RootRef) =>
    let next := (module.funcs.zip types).mapIdx fun index (func, vt) =>
      unionRoots (rootsAt candidate index)
        (func.returnedRoots (func.provenance candidate vt (moduleRootCount module)))
    (next, (next.zip candidate).any fun (a, b) => a.length != b.length)
  have step : ∀ candidate, bounded candidate → bounded (one candidate).1 := by
    intro candidate candidateBound index global member
    simp only [one, rootsAt, Array.getElem?_mapIdx] at member
    cases row : (module.funcs.zip types)[index]? with
    | none => simp [row] at member
    | some pair =>
      obtain ⟨func, vt⟩ := pair
      simp only [row, Option.map_some, Option.getD_some] at member
      rcases Core.Sound.unionRoots_mem _ _ _ member with prior | returned
      · exact candidateBound index global prior
      · have funcMember : func ∈ module.funcs.toList :=
          Array.mem_toList_iff.mpr (Array.of_mem_zip (Array.mem_of_getElem? row)).1
        have limits := (functions func funcMember).with_results candidateBound
        have tableBound := provenance_bounded (types := vt) limits.finite (moduleRootCount module)
        have valid := returnedRoots_subset (fun value => (tableBound.2 value).2) returned
        exact mem_finiteRootUniverse.mp valid
  have go : ∀ fuel candidate, bounded candidate → bounded (resultRoots.go one fuel candidate) := by
    intro fuel
    induction fuel with
    | zero => intro candidate bound; exact bound
    | succ fuel ih =>
      intro candidate bound
      rw [resultRoots.go]
      cases result : one candidate with
      | mk next changed =>
        have nextBound := step candidate bound
        rw [result] at nextBound
        dsimp only at nextBound ⊢
        split
        · exact ih next nextBound
        · exact nextBound
  exact go _ module.declaredResultRoots initial

theorem declaredResultRoots_global_bounds {module : GIR.Module}
    (tables : ∀ func ∈ module.funcs.toList, SymbolTableFacts module func) :
    ∀ index global, RootRef.global global ∈ rootsAt module.declaredResultRoots index →
      global < module.globals.size := by
  intro index global member
  simp only [Module.declaredResultRoots, rootsAt, Array.getElem?_map] at member
  cases row : module.funcs[index]? with
  | none => simp [row] at member
  | some func =>
    simp only [row, Option.map_some, Option.getD_some] at member
    have facts := tables func (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row))
    cases results : func.results with
    | nil => simp [results] at member
    | cons type rest =>
      cases rest with
      | cons next tail => simp [results] at member
      | nil =>
        simp only [results] at member
        split at member
        · cases annotation : func.roots.results[0]? with
          | none => simp [annotation] at member
          | some roots =>
            simp only [annotation, Option.getD_some] at member
            exact facts.results roots (Array.mem_toList_iff.mpr (Array.mem_of_getElem? annotation)) _ member
        · simp at member

theorem module_provenance_fixed_of_symbols {module : GIR.Module}
    (tables : ∀ func ∈ module.funcs.toList, SymbolTableFacts module func)
    (bounds : ∀ func ∈ module.funcs.toList, RootBounds #[] func module.globals.size)
    {func : Func} (member : func ∈ module.funcs.toList) :
    provRound (resultRoots module module.implTypes) (func.valueTypes module) func
        (func.provenance (resultRoots module module.implTypes) (func.valueTypes module) module.rootCount) =
      (func.provenance (resultRoots module module.implTypes) (func.valueTypes module) module.rootCount, false) := by
  apply provenance_module_fixed member
  exact (bounds func member).with_results
    (resultRoots_global_bounds bounds (declaredResultRoots_global_bounds tables))

#print axioms SymbolTableFacts.provenance_bounds
#print axioms returnedRoots_subset
#print axioms resultRoots_global_bounds
#print axioms declaredResultRoots_global_bounds
#print axioms module_provenance_fixed_of_symbols

end Goose.Lower.Validation
