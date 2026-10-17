import Goose.Lower.Validation.AdmittedSourceAccepted
import Goose.Lower.Validation.ProvenanceSourceAccepted
import Goose.Lower.Validation.Entry

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem forIn_unit_ok {items : List α} {body : α → PUnit → Except ε (ForInStep PUnit)}
    (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
    rw [List.forIn_cons, checked item (by simp)]
    simp only [bind, Except.bind]
    apply inductionHypothesis
    intro next member
    exact checked next (by simp [member])

theorem accepted_context_checkRegionClosure {module : Core.Module} {context : Context} {impl : Impl}
    {contextId : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextId]? = some context)
    (implAt : module.impls[context.impl]? = some impl) :
    let func := lowerContextAt module context impl
    func.checkRegionClosure (lower module)
      (resultRoots (lower module) (lower module).implTypes) (func.valueTypes (lower module))
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount)
      (some (rootsAt (resultRoots (lower module) (lower module).implTypes) contextId)) = .ok () := by
  dsimp only
  have quiet := lowerContextAt_provenance_fixed accepted contextAt implAt
  have returned := accepted_function_returnedRoots_closed accepted contextAt implAt
  have returns : ((lowerContextAt module context impl).returnedRoots
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount)).all
      (rootsAt (resultRoots (lower module) (lower module).implTypes) contextId).contains = true := by
    simpa only [List.all_eq_true, List.contains_iff_mem] using returned
  simp only [Func.checkRegionClosure, quiet, Bool.false_eq_true, ↓reduceIte, returns]
  exact accepted_context_checkAdmittedRegions accepted contextAt implAt

theorem accepted_global_checkRegionClosure {module : Core.Module} {global : Core.Global}
    {index : GlobalId} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global) :
    let func := (lowerGlobal module global).init
    func.checkRegionClosure (lower module)
      (resultRoots (lower module) (lower module).implTypes) (func.valueTypes (lower module))
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount) none = .ok () := by
  dsimp only
  have quiet := lowerGlobal_provenance_fixed accepted globalAt
  simp only [Func.checkRegionClosure, quiet, Bool.false_eq_true, ↓reduceIte]
  exact accepted_global_checkAdmittedRegions accepted globalAt

theorem accepted_module_checkAdmittedRegions {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    (lower module).checkAdmittedRegions (lower module).implTypes
      (resultRoots (lower module) (lower module).implTypes) (lower module).rootCount = .ok () := by
  unfold Module.checkAdmittedRegions
  rw [lower_checkRegionGlobalTypes accepted]
  simp only [bind, Except.bind]
  have functions : forIn (lower module).funcs.toList.zipIdx PUnit.unit
      (fun indexed _ => do
        let vt := (lower module).implTypes[indexed.2]?.getD #[]
        indexed.1.checkRegionClosure (lower module)
          (resultRoots (lower module) (lower module).implTypes) vt
          (indexed.1.provenance (resultRoots (lower module) (lower module).implTypes) vt (lower module).rootCount)
          (some (rootsAt (resultRoots (lower module) (lower module).implTypes) indexed.2))
        pure (.yield PUnit.unit)) =
      (Except.ok PUnit.unit : Except String PUnit) := by
    apply forIn_unit_ok
    intro indexed member
    obtain ⟨func, index⟩ := indexed
    have functionAt : (lower module).funcs[index]? = some func := by
      simpa only [Array.getElem?_toList] using List.mk_mem_zipIdx_iff_getElem?.mp member
    cases contextAt : module.contexts[index]? with
    | none => simp [lower, Array.getElem?_map, contextAt] at functionAt
    | some context =>
      obtain ⟨impl, implAt, _⟩ := (validate_modOk module accepted).ctx index context contextAt
      have same := Option.some.inj (functionAt.symm.trans (lower_func_at contextAt implAt))
      subst func
      have typeRow : (lower module).implTypes[index]?.getD #[] =
          (lowerContextAt module context impl).valueTypes (lower module) := by
        rw [module_implTypes_eq_native]
        simp only [Array.getElem?_map, lower_func_at contextAt implAt,
          Option.map_some, Option.getD_some]
      simp only [typeRow, accepted_context_checkRegionClosure accepted contextAt implAt,
        bind, Except.bind, pure, Except.pure]
  dsimp only at functions
  simp only [bind, Except.bind] at functions
  rw [functions]
  rw [← Array.forIn_toList]
  suffices loop : forIn (lower module).globals.toList PUnit.unit _ =
      (Except.ok PUnit.unit : Except String PUnit) by
    rw [loop]
    rfl
  apply forIn_unit_ok
  intro lowered member
  change lowered ∈ (module.globals.map (lowerGlobal module)).toList at member
  simp only [Array.toList_map, List.mem_map] at member
  obtain ⟨global, globalMember, rfl⟩ := member
  obtain ⟨index, globalAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp globalMember)
  simp only [accepted_global_checkRegionClosure accepted globalAt, pure, Except.pure]

#print axioms accepted_module_checkAdmittedRegions

end Goose.Lower.Validation
