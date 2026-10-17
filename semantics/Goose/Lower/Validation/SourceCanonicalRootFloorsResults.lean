import Goose.Lower.Validation.SourceCanonicalRootFloorsSeeds
import Goose.Lower.CoreToGir

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem result_rounds_retain
    {step : Array (List RootRef) → Array (List RootRef) × Bool} {count : Nat}
    (retains : ∀ current index, index < count →
      rootsAt current index ⊆ rootsAt (step current).1 index)
    (fuel : Nat) (initial : Array (List RootRef)) {index : Nat} (bounded : index < count) :
    rootsAt initial index ⊆ rootsAt (resultRoots.go step fuel initial) index := by
  induction fuel generalizing initial with
  | zero => exact fun _ member => member
  | succ fuel ih =>
      rw [resultRoots.go]
      cases advanced : step initial with
      | mk next changed =>
          have included := retains initial index bounded
          rw [advanced] at included
          dsimp only at included ⊢
          split
          · exact fun _ member => ih next (included member)
          · exact included

theorem resultRoots_declared_seed_floor (module : GIR.Module)
    (types : Array (Array (Option VTy))) (typeCount : module.funcs.size ≤ types.size)
    {index : FnId} (bounded : index < module.funcs.size) :
    rootsAt module.declaredResultRoots index ⊆ rootsAt (resultRoots module types) index := by
  unfold resultRoots
  apply result_rounds_retain (count := module.funcs.size) _ _ _ bounded
  intro current callee calleeBound
  have typeBound : callee < types.size := Nat.lt_of_lt_of_le calleeBound typeCount
  have functionAt : module.funcs[callee]? = some module.funcs[callee] := by simp [calleeBound]
  have typeAt : types[callee]? = some types[callee] := by simp [typeBound]
  have paired : (module.funcs.zip types)[callee]? = some (module.funcs[callee], types[callee]) :=
    Array.getElem?_zip_eq_some.mpr ⟨functionAt, typeAt⟩
  dsimp only
  simp only [rootsAt, Array.getElem?_mapIdx, paired, Option.map_some, Option.getD_some]
  exact unionRoots_left _ _

theorem module_implTypes_size (module : GIR.Module) : module.implTypes.size = module.funcs.size := by
  simp [GIR.Module.implTypes, GIR.Module.infos, GIR.Module.labelled]

theorem resultRoots_declared_floor (module : GIR.Module) {index : FnId} {func : Func}
    (functionAt : module.funcs[index]? = some func) {type : Ty}
    (single : func.results = [type]) (reference : type.isRefLike = true)
    (annotated : func.roots.slots.isSome = true) :
    (func.roots.results[0]?.getD []) ⊆ rootsAt (resultRoots module module.implTypes) index := by
  apply List.Subset.trans _ (resultRoots_declared_seed_floor module module.implTypes
    (Nat.le_of_eq (module_implTypes_size module).symm) (Array.getElem?_eq_some_iff.mp functionAt).1)
  simp only [rootsAt, GIR.Module.declaredResultRoots, Array.getElem?_map,
    functionAt, Option.map_some, single, annotated, reference, Bool.and_self, ite_true, Option.getD_some]
  exact fun _ member => member

theorem lowerContext_resultRoots_declared_floor {module : Core.Module} {context : Context}
    {impl : Impl} {index : ContextId} (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl) {type : Ty}
    (single : impl.results.toList = [type]) (reference : type.isRefLike = true) :
    (context.resultRoots[0]?.getD []) ⊆
      rootsAt (resultRoots (lower module) (lower module).implTypes) index := by
  have functionAt : (lower module).funcs[index]? = some (lowerContextAt module context impl) := by
    simp [lower, Array.getElem?_map, contextAt, implAt, lowerContextAt, lowerImpl]
  have resultCount : impl.results.size = 1 := by
    simpa only [Array.length_toList, List.length_cons, List.length_nil] using congrArg List.length single
  have seed : (context.resultRoots[0]?.getD []) ⊆
      ((lowerContextAt module context impl).roots.results[0]?.getD []) := by
    change _ ⊆ (((List.range impl.results.size).map fun index =>
      lowerContextRootCeiling context impl (context.resultRoots[index]?.getD [])).toArray[0]?.getD [])
    rw [resultCount]
    change _ ⊆ lowerContextRootCeiling context impl (context.resultRoots[0]?.getD [])
    exact unionRoots_left _ _
  apply List.Subset.trans seed
  exact resultRoots_declared_floor (lower module) functionAt single reference rfl

end Goose.Lower.Validation.SourceCanonicalRootFloors
