import Goose.GIR.Validate
import Goose.Core.Sound.Frame

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem result_rounds_retain {one : Array (List RootRef) → Array (List RootRef) × Bool}
    (index : Nat)
    (retained : ∀ current root, root ∈ rootsAt current index → root ∈ rootsAt (one current).1 index)
    (fuel : Nat) (initial : Array (List RootRef)) (root : RootRef)
    (member : root ∈ rootsAt initial index) :
    root ∈ rootsAt (GIR.resultRoots.go one fuel initial) index := by
  induction fuel generalizing initial with
  | zero => exact member
  | succ fuel ih =>
    rw [GIR.resultRoots.go]
    cases step : one initial with
    | mk next changed =>
      have nextMember := retained initial root member
      rw [step] at nextMember
      dsimp only at nextMember ⊢
      split
      · exact ih _ nextMember
      · exact nextMember

theorem native_declared_resultRoots_retained (module : GIR.Module) (types : Array (Array (Option VTy)))
    (size : types.size = module.funcs.size) {index : FnId} {func : Func}
    (funcAt : module.funcs[index]? = some func) (root : RootRef)
    (member : root ∈ rootsAt module.declaredResultRoots index) :
    root ∈ rootsAt (GIR.resultRoots module types) index := by
  have bound : index < types.size := size ▸ (Array.getElem?_eq_some_iff.mp funcAt).1
  have typeAt : types[index]? = some types[index] := Array.getElem?_eq_getElem bound
  have zipped : (module.funcs.zip types)[index]? = some (func, types[index]) :=
    Array.getElem?_zip_eq_some.mpr ⟨funcAt, typeAt⟩
  unfold GIR.resultRoots
  apply result_rounds_retain index ?_ _ _ root member
  intro current chosen present
  change chosen ∈ rootsAt ((module.funcs.zip types).mapIdx fun k pair =>
    unionRoots (current[k]?.getD [])
      (pair.1.returnedRoots (pair.1.provenance current pair.2 module.rootCount))) index
  simp only [rootsAt, Array.getElem?_mapIdx, zipped, Option.bind_some,
    Option.map_some, Option.getD_some]
  exact unionRoots_left _ _ chosen present

#print axioms native_declared_resultRoots_retained

end Goose.Lower.Validation
