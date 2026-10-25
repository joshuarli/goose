import Goose.Lower.Validation.SourceValueRecipeTypes
import Goose.Lower.Validation.ValidationTypedModuleTables

namespace Goose.Lower.Validation.SourceValueRecipeTypes

open Goose.Core Goose.GIR

theorem lowerContextAt_valueRoots_refLike {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {context : Context} {impl : Impl} {index : Nat}
    (implAt : module.impls[index]? = some impl) {row : ValueId × List RootRef}
    (member : row ∈ ((lowerContextAt module context impl).roots.values.getD #[]).toList) :
    valRefLike ((lowerContextAt module context impl).valueTypes (lower module)) row.1 = true := by
  rw [lowerContext_valueTypes_of_accepted accepted implAt]
  obtain ⟨type, typed, reference⟩ := lowerContextAt_valueRoots_type module context impl member
  change valRefLike (lowerImplState module impl).vals row.1 = true
  simp only [valRefLike, typed, reference]

theorem lowerGlobal_valueRoots_refLike {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {global : Core.Global} {index : Nat}
    (globalAt : module.globals[index]? = some global) {row : ValueId × List RootRef}
    (member : row ∈ ((lowerGlobal module global).init.roots.values.getD #[]).toList) :
    valRefLike ((lowerGlobal module global).init.valueTypes (lower module)) row.1 = true := by
  rw [lowerGlobal_valueTypes_of_accepted accepted globalAt]
  obtain ⟨type, typed, reference⟩ := lowerGlobal_valueRoots_type module global member
  change valRefLike (globalRecipeTypeState module global).vals row.1 = true
  simp only [valRefLike, typed, reference]

end Goose.Lower.Validation.SourceValueRecipeTypes
