import Goose.GIR.Effects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem effectStep_store_parameter_nonSlice {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {effect : Core.Eff} {address value : ValueId}
    {parameter : Nat} {origin : OriginId}
    (roots : rootsAt provenance.vals address = [.param parameter])
    (owner : (ownerTy vt address).any Ty.isSlice = false) :
    func.effectStep module vt provenance effect (.eff (.store address value origin)) =
      { effect with writes := addTargets effect.writes [.param parameter] } := by
  cases lookup : func.params[parameter]? <;>
    simp [Func.effectStep, roots, owner, lookup, targetsOf, rootsTargets, rootTarget, addTargets]

theorem effectStep_store_parameter_slice {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {effect : Core.Eff} {address value : ValueId}
    {parameter : Nat} {ty : Ty} {origin : OriginId}
    (roots : rootsAt provenance.vals address = [.param parameter])
    (lookup : func.params[parameter]? = some ty) (reference : ty.isRefSlice = true)
    (owner : (ownerTy vt address).any Ty.isSlice = true) :
    func.effectStep module vt provenance effect (.eff (.store address value origin)) =
      { effect with
        writes := addTargets effect.writes [.param parameter]
        rebinds := addTargets effect.rebinds [.param parameter] } := by
  simp [Func.effectStep, roots, lookup, reference, owner, targetsOf, rootsTargets, rootTarget]

end Goose.Lower.Validation.SummaryPreservation
