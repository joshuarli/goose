import Goose.Lower.Validation.SummaryPreservationEffectFold
import Goose.Lower.Validation.SummaryPreservationValueGrowth

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem effectStep_congr_values {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {before after : Prov} {effect : Core.Eff} (inst : Inst)
    (values : ∀ value ∈ inst.uses, rootsAt before.vals value = rootsAt after.vals value) :
    func.effectStep module vt before effect inst = func.effectStep module vt after effect inst := by
  cases inst with
  | «def» result op =>
    cases op with
    | call callee args origin =>
      have arguments : args.map (fun value =>
          let expanded := (rootsAt before.vals value).flatMap func.expandParameterRoot
          expanded.foldl (fun acc root => unionRoots acc [root]) []) =
        args.map (fun value =>
          let expanded := (rootsAt after.vals value).flatMap func.expandParameterRoot
          expanded.foldl (fun acc root => unionRoots acc [root]) []) := by
        apply List.map_congr_left
        intro value member
        rw [values value member]
      simp only [Func.effectStep, arguments]
    | viewSlice mutability value low high origin => cases low <;> cases high <;> rfl
    | un operation ty value origin => cases operation <;> rfl
    | conv kind source target value origin => cases kind <;> rfl
    | _ => simp_all [Func.effectStep, Inst.uses, Op.uses]
  | eff effect => cases effect <;> simp_all [Func.effectStep, Inst.uses, Effect.uses]
  | term term => cases term <;> rfl

theorem effectStep_push_fresh {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {before : Prov} {newRoots : List RootRef} {effect : Core.Eff} {inst : Inst}
    (bounds : ∀ value ∈ inst.uses, value < before.vals.size) :
    func.effectStep module vt { before with vals := before.vals.push newRoots } effect inst =
      func.effectStep module vt before effect inst := by
  apply effectStep_congr_values inst
  intro value member
  exact rootsAt_push_old (bounds value member)

end Goose.Lower.Validation.SummaryPreservation
