import Goose.Lower.Validation.CfgCoreNoReturn
import Goose.Lower.Validation.CfgReturnConvergence
import Goose.Lower.Validation.CfgUnreachableCheck

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def CoreNoReturnBarrier (module : Core.Module) (current : Array Bool) : Prop :=
  ReturnBarrier (fun callee => module.noReturn callee = true) current

theorem lower_noReturn_of_transfer (module : Core.Module)
    (preserves : ∀ current, current.size = (lower module).funcs.size →
      CoreNoReturnBarrier module current →
      CoreNoReturnBarrier module (ReturnTransfer (lower module) current)) :
    ∀ callee, module.noReturn callee = true →
      (lower module).functionsMayReturn[callee]?.getD true = false := by
  apply functionsMayReturn_preservesBarrier (lower module) (fun callee => module.noReturn callee = true)
  · intro callee stopped
    simp only [lower, Array.size_map]
    exact core_noReturn_bounded module callee stopped
  · exact preserves

theorem lower_checkUnreachable_of_transfer (module : Core.Module)
    (preserves : ∀ current, current.size = (lower module).funcs.size →
      CoreNoReturnBarrier module current →
      CoreNoReturnBarrier module (ReturnTransfer (lower module) current)) :
    checkUnreachable (lower module) = .ok () :=
  lower_checkUnreachable module (lower_noReturn_of_transfer module preserves)

end Goose.Lower.Validation
