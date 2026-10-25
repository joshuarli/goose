import Goose.Lower.Validation.CfgFunctionNoReturn
import Goose.Lower.Validation.CfgNoReturnPreservation

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def SourceStoppingReturnFree (module : Core.Module) : Prop :=
  ∀ callee context impl, module.contexts[callee]? = some context →
    module.impls[context.impl]? = some impl → module.noReturn callee = true →
      ReturnFreeStoppingBlock module.noReturn impl.body

theorem lower_context_function (module : Core.Module) (callee : ContextId)
    (context : Core.Context) (impl : Core.Impl)
    (contextRow : module.contexts[callee]? = some context)
    (implRow : module.impls[context.impl]? = some impl) :
    (lower module).funcs[callee]? = some (lowerContextAt module context impl) := by
  simp [lower, Array.getElem?_map, contextRow, implRow, lowerContextAt, lowerImpl]

theorem lower_returnTransfer_barrier (module : Core.Module) (source : SourceStoppingReturnFree module)
    (current : Array Bool) (_sized : current.size = (lower module).funcs.size)
    (barrier : CoreNoReturnBarrier module current) :
    CoreNoReturnBarrier module (ReturnTransfer (lower module) current) := by
  intro callee stopped
  obtain ⟨context, impl, contextRow, implRow, bodyStops⟩ := core_noReturn_body_stops module callee stopped
  have free := source callee context impl contextRow implRow stopped
  have returns := lowerImpl_stopping_mayReturn module impl free bodyStops current (by
    intro called noReturn
    simp [barrier called noReturn])
  have contextReturns : funcMayReturn current (lowerContextAt module context impl) = false := by
    rw [funcMayReturn_of_blocks current (left := lowerContextAt module context impl)
      (right := lowerImpl module impl) rfl]
    exact returns
  simp only [ReturnTransfer, Array.getElem?_map,
    lower_context_function module callee context impl contextRow implRow, Option.map_some]
  rw [contextReturns]

theorem lower_noReturn_of_source (module : Core.Module) (source : SourceStoppingReturnFree module) :
    ∀ callee, module.noReturn callee = true → (lower module).functionsMayReturn[callee]?.getD true = false :=
  lower_noReturn_of_transfer module (lower_returnTransfer_barrier module source)

theorem lower_checkUnreachable_of_source (module : Core.Module) (source : SourceStoppingReturnFree module) :
    checkUnreachable (lower module) = .ok () :=
  lower_checkUnreachable_of_transfer module (lower_returnTransfer_barrier module source)

end Goose.Lower.Validation
