import Goose.Lower.Validation.CfgReturnFixedPoint
import Goose.Lower.Validation.CfgReturnWalk

namespace Goose.Lower.Validation

open Goose.GIR

theorem returnTransfer_monotone (module : Module) : ReturnTransferMonotone module := by
  intro left right order
  refine ⟨by simp [ReturnTransfer], ?_⟩
  intro index found
  simp only [ReturnTransfer, Array.getElem?_map] at found ⊢
  cases row : module.funcs[index]? with
  | none => simp [row] at found
  | some func =>
    simp only [row, Option.map_some, Option.some.injEq] at found ⊢
    exact funcMayReturn_monotone order func found

theorem functionsMayReturn_fixedPoint (module : Module) :
    ReturnTransfer module module.functionsMayReturn = module.functionsMayReturn :=
  (functionsMayReturn_invariant module (returnTransfer_monotone module)
    (fun _ => True) trivial (by intros; trivial)).2

theorem functionsMayReturn_preserves (module : Module) (invariant : Array Bool → Prop)
    (initial : invariant (Array.replicate module.funcs.size false))
    (preserves : ∀ current, current.size = module.funcs.size → invariant current →
      invariant (ReturnTransfer module current)) : invariant module.functionsMayReturn :=
  (functionsMayReturn_invariant module (returnTransfer_monotone module) invariant initial preserves).1

theorem functionsMayReturn_preservesBarrier (module : Module) (forbidden : Nat → Prop)
    (bounded : ∀ callee, forbidden callee → callee < module.funcs.size)
    (preserves : ∀ current, current.size = module.funcs.size → ReturnBarrier forbidden current →
      ReturnBarrier forbidden (ReturnTransfer module current)) :
    ∀ callee, forbidden callee → module.functionsMayReturn[callee]?.getD true = false :=
  functionsMayReturn_barrier module (returnTransfer_monotone module) forbidden bounded preserves

end Goose.Lower.Validation
