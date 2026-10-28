import Goose.Lower.DemandParameterPrologue
import Goose.Lower.DemandGeneratedParameters

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem initSlots_layout {cx : FnCtx} (bindings : List (SlotId × ValueId × OriginId))
    {le : LEnv} {before : LS} {point : Pt} (atPoint : before.pp = some point)
    (extended : ExtT (initSlots bindings le before).2 cx.fn.blocks) :
    (initSlots bindings le before).2.pp = some (point.1, point.2 + bindings.length) ∧
      (initSlots bindings le before).2.vals.size = before.vals.size ∧
      (initSlots bindings le before).2.stack = before.stack := by
  induction bindings generalizing before point with
  | nil => simp [initSlots, pure_run, atPoint]
  | cons binding rest ih =>
    rcases binding with ⟨slot, id, origin⟩
    let emitted := emitEffect (.slotInit slot id (some origin)) le before
    have advance := advB_initSlots rest le emitted.2 _ _ rfl
    have lowered : (initSlots ((slot, id, origin) :: rest) le before).2 = (initSlots rest le emitted.2).2 := by
      simp only [initSlots, bind_run, emitted]
    have restExtended : ExtT (initSlots rest le emitted.2).2 cx.fn.blocks := by simpa only [lowered, emitted] using extended
    have emittedExtended : ExtT emitted.2 cx.fn.blocks := restExtended.of_adv advance
    obtain ⟨values, stack, nextPoint, _⟩ := emitEffect_facts
      (show emitEffect (.slotInit slot id (some origin)) le before = (emitted.1, emitted.2) from rfl) atPoint emittedExtended
    obtain ⟨endPoint, endValues, endStack⟩ := ih nextPoint restExtended
    rw [lowered]
    refine ⟨?_, endValues.trans values, endStack.trans stack⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using endPoint

#print axioms initSlots_layout
end Goose.Lower
