import Goose.Lower.GeneratedBuilder
import Goose.Lower.GeneratedTargetFramesControl
import Goose.Lower.Validation.PermissionPreservationInstructionRules
import Goose.Lower.Validation.PermissionPreservationNewEmit

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem initSlots_newPermissionInstructions (slots : List (SlotId × ValueId × OriginId))
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {before after : LS} {result : Unit}
    (run : initSlots slots le before = (result, after))
    (generated : GeneratedBuilderState before)
    (transfer : ∀ entry ∈ slots, ∀ descriptor, func.slots[entry.1]? = some descriptor →
      PermissionTransfer module.profile (FreshWritableEvidence le first before)
        (FreshContentsEvidence le first before) entry.2.1 descriptor.ty) :
    NewPermissionInstructions module func le first before after := by
  induction slots generalizing before after with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | cons entry rest ih =>
    rcases entry with ⟨slot, value, origin⟩
    obtain ⟨emittedResult, middle, emitted, remaining⟩ := bind_eq.mp run
    have middleGenerated := generated.emitEffect (.slotInit slot value (some origin)) emitted
    have retainTransfer {value : ValueId} {type : Ty}
        (allowed : PermissionTransfer module.profile (FreshWritableEvidence le first before)
          (FreshContentsEvidence le first before) value type) :
        PermissionTransfer module.profile (FreshWritableEvidence le first middle)
          (FreshContentsEvidence le first middle) value type := by
      exact allowed.mono
        (fun _ evidence => evidence.of_framed_run (loop := none) emitted (dense_emitEffect _)
          (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _)
          generated.dense generated.live trivial)
        (fun _ evidence => evidence.of_framed_run (loop := none) emitted (dense_emitEffect _)
          (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _)
          generated.dense generated.live trivial)
    have firstRun := NewPermissionInstructions.emitEffect (module := module) (func := func)
      (first := first) emitted (fun _ => .slotInit (fun descriptor row =>
        retainTransfer (transfer (slot, value, origin) (by simp) descriptor row)))
    have restTransfer : ∀ entry ∈ rest, ∀ descriptor, func.slots[entry.1]? = some descriptor →
        PermissionTransfer module.profile (FreshWritableEvidence le first middle)
          (FreshContentsEvidence le first middle) entry.2.1 descriptor.ty := by
      intro entry member descriptor row
      exact retainTransfer (transfer entry (by simp [member]) descriptor row)
    have restRun := ih remaining middleGenerated restTransfer
    apply firstRun.compose restRun
    intro instruction member permitted
    have advanced := advB_initSlots rest le middle result after remaining
    have framed := (generatedTargetFrame_initSlots none rest middle le middle result after
      (.refl _) trivial (.refl none middle) remaining).1
    exact permitted.retained (loop := none) middleGenerated.dense
      (middleGenerated.initSlots rest remaining).dense advanced.ext advanced.vals
      (types_initSlots rest le middle result after remaining) trivial framed

#print axioms initSlots_newPermissionInstructions

end Goose.Lower.Validation
