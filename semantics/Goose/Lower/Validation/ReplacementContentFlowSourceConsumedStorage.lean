import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrencePaths
import Goose.Lower.Validation.ReplacementContentFlowSourceNativeContinuation
import Goose.Lower.Validation.FreshRunSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem reference_storage_nonowner {type : Ty} (reference : type.isRefLike = true) :
    type.ownerElem?.isSome = false := by
  cases type <;> simp_all [Ty.ownerElem?, Ty.isRefLike]

theorem ConsumedReferenceOccurrence.emitted_slotAddr
    {env : PEnv} {root : DemandNode} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {le : LEnv} {before after : LS} {value : ValueId} {slot : SlotId} {storage : Slot} {mutability : Mutability}
    (generated : GeneratedBuilderState before)
    (run : emitDef (.slotAddr slot) le before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (storageAt : func.slots[slot]? = some storage)
    (typeAt : types[value]? = some (some (.data (.ref mutability storage.ty))))
    (nonowner : storage.ty.ownerElem?.isSome = false) :
    ConsumedReferenceOccurrence env root func types upper value := by
  have beforeLive := (dead_emitDef (.slotAddr slot)).live_before run live
  cases current : before.cur with
  | none => simp [current] at beforeLive
  | some block =>
    obtain ⟨completed, extension, blocks⟩ := continuation
    obtain ⟨body, member, defined⟩ := emitted_definition_retained current (generated.live block current)
      run extension blocks
    exact .administrative value slot storage mutability body member defined storageAt typeAt nonowner

end Goose.Lower.Validation.ReplacementContentFlowSource
