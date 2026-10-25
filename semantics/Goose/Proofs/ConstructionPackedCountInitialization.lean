import Goose.Construct.Eval
import Init.Data.ByteArray.Lemmas
import Init.Data.Range.Lemmas
import Init.Data.UInt.Lemmas
import Lean

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct

open Lean Elab Term in
elab "construction_count_patch" : term => do
  let information ← getConstInfo ``Goose.Construct.finishDestination
  let some value := information.value? | throwError "missing destination completion definition"
  let some operation := value.find? (fun expression => match expression with
    | .const name _ => name.toString.endsWith ".patchCount"
    | _ => false) | throwError "missing destination count patch"
  return operation

private abbrev nativeCountPatch : ByteArray → Nat → Nat → ByteArray := construction_count_patch

open Lean Elab Tactic in
elab "unfold_construction_count_patch" : tactic => do
  let information ← getConstInfo ``Goose.Construct.finishDestination
  let some value := information.value? | throwError "missing destination completion definition"
  let some operation := value.find? (fun expression => match expression with
    | .const name _ => name.toString.endsWith ".patchCount"
    | _ => false) | throwError "missing destination count patch"
  evalTactic (← `(tactic| unfold $(mkIdent operation.constName!)))

private theorem nativeCountPatch_size (bytes : ByteArray) (start count : Nat) :
    (nativeCountPatch bytes start count).size = bytes.size := by
  unfold nativeCountPatch
  unfold_construction_count_patch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, bind, pure,
    Id.run, ByteArray.size_set!]

private theorem nativeCountPatch_readCount (bytes : ByteArray) (start count : Nat)
    (bounded : start + 4 ≤ bytes.size) (fits : count < 2 ^ 32) :
    readCount (nativeCountPatch bytes start count) start = .ok count := by
  have arrayBound : start + 4 ≤ bytes.data.size := bounded
  have bound1 : start + 1 < bytes.size := by omega
  have bound2 : start + 2 < bytes.size := by omega
  have bound3 : start + 3 < bytes.size := by omega
  have ready : ¬start + 4 > (nativeCountPatch bytes start count).size := by
    rw [nativeCountPatch_size]
    omega
  simp only [readCount, ready, ↓reduceIte]
  unfold nativeCountPatch
  unfold_construction_count_patch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, bind, pure, Id.run]
  simp (disch := omega) [ByteArray.set!, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds, UInt8.toNat_ofNat', Except.bind, Except.pure, bound1, bound2, bound3]
  omega

theorem finishDestination_packed_count (before after : ConstructionState) (id : Nat)
    (destination : PendingDestination) (storage : ReceivingStorage) (count : Nat)
    (present : before.destinations[id]? = some destination)
    (stored : before.storage[destination.storage]? = some storage)
    (opened : destination.progress = .open count) (layout : destination.layout = .packed)
    (request : destination.capability.request = .value)
    (bounded : destination.capability.start + 4 ≤ storage.bytes.size) (fits : count < 2 ^ 32)
    (executed : finishDestination id before = .ok () after) :
    ∃ current, after.storage[destination.storage]? = some current ∧
      readCount current.bytes destination.capability.start = .ok count ∧
      current.bytes.size = storage.bytes.size ∧
      after.destinations[id]? = some { destination with progress := .built count } := by
  have destinationInside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [finishDestination, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before id with
  | false => simp only [allowed] at executed; cases executed
  | true =>
      simp only [allowed, opened, layout, hasPrefix_result, request, beq_self_eq_true,
        Bool.and_self, ↓reduceIte, lookupStorage_result, stored, replaceStorage_result,
        replaceDestination_result, storageInside, destinationInside, bind, pure,
        ↓reduceIte] at executed
      cases executed
      refine ⟨_, Array.getElem?_setIfInBounds_self_of_lt storageInside, ?_, ?_, ?_⟩
      · change readCount (nativeCountPatch storage.bytes destination.capability.start count)
          destination.capability.start = .ok count
        exact nativeCountPatch_readCount storage.bytes destination.capability.start count bounded fits
      · change (nativeCountPatch storage.bytes destination.capability.start count).size = storage.bytes.size
        exact nativeCountPatch_size _ _ _
      · simpa only [layout, Array.set!_eq_setIfInBounds] using (Array.getElem?_setIfInBounds_self_of_lt
          (xs := before.destinations) (a := { destination with progress := .built count }) destinationInside)

#print axioms finishDestination_packed_count

end Goose.Proofs.ConstructionRepresentation
