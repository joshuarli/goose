import Goose.Construct.Runtime
import Goose.Proofs.ExitExecutionStorageIntervals

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem listForIn_congr {m : Type → Type} [Monad m] (items : List α)
    (left right : α → β → m (ForInStep β))
    (equal : ∀ item ∈ items, ∀ accumulator, left item accumulator = right item accumulator)
    (accumulator : β) : forIn items accumulator left = forIn items accumulator right := by
  induction items generalizing accumulator with
  | nil => rfl
  | cons item items ih =>
      simp only [List.forIn_cons, equal item (by simp)]
      congr 1
      funext next
      cases next with
      | done value => rfl
      | yield value => exact ih (fun item member => equal item (List.mem_cons_of_mem _ member)) value

theorem BytePrefixEqual.bytesInt {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (ty : Goose.Core.IntTy) (start : Nat)
    (inside : start + ty.bits / 8 ≤ limit) :
    Goose.Construct.bytesInt ty after start = Goose.Construct.bytesInt ty before start := by
  have beforeSize := equal.beforeBound
  have afterSize := equal.afterBound
  have beforeBound : ¬start + ty.bits / 8 > before.size := by omega
  have afterBound : ¬start + ty.bits / 8 > after.size := by omega
  simp only [Goose.Construct.bytesInt, beforeBound, afterBound, ↓reduceIte,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  congr 1
  apply listForIn_congr
  intro index member accumulator
  have bounded : index < ty.bits / 8 := by
    have indexBound := List.mem_range'.mp member
    obtain ⟨offset, inside, rfl⟩ := indexBound
    simpa only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Nat.zero_add, Nat.one_mul] using inside
  rw [equal.getElem? (start + index) (by omega)]

def FixedLayoutFieldBounds (layout : LayoutEnv) : Prop :=
  ∀ (id : Nat) (descriptor : StructDef), layout.structs[id]? = some descriptor →
    ∀ (field : StructField), field ∈ descriptor.fields.toList → ∃ width,
      fixedByteSize? layout field.ty = some width ∧ field.byteOffset + width ≤ descriptor.byteSize

private theorem listMapM_congr {m : Type → Type} [Monad m] [LawfulMonad m] (items : List α)
    (left right : α → m β) (equal : ∀ item ∈ items, left item = right item) :
    items.mapM left = items.mapM right := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp only [List.mapM_cons, equal item (by simp),
        ih (fun item member => equal item (List.mem_cons_of_mem _ member))]

theorem BytePrefixEqual.fixedValue {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (fuel : Nat) (layout : LayoutEnv)
    (fields : FixedLayoutFieldBounds layout) (ty : Ty) (width start : Nat)
    (size : fixedByteSize? layout ty = some width) (inside : start + width ≤ limit) :
    Goose.Construct.fixedValue fuel layout ty after start = Goose.Construct.fixedValue fuel layout ty before start := by
  induction fuel generalizing ty width start with
  | zero => rfl
  | succ fuel ih =>
    cases ty with
    | int ty =>
        have sizeEqual : ty.bits / 8 = width := Option.some.inj size
        simp only [Goose.Construct.fixedValue]
        rw [equal.bytesInt ty start (by omega)]
    | bool =>
        have sizeEqual : 1 = width := Option.some.inj size
        simp only [Goose.Construct.fixedValue]
        rw [equal.getElem? start (by omega)]
    | arr element count =>
        cases sized : fixedByteSize? layout element with
        | none => simp [fixedByteSize?, sized] at size
        | some elementWidth =>
            have sizeEqual : count * elementWidth = width := by
              simpa only [fixedByteSize?, sized, Option.map_some, Option.some.injEq] using size
            simp only [Goose.Construct.fixedValue, sized]
            have reads : (List.range count).mapM
                (fun index => Goose.Construct.fixedValue fuel layout element after (start + index * elementWidth)) =
              (List.range count).mapM
                (fun index => Goose.Construct.fixedValue fuel layout element before (start + index * elementWidth)) := by
              apply listMapM_congr
              intro index member
              have indexBound := List.mem_range.mp member
              exact ih element elementWidth (start + index * elementWidth) sized (by
                have multiplication := Nat.mul_le_mul_right elementWidth (show index + 1 ≤ count by omega)
                simp only [Nat.add_mul, Nat.one_mul] at multiplication
                omega)
            rw [reads]
    | structT id members =>
        simp only [fixedByteSize?] at size
        split at size
        · cases size
        · cases descriptor : layout.structs[id]? with
          | none => simp [descriptor] at size
          | some definition =>
              have sizeEqual : definition.byteSize = width := by
                simpa only [descriptor, Option.map_some, Option.some.injEq] using size
              simp only [Goose.Construct.fixedValue, descriptor]
              have reads : definition.fields.toList.mapM
                  (fun field => Goose.Construct.fixedValue fuel layout field.ty after (start + field.byteOffset)) =
                definition.fields.toList.mapM
                  (fun field => Goose.Construct.fixedValue fuel layout field.ty before (start + field.byteOffset)) := by
                apply listMapM_congr
                intro field member
                obtain ⟨fieldWidth, fieldSize, fieldBound⟩ := fields id definition descriptor field member
                exact ih field.ty fieldWidth (start + field.byteOffset) fieldSize (by omega)
              rw [reads]
    | _ => cases size

#print axioms BytePrefixEqual.bytesInt
#print axioms BytePrefixEqual.fixedValue

end Goose.Proofs.ExitExecution
