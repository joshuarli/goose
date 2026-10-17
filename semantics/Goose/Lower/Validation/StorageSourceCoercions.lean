import Goose.Lower.Validation.StorageSourceActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageAt.freezeTo (le : LEnv) (before : LS) (mu : Mutability) (value : ValueId) :
    StorageAt le before (Goose.Lower.freezeTo mu value) := by
  unfold Goose.Lower.freezeTo
  apply (StorageAt.valTy _ _ _).bind
  cases mu <;> cases (Goose.Lower.valTy value le before).1 with
  | data ty => cases ty <;> first
      | exact StorageAt.pure _ _ _
      | (rename_i mu ty; cases mu <;> first
          | exact StorageAt.pure _ _ _
          | exact StorageAt.emitDef _ (by intros; trivial))
  | view _ _ => exact StorageAt.pure _ _ _

theorem StorageAt.borrowTo (le : LEnv) (before : LS) (mu : Mutability) (value : ValueId) :
    StorageAt le before (Goose.Lower.borrowTo mu value) := by
  intro checked
  cases run : Goose.Lower.borrowTo mu value le before with
  | mk result after =>
    change StorageBuilder le.mod.profile after
    rcases borrowTo_cases run with frozen | borrowed
    · have retained := StorageAt.freezeTo le before mu value checked
      change StorageBuilder le.mod.profile (Goose.Lower.freezeTo mu value le before).2 at retained
      rw [frozen] at retained
      exact retained
    · exact checked.emitDef (op := .ownerBorrow value) (fun _ => trivial) borrowed

theorem StorageAt.coerceTo (le : LEnv) (before : LS) (target : Ty) (value : ValueId) (origin : OriginId) :
    StorageAt le before (Goose.Lower.coerceTo target value origin) := by
  intro checked
  cases run : Goose.Lower.coerceTo target value origin le before with
  | mk result after =>
    change StorageBuilder le.mod.profile after
    rcases coerceTo_cases run with
      ⟨_, same⟩ | ⟨element, _, emitted⟩ | ⟨element, view, middle, _, viewRun, sliceRun⟩
    · rw [same]; exact checked
    · exact checked.emitDef (op := .refFreeze value) (fun _ => trivial) emitted
    · exact (checked.emitDef (op := .sliceView value) (fun _ => trivial) viewRun).emitDef
        (op := .viewSlice .readOnly view .omitted .omitted (some origin)) (fun _ => trivial) sliceRun

theorem StorageAt.coerceSlot (le : LEnv) (before : LS) (slot : SlotId) (value : ValueId) (origin : OriginId) :
    StorageAt le before (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  apply (StorageAt.read _ _).bind
  simp only [read_apply]
  split
  · exact StorageAt.coerceTo _ _ _ _ _
  · exact StorageAt.pure _ _ _

theorem StorageAt.coerceResult (le : LEnv) (before : LS) (value : ValueId) (origin : OriginId) :
    StorageAt le before (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  apply (StorageAt.read _ _).bind
  simp only [read_apply]
  split
  · exact StorageAt.coerceTo _ _ _ _ _
  · exact StorageAt.pure _ _ _

end Goose.Lower.Validation
