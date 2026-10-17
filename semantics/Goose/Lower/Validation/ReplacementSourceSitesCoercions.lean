import Goose.Lower.Validation.ReplacementSourceSitesActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSitesAt.freezeTo (le : LEnv) (before : LS) (mu : Mutability) (value : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.freezeTo mu value) := by
  unfold Goose.Lower.freezeTo
  apply (ReplacementSitesAt.valTy _ _ _).bind
  cases mu <;> cases (Goose.Lower.valTy value le before).1 with
  | data ty => cases ty <;> first
      | exact ReplacementSitesAt.pure _ _ _
      | (rename_i mu ty; cases mu <;> first
          | exact ReplacementSitesAt.pure _ _ _
          | exact ReplacementSitesAt.emitDef _ (by intros; trivial))
  | view _ _ => exact ReplacementSitesAt.pure _ _ _

theorem ReplacementSitesAt.borrowTo (le : LEnv) (before : LS) (mu : Mutability) (value : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.borrowTo mu value) := by
  intro checked
  cases run : Goose.Lower.borrowTo mu value le before with
  | mk result after =>
    change ReplacementSitesBuilder le after
    rcases borrowTo_cases run with frozen | borrowed
    · have retained := ReplacementSitesAt.freezeTo le before mu value checked
      change ReplacementSitesBuilder le (Goose.Lower.freezeTo mu value le before).2 at retained
      rw [frozen] at retained
      exact retained
    · exact checked.emitDef (op := .ownerBorrow value) (fun _ => trivial) borrowed

theorem ReplacementSitesAt.coerceTo (le : LEnv) (before : LS) (target : Ty) (value : ValueId) (origin : OriginId) :
    ReplacementSitesAt le before (Goose.Lower.coerceTo target value origin) := by
  intro checked
  cases run : Goose.Lower.coerceTo target value origin le before with
  | mk result after =>
    change ReplacementSitesBuilder le after
    rcases coerceTo_cases run with
      ⟨_, same⟩ | ⟨element, _, emitted⟩ | ⟨element, view, middle, _, viewRun, sliceRun⟩
    · rw [same]; exact checked
    · exact checked.emitDef (op := .refFreeze value) (fun _ => trivial) emitted
    · exact (checked.emitDef (op := .sliceView value) (fun _ => trivial) viewRun).emitDef
        (op := .viewSlice .readOnly view .omitted .omitted (some origin)) (fun _ => trivial) sliceRun

theorem ReplacementSitesAt.coerceSlot (le : LEnv) (before : LS) (slot : SlotId) (value : ValueId) (origin : OriginId) :
    ReplacementSitesAt le before (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  apply (ReplacementSitesAt.read _ _).bind
  simp only [read_apply]
  split
  · exact ReplacementSitesAt.coerceTo _ _ _ _ _
  · exact ReplacementSitesAt.pure _ _ _

theorem ReplacementSitesAt.coerceResult (le : LEnv) (before : LS) (value : ValueId) (origin : OriginId) :
    ReplacementSitesAt le before (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  apply (ReplacementSitesAt.read _ _).bind
  simp only [read_apply]
  split
  · exact ReplacementSitesAt.coerceTo _ _ _ _ _
  · exact ReplacementSitesAt.pure _ _ _

end Goose.Lower.Validation
