import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.Core.Sound

theorem source_reference_argument_cached {typingEnv : TEnv} {place : Place} {info : PlaceInfo}
    {start finish : Nat} {mutability : Mutability} {results : List Ty}
    {before after : LS} {value : ValueId}
    (source : Core.tyPlace typingEnv place start = .ok (info, finish))
    (writable : mutability = .mutable → info.referenceWritable typingEnv.mod.profile = true)
    (generated : GeneratedBuilderState before)
    (run : lowerArg (.byRef mutability place) (lowerEnv typingEnv.mod typingEnv.vars results) before = (value, after))
    (live : after.cur.isSome = true) :
    after.vals[value]? = some (some (.data (.ref mutability info.ty))) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  have actual := run
  simp only [lowerArg] at actual
  obtain ⟨address, middle, placeRun, borrowRun⟩ := bind_eq.mp actual
  have placeLive := (dead_borrowTo mutability address).live_before borrowRun live
  have cached : after.vals[value]? = some (some (.data (.ref mutability info.ty))) := by
    cases mutability with
    | readOnly =>
      obtain ⟨actualMu, placeTyped⟩ := lowerPlace_generated_typed place source placeRun placeLive generated
      cases current : middle.cur with
      | none => simp [current] at placeLive
      | some block =>
        have permission : actualMu.atLeast .readOnly = true := by cases actualMu <;> rfl
        have recorded := lowerArg_byRef_typed_of_place placeRun placeTyped permission current
        rw [run] at recorded
        exact recorded
    | mutable =>
      have placeTyped := lowerPlace_generated_writable_typed place source (writable rfl) placeRun placeLive generated
      cases current : middle.cur with
      | none => simp [current] at placeLive
      | some block =>
        have recorded := lowerArg_byRef_typed_of_place (requested := .mutable) placeRun placeTyped (by rfl) current
        rw [run] at recorded
        exact recorded
  exact cached


theorem source_reference_argument_type {typingEnv : TEnv} {place : Place} {info : PlaceInfo}
    {start finish : Nat} {mutability : Mutability} {results : List Ty}
    {before after : LS} {value : ValueId} {types : Array (Option VTy)}
    (source : Core.tyPlace typingEnv place start = .ok (info, finish))
    (writable : mutability = .mutable → info.referenceWritable typingEnv.mod.profile = true)
    (generated : GeneratedBuilderState before)
    (run : lowerArg (.byRef mutability place) (lowerEnv typingEnv.mod typingEnv.vars results) before = (value, after))
    (native : SummaryPreservation.NativeRows types after)
    (live : after.cur.isSome = true) :
    types[value]? = some (some (.data (.ref mutability info.ty))) :=
  native value _ (source_reference_argument_cached source writable generated run live)

#print axioms source_reference_argument_cached

#print axioms source_reference_argument_type

end Goose.Lower.Validation.ReplacementContentFlowSource
