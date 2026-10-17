import Goose.Lower.Validation.ShrinkPropagation

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem freshRuns_literal (func : Func) (types : Array (Option VTy))
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result : ValueId} {ty : Ty} {values : List ValueId}
    (literal : Inst.def result (.arrLit ty values) ∈ block.insts)
    (runType : isLiteralRunType ty = true) (typed : types[result]? = some (some (.data ty)))
    (bounded : result < func.numValues) : (freshRuns func types)[result]? = some true := by
  let seed : Array Bool := literalRunSeeds func types
  have seeded : seed[result]? = some true := by
    unfold seed literalRunSeeds
    change (Id.run (forIn (m := Id) func.blocks (Array.replicate func.numValues false) _))[result]? = some true
    rw [← Array.forIn_toList]
    refine list_forIn_establishes (property := fun flags : Array Bool => flags.size = func.numValues)
      (known := fun flags => flags[result]? = some true) _ _ _ block blockMember ?_ ?_ ?_ ?_ ?_
    · simp
    · intro body flags size
      apply list_forIn_state_invariant (property := fun flags : Array Bool => flags.size = func.numValues)
      · exact size
      · intro inst flags size
        cases inst with
        | «def» r op =>
          cases op <;> try exact size
          dsimp only
          split
          · change (flags.set! r true).size = func.numValues
            simpa only [Array.size_set!] using size
          · exact size
        | _ => exact size
    · intro body flags known
      apply list_forIn_state_invariant (property := fun flags : Array Bool => flags[result]? = some true)
      · exact known
      · intro inst flags known
        cases inst with
        | «def» r op =>
          cases op <;> try exact known
          dsimp only
          split
          · exact (trueFlags_set flags r).2 result known
          · exact known
        | _ => exact known
    · intro body flags
      exact ⟨_, rfl⟩
    · intro flags size
      change (Id.run (forIn (m := Id) block.insts flags _))[result]? = some true
      refine list_forIn_establishes (property := fun flags : Array Bool => flags.size = func.numValues)
        (known := fun flags => flags[result]? = some true) _ _ _ _ literal size ?_ ?_ ?_ ?_
      · intro inst flags size
        cases inst with
        | «def» r op =>
          cases op <;> try exact size
          dsimp only
          split
          · change (flags.set! r true).size = func.numValues
            simpa only [Array.size_set!] using size
          · exact size
        | _ => exact size
      · intro inst flags known
        cases inst with
        | «def» r op =>
          cases op <;> try exact known
          dsimp only
          split
          · exact (trueFlags_set flags r).2 result known
          · exact known
        | _ => exact known
      · intro inst flags
        cases inst with
        | «def» r op =>
          cases op <;> try exact ⟨_, rfl⟩
          dsimp only
          split <;> exact ⟨_, rfl⟩
        | _ => exact ⟨_, rfl⟩
      · intro flags size
        simp only [runType, typed, beq_self_eq_true, Bool.and_self, ite_true]
        change (flags.setIfInBounds result true)[result]? = some true
        simp [size, bounded]
  have retained : TrueFlagsPreserved seed
      (dataflowRounds (freshRunRound func) seed true (func.numValues + 1)) := by
    apply dataflowRounds_invariant
    · intro state checked
      exact checked.trans (freshRunRound_preserves_true func state)
    · exact .refl seed
  have algorithm : freshRuns func types =
      dataflowRounds (freshRunRound func) seed true (func.numValues + 1) := by
    rfl
  rw [algorithm]
  exact retained.2 result seeded

end Goose.Lower.Validation
