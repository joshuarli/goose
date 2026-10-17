import Goose.Lower.Validation.ReplacementScopedOperandsActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def RhsValueFresh (floor : Nat) (state : LS) (value : ValueId) : Prop :=
  state.cur.isSome = true → floor ≤ value

theorem RhsValueFresh.after {floor value : Nat} {before after : LS} {env : LEnv}
    {action : B α} {result : α} (fresh : RhsValueFresh floor before value)
    (dead : DeadRun action) (run : action env before = (result, after)) :
    RhsValueFresh floor after value := fun live => fresh (live_before dead run live)

theorem RhsValueFresh.output {floor : Nat} {before after : LS} {env : LEnv}
    {action : B ValueId} {value : ValueId} (floorBound : floor ≤ before.vals.size)
    (fresh : FreshValueRun action) (run : action env before = (value, after)) :
    RhsValueFresh floor after value :=
  fun live => Nat.le_trans floorBound (fresh env before value after run live)

theorem RhsOperandsAt.freezeTo (floor : Nat) (env : LEnv) (before : LS)
    (mu : Mutability) (value : ValueId) (fresh : RhsValueFresh floor before value) :
    RhsOperandsAt floor env before (Goose.Lower.freezeTo mu value) := by
  cases run : Goose.Lower.freezeTo mu value env before with
  | mk result after =>
    rcases freezeTo_cases run with ⟨_, same⟩ | emitted
    · apply RhsOperandsAt.of_blocks
      rw [run, same]
    · have receipt := RhsOperandsAt.emitDef floor env before (.refFreeze value)
        (by simpa only [Op.uses, List.mem_singleton] using fun live source equal => equal ▸ fresh live)
      change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.freezeTo mu value env before).2
      rw [run]
      change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.emitDef (.refFreeze value) env before).2 at receipt
      rw [emitted] at receipt
      exact receipt

theorem RhsOperandsAt.borrowTo (floor : Nat) (env : LEnv) (before : LS)
    (mu : Mutability) (value : ValueId) (fresh : RhsValueFresh floor before value) :
    RhsOperandsAt floor env before (Goose.Lower.borrowTo mu value) := by
  cases run : Goose.Lower.borrowTo mu value env before with
  | mk result after =>
    rcases borrowTo_cases run with frozen | emitted
    · have receipt := RhsOperandsAt.freezeTo floor env before mu value fresh
      change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.borrowTo mu value env before).2
      rw [run]
      change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.freezeTo mu value env before).2 at receipt
      rw [frozen] at receipt
      exact receipt
    · have receipt := RhsOperandsAt.emitDef floor env before (.ownerBorrow value)
        (by simpa only [Op.uses, List.mem_singleton] using fun live source equal => equal ▸ fresh live)
      change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.borrowTo mu value env before).2
      rw [run]
      change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.emitDef (.ownerBorrow value) env before).2 at receipt
      rw [emitted] at receipt
      exact receipt

theorem RhsOperandsAt.coerceTo (floor : Nat) (env : LEnv) (before : LS)
    (target : Ty) (value : ValueId) (origin : OriginId)
    (floorBound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before value) :
    RhsOperandsAt floor env before (Goose.Lower.coerceTo target value origin) := by
  cases run : Goose.Lower.coerceTo target value origin env before with
  | mk result after =>
    change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.coerceTo target value origin env before).2
    rw [run]
    rcases coerceTo_cases run with
      ⟨_, same⟩ | ⟨element, _, emitted⟩ | ⟨element, view, middle, _, viewRun, sliceRun⟩
    · exact EmitsOnly.of_blocks (congrArg LS.blocks same)
    · have receipt := RhsOperandsAt.emitDef floor env before (.refFreeze value)
        (by simpa only [Op.uses, List.mem_singleton] using fun live source equal => equal ▸ fresh live)
      change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.emitDef (.refFreeze value) env before).2 at receipt
      simpa only [emitted] using receipt
    · have first := RhsOperandsAt.emitDef floor env before (.sliceView value)
        (by simpa only [Op.uses, List.mem_singleton] using fun live source equal => equal ▸ fresh live)
      have viewFresh := RhsValueFresh.output floorBound (freshValue_emitDef _) viewRun
      have second := RhsOperandsAt.emitDef floor env middle
        (.viewSlice .readOnly view .omitted .omitted (some origin))
        (by simpa only [Op.uses, Bnd.uses, List.append_nil, List.mem_singleton] using
          fun live source equal => equal ▸ viewFresh live)
      change EmitsOnly (RhsUsesFresh floor) before (Goose.Lower.emitDef (.sliceView value) env before).2 at first
      change EmitsOnly (RhsUsesFresh floor) middle
        (Goose.Lower.emitDef (.viewSlice .readOnly view .omitted .omitted (some origin)) env middle).2 at second
      rw [viewRun] at first
      rw [sliceRun] at second
      exact first.trans second

theorem RhsOperandsAt.coerceSlot (floor : Nat) (env : LEnv) (before : LS)
    (slot : SlotId) (value : ValueId) (origin : OriginId)
    (floorBound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before value) :
    RhsOperandsAt floor env before (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  apply (RhsOperandsAt.read _ _ _).bind
  simp only [read_apply]
  split
  · exact RhsOperandsAt.coerceTo _ _ _ _ _ _ floorBound fresh
  · exact RhsOperandsAt.pure _ _ _ _

theorem RhsOperandsAt.coerceResult (floor : Nat) (env : LEnv) (before : LS)
    (value : ValueId) (origin : OriginId)
    (floorBound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before value) :
    RhsOperandsAt floor env before (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  apply (RhsOperandsAt.read _ _ _).bind
  simp only [read_apply]
  split
  · exact RhsOperandsAt.coerceTo _ _ _ _ _ _ floorBound fresh
  · exact RhsOperandsAt.pure _ _ _ _

end Goose.Lower.Validation
