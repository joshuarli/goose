import Goose.Evidence.SSA

namespace Goose.Evidence

open Goose.Core Goose.GIR

def domBit (masks : Array Nat) (block dominator : Nat) : Bool :=
  (masks[block]?.getD 0).testBit dominator

inductive PredWalk (preds : Array (List BlockId)) (n blocked : Nat) : Nat → BlockId → Prop
  | entry (bound : 0 < n) (avoids : 0 ≠ blocked) : PredWalk preds n blocked 0 0
  | next {length before after}
      (prior : PredWalk preds n blocked length before)
      (bound : after < n) (avoids : after ≠ blocked)
      (edge : before ∈ preds[after]?.getD []) : PredWalk preds n blocked (length + 1) after

def ZeroUpTo (preds : Array (List BlockId)) (n blocked budget : Nat) (masks : Array Nat) : Prop :=
  ∀ length block, length ≤ budget → PredWalk preds n blocked length block →
    domBit masks block blocked = false

def domUpdate (preds : Array (List BlockId)) (full : Nat)
    (state : Array Nat × Bool) (block : Nat) : Array Nat × Bool :=
  if block = 0 then state
  else
    let intersection := (preds[block]?.getD []).foldl
      (fun acc parent => acc &&& (state.1[parent]?.getD 0)) full
    let mask := intersection ||| (1 <<< block)
    if mask != (state.1[block]?.getD 0) then (state.1.set! block mask, true) else state

def domRound (preds : Array (List BlockId)) (n full : Nat) (masks : Array Nat) :
    Array Nat × Bool := (List.range n).foldl (domUpdate preds full) (masks, false)

theorem PredWalk.bound {preds : Array (List BlockId)} {n blocked length block : Nat}
    (walk : PredWalk preds n blocked length block) : block < n := by
  cases walk with
  | entry bound _ => exact bound
  | next _ bound _ _ => exact bound

theorem PredWalk.avoids {preds : Array (List BlockId)} {n blocked length block : Nat}
    (walk : PredWalk preds n blocked length block) : block ≠ blocked := by
  cases walk with
  | entry _ avoids => exact avoids
  | next _ _ avoids _ => exact avoids

theorem bit_intersection_preserve_zero {masks : Array Nat} {parents : List Nat}
    {full blocked : Nat} (zero : full.testBit blocked = false) :
    (parents.foldl (fun acc p => acc &&& (masks[p]?.getD 0)) full).testBit blocked = false := by
  induction parents generalizing full with
  | nil => exact zero
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih (by simp [Nat.testBit_and, zero])

theorem bit_intersection_zero {masks : Array Nat} {parents : List Nat} {full blocked parent : Nat}
    (member : parent ∈ parents) (zero : domBit masks parent blocked = false) :
    (parents.foldl (fun acc p => acc &&& (masks[p]?.getD 0)) full).testBit blocked = false := by
  induction parents generalizing full with
  | nil => simp at member
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with rfl | member
    · apply bit_intersection_preserve_zero
      simp only [Nat.testBit_and]
      simp only [domBit] at zero
      simp [zero]
    · exact ih member

theorem singleton_bit_zero {block blocked : Nat} (hne : block ≠ blocked) :
    (1 <<< block).testBit blocked = false := by
  simp only [Nat.testBit_shiftLeft]
  by_cases hle : block ≤ blocked
  · have hlt : block < blocked := by omega
    simp [hle, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega : blocked - block ≠ 0))]
  · simp [hle]

theorem domUpdate_size {preds : Array (List BlockId)} {full : Nat}
    (state : Array Nat × Bool) (block : Nat) :
    (domUpdate preds full state block).1.size = state.1.size := by
  unfold domUpdate
  split
  · rfl
  · dsimp only
    split <;> simp

theorem domUpdate_zero {preds : Array (List BlockId)} {n blocked budget full : Nat}
    {state : Array Nat × Bool} {changedBlock : Nat}
    (size : state.1.size = n) (zeros : ZeroUpTo preds n blocked budget state.1) :
    ZeroUpTo preds n blocked budget (domUpdate preds full state changedBlock).1 := by
  intro length block bound walk
  unfold domUpdate
  split
  · exact zeros length block bound walk
  dsimp only
  split
  · rename_i hne changed
    by_cases equal : changedBlock = block
    · subst changedBlock
      have hblock : block ≠ 0 := hne
      cases walk with
      | entry _ _ => contradiction
      | next prior hb ha edge =>
        have hz := zeros _ _ (by omega) prior
        have hi := bit_intersection_zero edge hz (full := full)
        have hs := singleton_bit_zero ha
        have hsize : block < state.1.size := by rw [size]; exact hb
        simp only [domBit, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self_of_lt hsize, Option.getD_some, Nat.testBit_or]
        simp [hi, hs]
    · simp only [domBit, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne equal]
      exact zeros length block bound walk
  · exact zeros length block bound walk

theorem domUpdate_bit_ne {preds : Array (List BlockId)} {full : Nat}
    {state : Array Nat × Bool} {changedBlock block blocked : Nat} (hne : changedBlock ≠ block) :
    domBit (domUpdate preds full state changedBlock).1 block blocked = domBit state.1 block blocked := by
  unfold domUpdate
  split
  · rfl
  · dsimp only
    split
    · simp only [domBit, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hne]
    · rfl

theorem domUpdate_bit_at {preds : Array (List BlockId)} {full : Nat}
    {state : Array Nat × Bool} {block blocked : Nat}
    (bound : block < state.1.size) (nonentry : block ≠ 0) :
    domBit (domUpdate preds full state block).1 block blocked =
      ((preds[block]?.getD []).foldl (fun acc parent => acc &&& (state.1[parent]?.getD 0)) full
        ||| (1 <<< block)).testBit blocked := by
  unfold domUpdate
  rw [if_neg nonentry]
  dsimp only
  split
  · simp only [domBit, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt bound, Option.getD_some]
  · rename_i equal
    have heq :
        (preds[block]?.getD []).foldl (fun acc parent => acc &&& (state.1[parent]?.getD 0)) full
          ||| (1 <<< block) = state.1[block]?.getD 0 := by simpa using equal
    exact congrArg (Nat.testBit · blocked) heq.symm

theorem domUpdate_target_zero {preds : Array (List BlockId)} {n blocked budget full : Nat}
    {state : Array Nat × Bool} {length block : Nat}
    (size : state.1.size = n) (zeros : ZeroUpTo preds n blocked budget state.1)
    (bound : length ≤ budget + 1) (walk : PredWalk preds n blocked length block) :
    domBit (domUpdate preds full state block).1 block blocked = false := by
  cases walk with
  | entry hb ha =>
    simp only [domUpdate, ite_true]
    exact zeros 0 0 (by omega) (.entry hb ha)
  | next prior hb ha edge =>
    by_cases entry : block = 0
    · subst block
      simp only [domUpdate, ite_true]
      exact zeros 0 0 (by omega) (.entry (by omega) ha)
    · rw [domUpdate_bit_at (by rw [size]; exact hb) entry, Nat.testBit_or]
      have zero := zeros _ _ (by omega) prior
      simp [bit_intersection_zero edge zero (full := full), singleton_bit_zero ha]

theorem domUpdate_preserves_target_zero {preds : Array (List BlockId)} {n blocked budget full : Nat}
    {state : Array Nat × Bool} {length block changedBlock : Nat}
    (size : state.1.size = n) (zeros : ZeroUpTo preds n blocked budget state.1)
    (bound : length ≤ budget + 1) (walk : PredWalk preds n blocked length block)
    (zero : domBit state.1 block blocked = false) :
    domBit (domUpdate preds full state changedBlock).1 block blocked = false := by
  by_cases equal : changedBlock = block
  · subst changedBlock
    exact domUpdate_target_zero size zeros bound walk
  · rw [domUpdate_bit_ne equal]
    exact zero

theorem domScan_zero {preds : Array (List BlockId)} {n blocked budget full : Nat}
    {state : Array Nat × Bool} (blocks : List Nat)
    (size : state.1.size = n) (zeros : ZeroUpTo preds n blocked budget state.1) :
    (blocks.foldl (domUpdate preds full) state).1.size = n ∧
    ZeroUpTo preds n blocked budget (blocks.foldl (domUpdate preds full) state).1 ∧
    (∀ length block, length ≤ budget + 1 → PredWalk preds n blocked length block →
      (block ∈ blocks ∨ domBit state.1 block blocked = false) →
      domBit (blocks.foldl (domUpdate preds full) state).1 block blocked = false) := by
  induction blocks generalizing state with
  | nil =>
    refine ⟨size, zeros, ?_⟩
    intro length block bound walk known
    simpa using known
  | cons changedBlock blocks ih =>
    simp only [List.foldl_cons]
    have size' : (domUpdate preds full state changedBlock).1.size = n :=
      (domUpdate_size state changedBlock).trans size
    have zeros' := domUpdate_zero (full := full) (changedBlock := changedBlock) size zeros
    obtain ⟨hsize, hzeros, hprocessed⟩ := ih size' zeros'
    refine ⟨hsize, hzeros, ?_⟩
    intro length block bound walk known
    apply hprocessed length block bound walk
    rcases known with member | zero
    · rcases List.mem_cons.mp member with equal | member
      · subst block
        exact Or.inr (domUpdate_target_zero size zeros bound walk)
      · exact Or.inl member
    · exact Or.inr (domUpdate_preserves_target_zero size zeros bound walk zero)

theorem domRound_zero {preds : Array (List BlockId)} {n blocked budget full : Nat}
    {masks : Array Nat} (size : masks.size = n)
    (zeros : ZeroUpTo preds n blocked budget masks) :
    (domRound preds n full masks).1.size = n ∧
      ZeroUpTo preds n blocked (budget + 1) (domRound preds n full masks).1 := by
  obtain ⟨hsize, _, hzero⟩ := domScan_zero (state := (masks, false)) (List.range n) size zeros
  refine ⟨hsize, ?_⟩
  intro length block bound walk
  exact hzero length block bound walk (Or.inl (List.mem_range.mpr walk.bound))

theorem domUpdate_unchanged {preds : Array (List BlockId)} {full : Nat}
    {state : Array Nat × Bool} {block : Nat}
    (unchanged : (domUpdate preds full state block).2 = false) :
    state.2 = false ∧ (domUpdate preds full state block).1 = state.1 := by
  by_cases entry : block = 0
  · simp only [domUpdate, if_pos entry] at unchanged ⊢
    exact ⟨unchanged, by trivial⟩
  · simp only [domUpdate, if_neg entry] at unchanged ⊢
    try dsimp only at unchanged ⊢
    split
    · rename_i changed
      simp only [if_pos changed] at unchanged
      contradiction
    · rename_i equal
      simp only [if_neg equal] at unchanged
      exact ⟨unchanged, by trivial⟩

theorem domScan_unchanged {preds : Array (List BlockId)} {full : Nat}
    {state : Array Nat × Bool} (blocks : List Nat)
    (unchanged : (blocks.foldl (domUpdate preds full) state).2 = false) :
    state.2 = false ∧ (blocks.foldl (domUpdate preds full) state).1 = state.1 := by
  induction blocks generalizing state with
  | nil => exact ⟨unchanged, rfl⟩
  | cons block blocks ih =>
    simp only [List.foldl_cons] at unchanged ⊢
    obtain ⟨updateFalse, restEqual⟩ := ih unchanged
    obtain ⟨stateFalse, updateEqual⟩ := domUpdate_unchanged updateFalse
    exact ⟨stateFalse, restEqual.trans updateEqual⟩

theorem domRound_fixed_zero {preds : Array (List BlockId)} {n blocked budget full : Nat}
    {masks : Array Nat} (size : masks.size = n)
    (zeros : ZeroUpTo preds n blocked budget masks)
    (fixed : (domRound preds n full masks).1 = masks) (extra : Nat) :
    ZeroUpTo preds n blocked (budget + extra) masks := by
  induction extra with
  | zero => simpa using zeros
  | succ extra ih =>
    have hzero := (domRound_zero (full := full) size ih).2
    rw [fixed] at hzero
    simpa [Nat.add_assoc] using hzero

theorem dominators_go_zero {preds : Array (List BlockId)} {n blocked budget full fuel : Nat}
    {masks : Array Nat} (size : masks.size = n)
    (zeros : ZeroUpTo preds n blocked budget masks) :
    ZeroUpTo preds n blocked (budget + fuel) (dominators.go preds n full fuel masks) := by
  induction fuel generalizing budget masks with
  | zero => simpa [dominators.go] using zeros
  | succ fuel ih =>
    change ZeroUpTo preds n blocked (budget + (fuel + 1))
      (if (domRound preds n full masks).2 then
        dominators.go preds n full fuel (domRound preds n full masks).1
      else (domRound preds n full masks).1)
    obtain ⟨nextSize, nextZeros⟩ := domRound_zero (full := full) size zeros
    cases changed : (domRound preds n full masks).2 with
    | true =>
      simp only [changed, ite_true]
      have next := ih nextSize nextZeros
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next
    | false =>
      simp only [changed, Bool.false_eq_true, ite_false]
      have fixed : (domRound preds n full masks).1 = masks :=
        (domScan_unchanged (state := (masks, false)) (List.range n) changed).2
      rw [fixed]
      exact domRound_fixed_zero size zeros fixed (fuel + 1)

theorem dominators_initial_zero {preds : Array (List BlockId)} {n blocked full : Nat}
    (nonempty : 0 < n) :
    ZeroUpTo preds n blocked 0 ((Array.replicate n full).set! 0 1) := by
  intro length block bound walk
  cases walk with
  | entry hb ha =>
    have initialBound : 0 < (Array.replicate n full).size := by simpa using nonempty
    unfold domBit
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt initialBound]
    simpa using singleton_bit_zero ha
  | next prior hb ha edge => omega

theorem dominators_predWalk_zero {fn : Func} {preds : Array (List BlockId)}
    {blocked length block : Nat}
    (walk : PredWalk preds fn.blocks.size blocked length block)
    (bound : length ≤ fn.blocks.size + 2) :
    domBit (dominators fn preds) block blocked = false := by
  have nonempty : 0 < fn.blocks.size := by have hb := walk.bound; omega
  have initial := dominators_initial_zero (preds := preds)
    (blocked := blocked) (full := (1 <<< fn.blocks.size) - 1) nonempty
  have final := dominators_go_zero (full := (1 <<< fn.blocks.size) - 1)
    (fuel := fn.blocks.size + 2) (by simp) initial
  exact final length block (by simpa using bound) walk

theorem PredWalk.finite_witness {preds : Array (List BlockId)} {n blocked length block : Nat}
    (walk : PredWalk preds n blocked length block) :
    ∃ nodes : List Nat, nodes.Nodup ∧ (∀ node ∈ nodes, node < n) ∧ block ∈ nodes ∧
      (∀ node ∈ nodes, ∃ distance, distance < nodes.length ∧ PredWalk preds n blocked distance node) := by
  induction walk with
  | entry bound avoids =>
    refine ⟨[0], by simp, ?_, by simp, ?_⟩
    · intro node member
      simpa using (List.mem_singleton.mp member) ▸ bound
    · intro node member
      have equal := List.mem_singleton.mp member
      subst node
      exact ⟨0, by simp, .entry bound avoids⟩
  | @next length before after prior bound avoids edge ih =>
    obtain ⟨nodes, nodup, bounds, member, distances⟩ := ih
    by_cases existsNode : after ∈ nodes
    · exact ⟨nodes, nodup, bounds, existsNode, distances⟩
    · refine ⟨after :: nodes, List.nodup_cons.mpr ⟨existsNode, nodup⟩, ?_, by simp, ?_⟩
      · intro node member
        rcases List.mem_cons.mp member with equal | member
        · exact equal ▸ bound
        · exact bounds node member
      · intro node hnode
        rcases List.mem_cons.mp hnode with equal | hnode
        · subst node
          obtain ⟨distance, hdist, hwalk⟩ := distances before member
          exact ⟨distance + 1, by simp only [List.length_cons]; omega, .next hwalk bound avoids edge⟩
        · obtain ⟨distance, hdist, hwalk⟩ := distances node hnode
          exact ⟨distance, by simp only [List.length_cons]; omega, hwalk⟩

theorem PredWalk.short {preds : Array (List BlockId)} {n blocked length block : Nat}
    (walk : PredWalk preds n blocked length block) :
    ∃ distance, distance < n ∧ PredWalk preds n blocked distance block := by
  obtain ⟨nodes, nodup, bounds, member, distances⟩ := walk.finite_witness
  have size : nodes.length ≤ n := by
    simpa using nodup.length_le_of_subset (l₂ := List.range n)
      (fun node member => List.mem_range.mpr (bounds node member))
  obtain ⟨distance, bound, shortest⟩ := distances block member
  exact ⟨distance, by omega, shortest⟩

theorem dominators_predWalk_sound {fn : Func} {preds : Array (List BlockId)}
    {blocked length block : Nat} (walk : PredWalk preds fn.blocks.size blocked length block) :
    domBit (dominators fn preds) block blocked = false := by
  obtain ⟨distance, bound, shortest⟩ := walk.short
  exact dominators_predWalk_zero shortest (by omega)

end Goose.Evidence
