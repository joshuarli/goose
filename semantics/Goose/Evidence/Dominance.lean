import Goose.Evidence.CfgValidation

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

def predPush (n source : Nat) (acc : Array (List Nat)) (target : Nat) : Array (List Nat) :=
  if target < n then acc.modify target (source :: ·) else acc

def predUpdate (fn : Func) (acc : Array (List Nat)) (source : Nat) : Array (List Nat) :=
  match fn.blocks[source]? with
  | none => acc
  | some block => (block.terms.flatMap Term.successors).foldl (predPush fn.blocks.size source) acc

theorem predPush_size (n source : Nat) (acc : Array (List Nat)) (target : Nat) :
    (predPush n source acc target).size = acc.size := by
  unfold predPush
  split <;> simp

theorem predPush_preserve {n source target node parent : Nat} {acc : Array (List Nat)}
    (member : parent ∈ acc[node]?.getD []) : parent ∈ (predPush n source acc target)[node]?.getD [] := by
  unfold predPush
  split
  · rw [Array.getElem?_modify]
    split
    · cases found : acc[node]? with
      | none => simp [found] at member
      | some parents =>
        simp only [found, Option.getD_some] at member
        simp only [Option.map_some, Option.getD_some]
        exact List.mem_cons_of_mem _ member
    · exact member
  · exact member

theorem predPush_add {n source target : Nat} {acc : Array (List Nat)}
    (size : acc.size = n) (bound : target < n) : source ∈ (predPush n source acc target)[target]?.getD [] := by
  unfold predPush
  rw [if_pos bound, Array.getElem?_modify]
  simp only [ite_true]
  have inbounds : target < acc.size := by rw [size]; exact bound
  rw [Array.getElem?_eq_some_getElem! acc target inbounds]
  simp

theorem predList_size {n source : Nat} {acc : Array (List Nat)} (targets : List Nat) :
    (targets.foldl (predPush n source) acc).size = acc.size := by
  induction targets generalizing acc with
  | nil => rfl
  | cons target targets ih =>
    simp only [List.foldl_cons]
    exact ih.trans (predPush_size n source acc target)

theorem predList_preserve {n source node parent : Nat} {acc : Array (List Nat)} (targets : List Nat)
    (member : parent ∈ acc[node]?.getD []) :
    parent ∈ (targets.foldl (predPush n source) acc)[node]?.getD [] := by
  induction targets generalizing acc with
  | nil => exact member
  | cons target targets ih =>
    exact ih (predPush_preserve member)

theorem predList_add {n source target : Nat} {acc : Array (List Nat)} (targets : List Nat)
    (size : acc.size = n) (bound : target < n) (member : target ∈ targets) :
    source ∈ (targets.foldl (predPush n source) acc)[target]?.getD [] := by
  induction targets generalizing acc with
  | nil => simp at member
  | cons first targets ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with equal | member
    · subst first
      exact predList_preserve targets (predPush_add size bound)
    · exact ih ((predPush_size n source acc first).trans size) member

theorem predUpdate_size (fn : Func) (acc : Array (List Nat)) (source : Nat) :
    (predUpdate fn acc source).size = acc.size := by
  unfold predUpdate
  split
  · rfl
  · exact predList_size _

theorem predUpdate_preserve {fn : Func} {acc : Array (List Nat)} {node parent source : Nat}
    (member : parent ∈ acc[node]?.getD []) : parent ∈ (predUpdate fn acc source)[node]?.getD [] := by
  unfold predUpdate
  split
  · exact member
  · exact predList_preserve _ member

theorem predUpdate_add {fn : Func} {acc : Array (List Nat)} {block : Goose.GIR.Block} {source target : Nat}
    (size : acc.size = fn.blocks.size) (bound : target < fn.blocks.size)
    (found : fn.blocks[source]? = some block) (successor : target ∈ block.terms.flatMap Term.successors) :
    source ∈ (predUpdate fn acc source)[target]?.getD [] := by
  unfold predUpdate
  rw [found]
  exact predList_add _ size bound successor

theorem predScan_preserve {fn : Func} {acc : Array (List Nat)} {target parent : Nat} (sources : List Nat)
    (member : parent ∈ acc[target]?.getD []) :
    parent ∈ (sources.foldl (predUpdate fn) acc)[target]?.getD [] := by
  induction sources generalizing acc with
  | nil => exact member
  | cons source sources ih => exact ih (predUpdate_preserve member)

theorem predScan_add {fn : Func} {acc : Array (List Nat)} {block : Goose.GIR.Block} {source target : Nat}
    (sources : List Nat) (size : acc.size = fn.blocks.size) (bound : target < fn.blocks.size)
    (found : fn.blocks[source]? = some block) (successor : target ∈ block.terms.flatMap Term.successors)
    (member : source ∈ sources) : source ∈ (sources.foldl (predUpdate fn) acc)[target]?.getD [] := by
  induction sources generalizing acc with
  | nil => simp at member
  | cons first sources ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with equal | member
    · subst first
      exact predScan_preserve sources (predUpdate_add size bound found successor)
    · exact ih ((predUpdate_size fn acc first).trans size) member

theorem predecessors_successor {fn : Func} {block : Goose.GIR.Block} {source target : Nat}
    (found : fn.blocks[source]? = some block) (bound : target < fn.blocks.size)
    (successor : target ∈ block.terms.flatMap Term.successors) :
    source ∈ (predecessors fn)[target]?.getD [] := by
  have sourceBound := (Array.getElem?_eq_some_iff.mp found).1
  exact predScan_add (List.range fn.blocks.size) (by simp) bound found successor
    (List.mem_range.mpr sourceBound)

theorem predecessors_instAt {fn : Func} {pt : Pt} {term : Term} {target : Nat}
    (instruction : instAt fn pt = some (.term term)) (bound : target < fn.blocks.size)
    (successor : target ∈ term.successors) : pt.1 ∈ (predecessors fn)[target]?.getD [] := by
  unfold instAt at instruction
  cases found : fn.blocks[pt.1]? with
  | none => simp [found] at instruction
  | some block =>
    simp only [found, Option.bind_some] at instruction
    apply predecessors_successor found bound
    exact List.mem_flatMap.mpr ⟨term,
      List.mem_filterMap.mpr ⟨.term term, List.mem_of_getElem? instruction, rfl⟩, successor⟩

def DefinitionSite (fn : Func) (value block : Nat) (offset : Int) : Prop :=
  (offset = -1 ∧ ∃ body, fn.blocks[block]? = some body ∧ value ∈ body.params.map Prod.fst) ∨
    (∃ (index : Nat) (operation : Op), offset = (index : Int) ∧ instAt fn (block, index) = some (.def value operation))

theorem definitionLocation_site {fn : Func} {value block : Nat} {offset : Int}
    (member : (value, (block, offset)) ∈ fn.definitionLocations) : DefinitionSite fn value block offset := by
  obtain ⟨pair, hb, hloc⟩ := List.mem_flatMap.mp member
  rcases pair with ⟨body, id⟩
  have indexed := List.mem_zipIdx hb
  have found : fn.blocks[id]? = some body := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem (by simpa using indexed.2.1)]
    simp only [Nat.zero_add, Nat.sub_zero] at indexed
    rw [← indexed.2.2]
  simp only [Block.definitionLocations, List.mem_append] at hloc
  rcases hloc with parameter | definition
  · obtain ⟨param, hp, he⟩ := List.mem_map.mp parameter
    have valueEq : param.1 = value := congrArg Prod.fst he
    have siteEq : (id, (-1 : Int)) = (block, offset) := congrArg Prod.snd he
    cases siteEq
    exact Or.inl ⟨rfl, body, found, List.mem_map.mpr ⟨param, hp, valueEq⟩⟩
  · obtain ⟨pair, hi, he⟩ := List.mem_filterMap.mp definition
    rcases pair with ⟨inst, index⟩
    cases inst with
    | eff effect => simp at he
    | term term => simp at he
    | «def» result operation =>
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl, offsetEq⟩
      apply Or.inr
      refine ⟨index, operation, offsetEq.symm, ?_⟩
      have indexedInst := List.mem_zipIdx hi
      unfold instAt
      rw [found]
      simp only [Option.bind_some]
      rw [List.getElem?_eq_getElem (by simpa using indexedInst.2.1)]
      simp only [Nat.zero_add, Nat.sub_zero] at indexedInst
      rw [← indexedInst.2.2]

theorem ControlStep.source_bound {fn : Func} {before after : Pt}
    (step : ControlStep fn before after) : before.1 < fn.blocks.size := by
  have atSource : ∃ instruction, instAt fn before = some instruction := by
    cases step with
    | definition instruction => exact ⟨_, instruction⟩
    | effect instruction => exact ⟨_, instruction⟩
    | branch instruction _ => exact ⟨_, instruction⟩
  obtain ⟨instruction, found⟩ := atSource
  unfold instAt at found
  cases lookup : fn.blocks[before.1]? with
  | none => simp [lookup] at found
  | some block => exact (Array.getElem?_eq_some_iff.mp lookup).1

theorem ControlPath.source_bound {fn : Func} {ids : List ValueId} {first last : Pt}
    (path : ControlPath fn ids first last) (bound : last.1 < fn.blocks.size) : first.1 < fn.blocks.size := by
  cases path with
  | refl => exact bound
  | next transition _ _ => exact transition.source_bound

theorem ControlPath.definition_avoiding_predWalk {m : Goose.GIR.Module} {fn : Func} {id : ValueId}
    {operation : Op} {definitionPt last : Pt}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (definition : instAt fn definitionPt = some (.def id operation))
    (path : ControlPath fn [id] (0, 0) last)
    (past : last.1 ≠ definitionPt.1 ∨ definitionPt.2 < last.2)
    (lastBound : last.1 < fn.blocks.size) :
    ∃ length, PredWalk (predecessors fn) fn.blocks.size definitionPt.1 length last.1 := by
  have cannotEnter : ∀ point, ControlPath fn [id] point last → point = (definitionPt.1, 0) → False := by
    intro point suffix equal
    subst point
    have barrier := validated_definition_barrier valid member definition suffix ⟨rfl, by omega⟩
    rcases past with otherBlock | later
    · exact otherBlock barrier.1
    · omega
  have entryAvoids : 0 ≠ definitionPt.1 := by
    intro equal
    exact cannotEnter (0, 0) path (Prod.ext equal rfl)
  have entryBound := path.source_bound lastBound
  have initial : PredWalk (predecessors fn) fn.blocks.size definitionPt.1 0 0 := .entry entryBound entryAvoids
  have travel : ∀ {first : Pt}, ControlPath fn [id] first last →
      ∀ length, PredWalk (predecessors fn) fn.blocks.size definitionPt.1 length first.1 →
      ∃ distance, PredWalk (predecessors fn) fn.blocks.size definitionPt.1 distance last.1 := by
    intro first history
    induction history with
    | refl => intro length walk; exact ⟨length, walk⟩
    | @next first middle last step unwritten suffix ih =>
      intro length walk
      cases step with
      | definition instruction => exact ih path past lastBound cannotEnter length walk
      | effect instruction => exact ih path past lastBound cannotEnter length walk
      | @branch term target instruction successor =>
        have targetBound := suffix.source_bound lastBound
        have targetAvoids : target ≠ definitionPt.1 := by
          intro equal
          exact cannotEnter (target, 0) suffix (Prod.ext equal rfl)
        exact ih path past lastBound cannotEnter (length + 1) (PredWalk.next walk targetBound targetAvoids
          (predecessors_instAt instruction targetBound successor))
  exact travel path 0 initial

def EntryParameter (fn : Func) (value : ValueId) : Prop :=
  ∃ body, fn.blocks[0]? = some body ∧ value ∈ body.params.map Prod.fst

theorem ControlPath.parameter_avoiding_predWalk {fn : Func} {id block : ValueId}
    {body : Goose.GIR.Block} {last : Pt}
    (parameter : id ∈ body.params.map Prod.fst) (found : fn.blocks[block]? = some body)
    (nonentry : block ≠ 0) (path : ControlPath fn [id] (0, 0) last)
    (lastBound : last.1 < fn.blocks.size) :
    ∃ length, PredWalk (predecessors fn) fn.blocks.size block length last.1 := by
  have initial : PredWalk (predecessors fn) fn.blocks.size block 0 0 :=
    .entry (path.source_bound lastBound) nonentry.symm
  have travel : ∀ {first : Pt}, ControlPath fn [id] first last →
      ∀ length, PredWalk (predecessors fn) fn.blocks.size block length first.1 →
      ∃ distance, PredWalk (predecessors fn) fn.blocks.size block distance last.1 := by
    intro first history
    induction history with
    | refl => intro length walk; exact ⟨length, walk⟩
    | @next first middle last step unwritten suffix ih =>
      intro length walk
      cases step with
      | definition instruction => exact ih path lastBound length walk
      | effect instruction => exact ih path lastBound length walk
      | @branch term target instruction successor =>
        have targetBound := suffix.source_bound lastBound
        have targetAvoids : target ≠ block := by
          intro equal
          subst target
          have excluded := unwritten id (by simp)
          simp only [stepWrites, instruction, found, Option.map_some, Option.getD_some] at excluded
          exact excluded parameter
        exact ih path lastBound (length + 1) (PredWalk.next walk targetBound targetAvoids
          (predecessors_instAt instruction targetBound successor))
  exact travel path 0 initial

theorem instAt_block_bound {fn : Func} {pt : Pt} {instruction : Inst}
    (found : instAt fn pt = some instruction) : pt.1 < fn.blocks.size := by
  unfold instAt at found
  cases lookup : fn.blocks[pt.1]? with
  | none => simp [lookup] at found
  | some block => exact (Array.getElem?_eq_some_iff.mp lookup).1

theorem validated_operand_avoiding_path {m : Goose.GIR.Module} {fn : Func}
    {pt : Pt} {instruction : Inst} {value : ValueId}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (atPoint : instAt fn pt = some instruction) (operand : value ∈ instruction.uses)
    (path : ControlPath fn [value] (0, 0) pt) : EntryParameter fn value := by
  obtain ⟨block, offset, location, _, dominance⟩ :=
    validated_operand_definition valid member atPoint operand
  have site := definitionLocation_site location
  have lastBound := instAt_block_bound atPoint
  rcases site with ⟨rfl, body, found, parameter⟩ | ⟨index, operation, rfl, definition⟩
  · by_cases entry : block = 0
    · subst block
      exact ⟨body, found, parameter⟩
    · obtain ⟨length, walk⟩ := ControlPath.parameter_avoiding_predWalk parameter found entry path lastBound
      by_cases sameBlock : block = pt.1
      · exact False.elim (walk.avoids sameBlock.symm)
      · have mask : domBit (dominators fn (predecessors fn)) pt.1 block = true := by
          simpa only [if_neg sameBlock, domBit] using dominance
        rw [dominators_predWalk_sound walk] at mask
        contradiction
  · have past : pt.1 ≠ block ∨ index < pt.2 := by
      by_cases sameBlock : block = pt.1
      · right
        simp only [if_pos sameBlock] at dominance
        omega
      · exact Or.inl (Ne.symm sameBlock)
    obtain ⟨length, walk⟩ := ControlPath.definition_avoiding_predWalk valid member definition path past lastBound
    by_cases sameBlock : block = pt.1
    · exact False.elim (walk.avoids sameBlock.symm)
    · have mask : domBit (dominators fn (predecessors fn)) pt.1 block = true := by
        simpa only [if_neg sameBlock, domBit] using dominance
      rw [dominators_predWalk_sound walk] at mask
      contradiction

theorem ControlStep.write_location {fn : Func} {before after : Pt} {value : ValueId}
    (step : ControlStep fn before after) (written : value ∈ stepWrites fn before after) :
    (value, (after.1, (after.2 : Int) - 1)) ∈ fn.definitionLocations := by
  cases step with
  | definition instruction =>
    simp only [stepWrites, instruction, List.mem_singleton] at written
    subst value
    have offset : ((before.2 + 1 : Nat) : Int) - 1 = (before.2 : Int) := by omega
    simp only [offset]
    exact definitionLocation_mem instruction
  | effect instruction => simp [stepWrites, instruction] at written
  | @branch term target instruction successor =>
    simp only [stepWrites, instruction] at written
    cases found : fn.blocks[target]? with
    | none => simp [found] at written
    | some block =>
      simp only [found, Option.map_some, Option.getD_some] at written
      simpa using parameterLocation_mem found written

theorem validated_write_endpoints_unique {m : Goose.GIR.Module} {fn : Func} {value : ValueId}
    {leftBefore leftAfter rightBefore rightAfter : Pt}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (leftStep : ControlStep fn leftBefore leftAfter) (leftWrite : value ∈ stepWrites fn leftBefore leftAfter)
    (rightStep : ControlStep fn rightBefore rightAfter) (rightWrite : value ∈ stepWrites fn rightBefore rightAfter) :
    leftAfter = rightAfter := by
  have equal := validated_definition_locations_unique valid member
    (leftStep.write_location leftWrite) (rightStep.write_location rightWrite)
  apply Prod.ext
  · exact congrArg (fun row : Nat × Int => row.1) equal
  · have indices := congrArg (fun row : Nat × Int => row.2) equal
    omega

theorem validated_definition_write_source {m : Goose.GIR.Module} {fn : Func} {value : ValueId}
    {operation : Op} {definitionPt before after : Pt}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (definition : instAt fn definitionPt = some (.def value operation))
    (step : ControlStep fn before after) (written : value ∈ stepWrites fn before after) : before = definitionPt := by
  cases step with
  | definition instruction =>
    simp only [stepWrites, instruction, List.mem_singleton] at written
    subst value
    exact validated_instAt_def_unique valid member instruction definition
  | effect instruction => simp [stepWrites, instruction] at written
  | @branch term target instruction successor =>
    have sampleStep : ControlStep fn definitionPt (definitionPt.1, definitionPt.2 + 1) := .definition definition
    have sampleWrite : value ∈ stepWrites fn definitionPt (definitionPt.1, definitionPt.2 + 1) := by
      simp [stepWrites, definition]
    have equal := validated_write_endpoints_unique valid member sampleStep sampleWrite
      (.branch instruction successor) written
    have indices := congrArg Prod.snd equal
    omega

theorem ControlPath.avoid_to_definition {fn : Func} {value : ValueId} {first definitionPt : Pt}
    (path : ControlPath fn [] first definitionPt)
    (source : ∀ {before after}, ControlStep fn before after →
      value ∈ stepWrites fn before after → before = definitionPt) :
    ControlPath fn [value] first definitionPt := by
  induction path with
  | refl => exact .refl
  | @next first middle last step unwritten suffix ih =>
    by_cases written : value ∈ stepWrites fn first middle
    · have equal := source step written
      subst first
      exact .refl
    · exact .next step (by intro id member; simpa using (List.mem_singleton.mp member) ▸ written) (ih source)

theorem ControlPath.find_write_prefix {fn : Func} {ids : List ValueId} {value : ValueId} {first last : Pt}
    (path : ControlPath fn ids first last) :
    ControlPath fn [value] first last ∨
      ∃ before after, ControlPath fn ids first after ∧ ControlStep fn before after ∧
        value ∈ stepWrites fn before after := by
  induction path with
  | refl => exact Or.inl .refl
  | @next first middle last step unwritten suffix ih =>
    by_cases written : value ∈ stepWrites fn first middle
    · exact Or.inr ⟨first, middle, .next step unwritten .refl, step, written⟩
    · rcases ih with avoided | ⟨before, after, prior, foundStep, foundWrite⟩
      · exact Or.inl (.next step (by intro id member; simpa using (List.mem_singleton.mp member) ▸ written) avoided)
      · exact Or.inr ⟨before, after, .next step unwritten prior, foundStep, foundWrite⟩

theorem validated_entry_parameter_unwritten {m : Goose.GIR.Module} {fn : Func} {value : ValueId}
    {before after : Pt} (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (parameter : EntryParameter fn value) (step : ControlStep fn before after) :
    value ∉ stepWrites fn before after := by
  intro written
  obtain ⟨body, found, param⟩ := parameter
  have equal := validated_definition_locations_unique valid member
    (step.write_location written) (parameterLocation_mem found param)
  have blockEqual := congrArg (fun row : Nat × Int => row.1) equal
  have indexEqual := congrArg (fun row : Nat × Int => row.2) equal
  cases step with
  | definition instruction => dsimp only at indexEqual; omega
  | effect instruction => simp [stepWrites, instruction] at written
  | @branch term target instruction successor =>
    dsimp only at blockEqual
    subst target
    have targetBound := (Array.getElem?_eq_some_iff.mp found).1
    have predecessor := predecessors_instAt instruction targetBound successor
    rw [validated_entry_predecessors valid member] at predecessor
    simp at predecessor

theorem validated_comparison_operand_unwritten {m : Goose.GIR.Module} {fn : Func}
    {condition operand : ValueId} {comparison : Op} {samplePt before after branchPt : Pt}
    {yes no : BlockId} {yesArgs noArgs : List ValueId}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (found : fn.defOp? condition = some comparison)
    (sample : instAt fn samplePt = some (.def condition comparison))
    (entryPath : ControlPath fn [] (0, 0) samplePt)
    (operandUse : operand ∈ comparison.uses)
    (step : ControlStep fn before after)
    (suffix : ControlPath fn [condition] after branchPt)
    (branch : instAt fn branchPt = some (.term (.condbr condition yes yesArgs no noArgs))) :
    operand ∉ stepWrites fn before after := by
  intro written
  have entryAvoids := entryPath.avoid_to_definition (validated_definition_write_source valid member sample)
  rcases entryAvoids.find_write_prefix (value := operand) with operandAvoids |
      ⟨writeBefore, writeAfter, prior, writeStep, writeValue⟩
  · have parameter := validated_operand_avoiding_path valid member sample operandUse operandAvoids
    exact validated_entry_parameter_unwritten valid member parameter step written
  · have equal := validated_write_endpoints_unique valid member writeStep writeValue step written
    rw [equal] at prior
    have entryBranch := prior.trans suffix
    have parameter := validated_operand_avoiding_path valid member branch (by simp [Inst.uses, Term.uses]) entryBranch
    obtain ⟨body, bodyFound, parameterMem⟩ := parameter
    exact validated_defOp_not_param valid member found body (Array.mem_of_getElem? bodyFound) parameterMem

theorem validated_cmp_operands_unwritten {m : Goose.GIR.Module} {fn : Func}
    {condition i n : ValueId} {samplePt before after branchPt : Pt}
    {yes no : BlockId} {yesArgs noArgs : List ValueId}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (found : fn.defOp? condition = some (.cmp .lt .i64 i n))
    (sample : instAt fn samplePt = some (.def condition (.cmp .lt .i64 i n)))
    (entryPath : ControlPath fn [] (0, 0) samplePt)
    (step : ControlStep fn before after)
    (suffix : ControlPath fn [condition] after branchPt)
    (branch : instAt fn branchPt = some (.term (.condbr condition yes yesArgs no noArgs))) :
    i ∉ stepWrites fn before after ∧ n ∉ stepWrites fn before after := by
  constructor
  · exact validated_comparison_operand_unwritten valid member found sample entryPath
      (by simp [Op.uses]) step suffix branch
  · exact validated_comparison_operand_unwritten valid member found sample entryPath
      (by simp [Op.uses]) step suffix branch

end Goose.Evidence
