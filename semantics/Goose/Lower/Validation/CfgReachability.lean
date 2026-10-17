import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def cfgDiscover (size : Nat) (state : Array Bool × List BlockId) (target : BlockId) :
    Array Bool × List BlockId :=
  if target < size && !(state.1[target]?.getD true) then
    (state.1.set! target true, target :: state.2)
  else state

structure Discovery (initial current : Array Bool) (added : List BlockId) : Prop where
  size : current.size = initial.size
  retains : ∀ (block : BlockId), initial[block]? = some true → current[block]? = some true
  classifies : ∀ (block : BlockId), current[block]? = some true → initial[block]? = some true ∨ block ∈ added
  contains : ∀ (block : BlockId), block ∈ added → current[block]? = some true
  rank : current.count false + added.length = initial.count false

theorem Discovery.refl (seen : Array Bool) : Discovery seen seen [] :=
  ⟨rfl, fun _ row => row, fun _ row => Or.inl row, by simp, by simp⟩

theorem cfgDiscover_discovery {initial seen : Array Bool} {added : List BlockId}
    (discovery : Discovery initial seen added) (target : BlockId) :
    let next := cfgDiscover seen.size (seen, added) target
    Discovery initial next.1 next.2 := by
  unfold cfgDiscover
  split
  · rename_i unseen
    have bound : target < seen.size := by
      have both : target < seen.size ∧ !(seen[target]?.getD true) = true := by simpa using unseen
      exact both.1
    have row : seen[target]? = some false := by
      cases found : seen[target]? with
      | none => simp [found] at unseen
      | some value => cases value <;> simp_all
    have point : seen[target] = false := (Array.getElem?_eq_some_iff.mp row).2
    have positive : 0 < seen.count false :=
      Array.count_pos_iff.mpr (Array.mem_of_getElem? row)
    have nextSelf : (seen.set! target true)[target]? = some true := by
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt bound]
    have retain : ∀ (block : BlockId), seen[block]? = some true → (seen.set! target true)[block]? = some true := by
      intro block present
      by_cases same : target = block
      · subst block
        exact nextSelf
      · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same]
        exact present
    refine ⟨by simpa using discovery.size,
      fun block present => retain block (discovery.retains block present), ?_, ?_, ?_⟩
    · intro block present
      by_cases same : target = block
      · exact Or.inr (by simp [same])
      · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] at present
        rcases discovery.classifies block present with old | member
        · exact Or.inl old
        · exact Or.inr (by simp [member])
    · intro block member
      rcases List.mem_cons.mp member with same | member
      · subst block
        exact nextSelf
      · exact retain block (discovery.contains block member)
    · have count : (seen.set! target true).count false = seen.count false - 1 := by
        simp only [Array.set!, Array.setIfInBounds, bound, dite_true]
        rw [Array.count_set]
        simp [point]
      simp only [count, List.length_cons]
      have rank := discovery.rank
      omega
  · exact discovery

theorem cfgDiscover_retains (seen : Array Bool) (added : List BlockId) (target : BlockId)
    (block : BlockId) (present : seen[block]? = some true) :
    (cfgDiscover seen.size (seen, added) target).1[block]? = some true := by
  unfold cfgDiscover
  split
  · rename_i marked
    have bound : target < seen.size := by
      have both : target < seen.size ∧ !(seen[target]?.getD true) = true := by simpa using marked
      exact both.1
    by_cases same : target = block
    · subst block
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt bound]
    · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same]
      exact present
  · exact present

theorem cfgDiscover_marks (seen : Array Bool) (added : List BlockId) (target : BlockId)
    (bound : target < seen.size) :
    (cfgDiscover seen.size (seen, added) target).1[target]? = some true := by
  unfold cfgDiscover
  split
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt bound]
  · rename_i skipped
    cases row : seen[target]? with
    | none => exact False.elim (Nat.not_le_of_gt bound (Array.getElem?_eq_none_iff.mp row))
    | some value => cases value <;> simp_all

theorem cfgDiscover_fold {initial seen : Array Bool} {added : List BlockId}
    (discovery : Discovery initial seen added) (targets : List BlockId) :
    let next := targets.foldl (cfgDiscover initial.size) (seen, added)
    Discovery initial next.1 next.2 := by
  induction targets generalizing seen added with
  | nil => exact discovery
  | cons target rest ih =>
    rw [List.foldl_cons]
    have one := cfgDiscover_discovery discovery target
    rw [discovery.size] at one
    exact ih one

theorem cfgDiscover_size (size : Nat) (state : Array Bool × List BlockId) (target : BlockId) :
    (cfgDiscover size state target).1.size = state.1.size := by
  unfold cfgDiscover
  split <;> simp

theorem cfgDiscover_fold_retains (size : Nat) (targets : List BlockId)
    (seen : Array Bool) (added : List BlockId) (sized : seen.size = size)
    (block : BlockId) (present : seen[block]? = some true) :
    (targets.foldl (cfgDiscover size) (seen, added)).1[block]? = some true := by
  induction targets generalizing seen added with
  | nil => exact present
  | cons target rest ih =>
    rw [List.foldl_cons]
    apply ih _ _ ((cfgDiscover_size size _ target).trans sized)
    rw [← sized]
    exact cfgDiscover_retains seen added target block present

theorem cfgDiscover_fold_marks (size : Nat) (targets : List BlockId)
    (seen : Array Bool) (added : List BlockId) (sized : seen.size = size) :
    ∀ target ∈ targets, target < size →
      (targets.foldl (cfgDiscover size) (seen, added)).1[target]? = some true := by
  induction targets generalizing seen added with
  | nil => simp
  | cons target rest ih =>
    intro block member bound
    rw [List.foldl_cons]
    have nextSize := (cfgDiscover_size size (seen, added) target).trans sized
    rcases List.mem_cons.mp member with same | member
    · subst block
      apply cfgDiscover_fold_retains size rest _ _ nextSize
      rw [← sized]
      exact cfgDiscover_marks seen added target (by simpa [sized] using bound)
    · exact ih _ _ nextSize block member bound

def ReachabilityFrontier (func : Func) (seen : Array Bool) (pending : List BlockId) : Prop :=
  ∀ (block : BlockId) (body : GIR.Block), func.blocks[block]? = some body → seen[block]? = some true →
    block ∈ pending ∨
      ∀ target ∈ body.terms.flatMap Term.successors, target < func.blocks.size → seen[target]? = some true

def ReachabilityClosed (func : Func) (seen : Array Bool) : Prop :=
  ∀ (block : BlockId) (body : GIR.Block), func.blocks[block]? = some body → seen[block]? = some true →
    ∀ target ∈ body.terms.flatMap Term.successors, target < func.blocks.size → seen[target]? = some true

theorem reachability_frontier_step {func : Func} {seen : Array Bool} {block : BlockId}
    {pending : List BlockId} (size : seen.size = func.blocks.size)
    (frontier : ReachabilityFrontier func seen (block :: pending)) :
    let targets := match func.blocks[block]? with
      | some body => body.terms.flatMap Term.successors
      | none => []
    let next := targets.foldl (cfgDiscover func.blocks.size) (seen, [])
    ReachabilityFrontier func next.1 (next.2 ++ pending) := by
  dsimp only
  let targets := match func.blocks[block]? with
    | some body => body.terms.flatMap Term.successors
    | none => []
  have discovered := cfgDiscover_fold (Discovery.refl seen) targets
  rw [size] at discovered
  intro source body row marked
  rcases discovered.classifies source marked with old | added
  · rcases frontier source body row old with queued | closed
    · rcases List.mem_cons.mp queued with same | queued
      · subst source
        right
        have targetList : targets = body.terms.flatMap Term.successors := by simp [targets, row]
        rw [← targetList]
        exact cfgDiscover_fold_marks func.blocks.size targets seen [] size
      · left
        exact List.mem_append_right _ queued
    · right
      intro target member bound
      exact discovered.retains target (closed target member bound)
  · left
    exact List.mem_append_left _ added

theorem reachable_go_closes (func : Func) (fuel : Nat) (seen : Array Bool) (pending : List BlockId)
    (size : seen.size = func.blocks.size) (frontier : ReachabilityFrontier func seen pending)
    (budget : seen.count false + pending.length < fuel) :
    (reachable.go func func.blocks.size fuel pending seen).size = func.blocks.size ∧
      (∀ (block : BlockId), seen[block]? = some true →
        (reachable.go func func.blocks.size fuel pending seen)[block]? = some true) ∧
      ReachabilityClosed func (reachable.go func func.blocks.size fuel pending seen) := by
  induction fuel generalizing seen pending with
  | zero => omega
  | succ fuel ih =>
    cases pending with
    | nil =>
      refine ⟨size, fun _ row => row, ?_⟩
      intro block body row marked
      exact (frontier block body row marked).resolve_left (by simp)
    | cons block pending =>
      let targets := match func.blocks[block]? with
        | some body => body.terms.flatMap Term.successors
        | none => []
      let next := targets.foldl (cfgDiscover func.blocks.size) (seen, [])
      have discovered : Discovery seen next.1 next.2 := by
        have found := cfgDiscover_fold (Discovery.refl seen) targets
        simpa only [size] using found
      have nextSize : next.1.size = func.blocks.size := discovered.size.trans size
      have nextFrontier : ReachabilityFrontier func next.1 (next.2 ++ pending) :=
        reachability_frontier_step size frontier
      have nextBudget : next.1.count false + (next.2 ++ pending).length < fuel := by
        have rank := discovered.rank
        simp only [List.length_cons] at budget
        simp only [List.length_append]
        omega
      obtain ⟨finalSize, retained, closed⟩ := ih next.1 (next.2 ++ pending) nextSize nextFrontier nextBudget
      change (reachable.go func func.blocks.size fuel (next.2 ++ pending) next.1).size = _ ∧ _
      exact ⟨finalSize, fun block row => retained block (discovered.retains block row), closed⟩

theorem reachable_closed (func : Func) (nonempty : 0 < func.blocks.size) :
    (reachable func)[0]? = some true ∧ ReachabilityClosed func (reachable func) := by
  let initial := (Array.replicate func.blocks.size false).set! 0 true
  have initialSize : initial.size = func.blocks.size := by simp [initial]
  have initialEntry : initial[0]? = some true := by
    have bound : 0 < (Array.replicate func.blocks.size false).size := by simpa using nonempty
    simp only [initial, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt bound]
  have frontier : ReachabilityFrontier func initial [0] := by
    intro block body row marked
    by_cases entry : block = 0
    · left
      simp [entry]
    · have unchanged : initial[block]? = (Array.replicate func.blocks.size false)[block]? := by
        simp only [initial, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (Ne.symm entry)]
      rw [unchanged] at marked
      simp only [Array.getElem?_replicate] at marked
      split at marked <;> cases marked
  have initialCount : initial.count false = func.blocks.size - 1 := by
    simp only [initial, Array.set!, Array.setIfInBounds, Array.size_replicate,
      nonempty, dite_true]
    rw [Array.count_set]
    simp
  have closed := reachable_go_closes func (func.blocks.size + 1) initial [0] initialSize frontier
    (by simp only [initialCount, List.length_cons, List.length_nil]; omega)
  exact ⟨closed.2.1 0 initialEntry, closed.2.2⟩

inductive BlockReachable (func : Func) : BlockId → Prop
  | entry : BlockReachable func 0
  | next {source target : BlockId} {body : GIR.Block}
      (prior : BlockReachable func source) (row : func.blocks[source]? = some body)
      (successor : target ∈ body.terms.flatMap Term.successors) (bound : target < func.blocks.size) :
      BlockReachable func target

theorem reachable_marks_path {func : Func} {block : BlockId} (nonempty : 0 < func.blocks.size)
    (path : BlockReachable func block) : (reachable func)[block]? = some true := by
  obtain ⟨entry, closed⟩ := reachable_closed func nonempty
  induction path with
  | entry => exact entry
  | next prior row successor bound marked => exact closed _ _ row marked _ successor bound

theorem reachable_complete (func : Func) (nonempty : 0 < func.blocks.size)
    (paths : ∀ block, block < func.blocks.size → BlockReachable func block) :
    ∀ block, block < func.blocks.size → (reachable func)[block]? = some true :=
  fun block bound => reachable_marks_path nonempty (paths block bound)

theorem reachable_go_of_blocks {left right : Func} (same : left.blocks = right.blocks)
    (size fuel : Nat) (pending : List BlockId) (seen : Array Bool) :
    reachable.go left size fuel pending seen = reachable.go right size fuel pending seen := by
  induction fuel generalizing pending seen with
  | zero => rfl
  | succ fuel ih =>
    cases pending with
    | nil => rfl
    | cons block rest =>
      simp only [reachable.go, same]
      exact ih _ _

theorem reachable_of_blocks {left right : Func} (same : left.blocks = right.blocks) :
    reachable left = reachable right := by
  unfold reachable
  rw [same]
  exact reachable_go_of_blocks same _ _ _ _

end Goose.Lower.Validation
