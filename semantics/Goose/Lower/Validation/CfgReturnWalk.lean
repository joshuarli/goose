import Goose.Lower.Validation.CfgReturnPaths

namespace Goose.Lower.Validation

open Goose.GIR

private theorem return_seen_count {seen : Array Bool} {block : BlockId}
    (bound : block < seen.size) (unseen : seen[block]?.getD false = false) :
    (seen.set! block true).count false + 1 = seen.count false := by
  have row : seen[block]? = some false := by
    have present := Array.getElem?_eq_getElem bound
    cases value : seen[block] <;> simp_all
  have point : seen[block] = false := (Array.getElem?_eq_some_iff.mp row).2
  have positive : 0 < seen.count false := Array.count_pos_iff.mpr (Array.mem_of_getElem? row)
  have count : (seen.set! block true).count false = seen.count false - 1 := by
    simp only [Array.set!, Array.setIfInBounds, bound, dite_true]
    rw [Array.count_set]
    simp [point]
  omega

theorem return_walk_sound (mayReturn : Array Bool) (func : Func)
    (fuel : Nat) (pending : List BlockId) (seen : Array Bool)
    (sized : seen.size = func.blocks.size) (budget : seen.count false < fuel)
    (run : funcMayReturn.walk mayReturn func fuel pending seen = true) :
    ∃ block ∈ pending, ReturnPath mayReturn func block := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases pending with
    | nil => simp only [funcMayReturn.walk] at run; contradiction
    | cons block rest =>
      rw [funcMayReturn.walk] at run
      cases marked : seen[block]?.getD false with
      | true =>
        simp only [marked, ite_true] at run
        obtain ⟨target, member, path⟩ := return_walk_sound mayReturn func (fuel + 1) rest seen sized budget run
        exact ⟨target, by simp [member], path⟩
      | false =>
        simp only [marked, Bool.false_eq_true, ite_false] at run
        cases row : func.blocks[block]? with
        | none => exact ⟨block, by simp, .missing row⟩
        | some body =>
          simp only [row] at run
          have bound : block < seen.size := by
            rw [sized]
            exact (Array.getElem?_eq_some_iff.mp row).1
          have count := return_seen_count bound marked
          have nextSized : (seen.set! block true).size = func.blocks.size := by simpa using sized
          have nextBudget : (seen.set! block true).count false < fuel := by omega
          cases flow : blockReturnFlow mayReturn body.insts with
          | returns => exact ⟨block, by simp, .returns row flow⟩
          | stops =>
            simp only [flow] at run
            obtain ⟨target, member, path⟩ := return_walk_sound mayReturn func fuel rest
              (seen.set! block true) nextSized nextBudget run
            exact ⟨target, by simp [member], path⟩
          | branches targets =>
            simp only [flow] at run
            obtain ⟨target, member, path⟩ := return_walk_sound mayReturn func fuel (targets ++ rest)
              (seen.set! block true) nextSized nextBudget run
            rcases List.mem_append.mp member with next | old
            · exact ⟨block, by simp, .branch row flow next path⟩
            · exact ⟨target, by simp [old], path⟩
termination_by (fuel, pending.length)
decreasing_by all_goals simp_wf; simp_all only [List.length_cons]; omega

def ReturnBoundary (mayReturn : Array Bool) (func : Func) (seen : Array Bool)
    (closed : BlockId → Prop) : Prop :=
  ∀ block, closed block → seen[block]? = some true ∨
    ∃ body, func.blocks[block]? = some body ∧
      (blockReturnFlow mayReturn body.insts = .stops ∨
        ∃ targets, blockReturnFlow mayReturn body.insts = .branches targets ∧
          ∀ target ∈ targets, closed target)

private theorem return_boundary_unmark {mayReturn : Array Bool} {func : Func} {seen : Array Bool}
    {closed : BlockId → Prop} {block : BlockId} {body : Block}
    (row : func.blocks[block]? = some body)
    (flow : blockReturnFlow mayReturn body.insts = .stops ∨
      ∃ targets, blockReturnFlow mayReturn body.insts = .branches targets ∧
        ∀ target ∈ targets, closed target)
    (boundary : ReturnBoundary mayReturn func (seen.set! block true) closed) :
    ReturnBoundary mayReturn func seen closed := by
  intro target present
  rcases boundary target present with marked | safe
  · by_cases same : block = target
    · subst target
      exact Or.inr ⟨body, row, flow⟩
    · exact Or.inl (by simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using marked)
  · exact Or.inr safe

theorem return_walk_closed (mayReturn : Array Bool) (func : Func)
    (fuel : Nat) (pending : List BlockId) (seen : Array Bool)
    (sized : seen.size = func.blocks.size)
    (run : funcMayReturn.walk mayReturn func fuel pending seen = false) :
    ∃ closed : BlockId → Prop,
      (∀ block ∈ pending, closed block) ∧
      (∀ block, seen[block]? = some true → closed block) ∧
      ReturnBoundary mayReturn func seen closed := by
  cases fuel with
  | zero => simp only [funcMayReturn.walk] at run; contradiction
  | succ fuel =>
    cases pending with
    | nil =>
      exact ⟨fun block => seen[block]? = some true, by simp,
        fun _ found => found, fun _ found => Or.inl found⟩
    | cons block rest =>
      rw [funcMayReturn.walk] at run
      cases marked : seen[block]?.getD false with
      | true =>
        simp only [marked, ite_true] at run
        obtain ⟨closed, queued, contains, boundary⟩ := return_walk_closed mayReturn func (fuel + 1) rest seen sized run
        refine ⟨closed, ?_, contains, boundary⟩
        intro target member
        rcases List.mem_cons.mp member with same | old
        · subst target
          apply contains
          cases row : seen[block]? with
          | none => simp [row] at marked
          | some value => cases value <;> simp_all
        · exact queued target old
      | false =>
        simp only [marked, Bool.false_eq_true, ite_false] at run
        cases row : func.blocks[block]? with
        | none => simp only [row] at run; contradiction
        | some body =>
          simp only [row] at run
          cases flow : blockReturnFlow mayReturn body.insts with
          | returns => simp only [flow] at run; contradiction
          | stops =>
            simp only [flow] at run
            obtain ⟨closed, queued, contains, boundary⟩ :=
              return_walk_closed mayReturn func fuel rest (seen.set! block true) (by simpa using sized) run
            have oldMarked : ∀ target, seen[target]? = some true → closed target := by
              intro target found
              apply contains
              by_cases same : block = target
              · subst target
                have bound := (Array.getElem?_eq_some_iff.mp found).1
                simp [Array.set!_eq_setIfInBounds, bound]
              · simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne same] using found
            have self : closed block := by
              apply contains
              have bound : block < seen.size := by
                rw [sized]
                exact (Array.getElem?_eq_some_iff.mp row).1
              simp [Array.set!_eq_setIfInBounds, bound]
            exact ⟨closed, fun target member => by
              rcases List.mem_cons.mp member with same | old
              · simpa [same] using self
              · exact queued target old,
              oldMarked, return_boundary_unmark row (Or.inl flow) boundary⟩
          | branches targets =>
            simp only [flow] at run
            obtain ⟨closed, queued, contains, boundary⟩ :=
              return_walk_closed mayReturn func fuel (targets ++ rest) (seen.set! block true) (by simpa using sized) run
            let enlarged : BlockId → Prop := fun target => target = block ∨ closed target
            refine ⟨enlarged, ?_, ?_, ?_⟩
            · intro target member
              rcases List.mem_cons.mp member with same | old
              · exact Or.inl same
              · exact Or.inr (queued target (List.mem_append_right _ old))
            · intro target found
              by_cases same : target = block
              · exact Or.inl same
              · apply Or.inr
                apply contains
                simpa [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm same)] using found
            · intro target present
              rcases present with same | old
              · subst target
                exact Or.inr ⟨body, row, Or.inr ⟨targets, flow,
                  fun target member => Or.inr (queued target (List.mem_append_left _ member))⟩⟩
              · have unmarked := return_boundary_unmark row
                  (Or.inr ⟨targets, flow, fun target member => queued target (List.mem_append_left _ member)⟩) boundary
                rcases unmarked target old with oldMark | ⟨oldBody, oldRow, stopped | ⟨next, nextFlow, nextClosed⟩⟩
                · exact Or.inl oldMark
                · exact Or.inr ⟨oldBody, oldRow, Or.inl stopped⟩
                · exact Or.inr ⟨oldBody, oldRow, Or.inr ⟨next, nextFlow, fun target member => Or.inr (nextClosed target member)⟩⟩
termination_by (fuel, pending.length)
decreasing_by all_goals simp_wf; simp_all only [List.length_cons]; omega

theorem funcMayReturn_sound {mayReturn : Array Bool} {func : Func}
    (run : funcMayReturn mayReturn func = true) : ReturnPath mayReturn func 0 := by
  have checked := return_walk_sound mayReturn func (func.blocks.size + 1) [0]
    (Array.replicate func.blocks.size false) (by simp) (by
      have bound := Array.count_le_size (a := false) (xs := Array.replicate func.blocks.size false)
      simp only [Array.size_replicate] at bound
      omega) run
  obtain ⟨block, member, path⟩ := checked
  have same : block = 0 := by simpa using member
  simpa [same] using path

theorem funcMayReturn_closed {mayReturn : Array Bool} {func : Func}
    (run : funcMayReturn mayReturn func = false) :
    ∃ closed : BlockId → Prop, closed 0 ∧ ReturnClosed mayReturn func closed := by
  obtain ⟨closed, queued, _, boundary⟩ := return_walk_closed mayReturn func (func.blocks.size + 1) [0]
    (Array.replicate func.blocks.size false) (by simp) run
  refine ⟨closed, queued 0 (by simp), ?_⟩
  intro block present
  rcases boundary block present with marked | safe
  · simp only [Array.getElem?_replicate] at marked
    split at marked <;> simp_all
  · exact safe

theorem funcMayReturn_monotone {left right : Array Bool} (order : ReturnBitsLE left right)
    (func : Func) (returns : funcMayReturn left func = true) : funcMayReturn right func = true := by
  cases run : funcMayReturn right func with
  | true => rfl
  | false =>
    obtain ⟨closed, entry, safe⟩ := funcMayReturn_closed run
    exact False.elim ((safe.antitone order).excludes (funcMayReturn_sound returns) entry)

theorem funcMayReturn_of_closed {mayReturn : Array Bool} {func : Func} {closed : BlockId → Prop}
    (entry : closed 0) (safe : ReturnClosed mayReturn func closed) : funcMayReturn mayReturn func = false := by
  cases run : funcMayReturn mayReturn func with
  | false => rfl
  | true => exact False.elim (safe.excludes (funcMayReturn_sound run) entry)

theorem funcMayReturn_of_blocks (mayReturn : Array Bool) {left right : Func}
    (blocks : left.blocks = right.blocks) : funcMayReturn mayReturn left = funcMayReturn mayReturn right := by
  cases one : funcMayReturn mayReturn left <;> cases two : funcMayReturn mayReturn right
  · rfl
  · obtain ⟨closed, entry, safe⟩ := funcMayReturn_closed one
    exact False.elim ((safe.of_blocks blocks).excludes (funcMayReturn_sound two) entry)
  · obtain ⟨closed, entry, safe⟩ := funcMayReturn_closed two
    exact False.elim ((safe.of_blocks blocks.symm).excludes (funcMayReturn_sound one) entry)
  · rfl

end Goose.Lower.Validation
