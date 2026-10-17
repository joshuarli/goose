import Goose.Lower.Validation.CfgSourceDominanceState

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure BranchSSA (before after : LS) (beforeImports afterImports : ImportedValues)
    (first second : BlockId) : Prop where
  checked : ImportedState after afterImports
  advance : before.Adv after
  imports : ∀ block, block < before.blocks.size → afterImports block = beforeImports block
  live : before.cur.isSome = true
  firstBound : first < after.blocks.size
  secondBound : second < after.blocks.size
  firstFresh : before.blocks.size ≤ first
  secondFresh : before.blocks.size ≤ second
  firstOpen : ∃ body, after.blocks[first]? = some body ∧ OpenBlock body
  secondOpen : ∃ body, after.blocks[second]? = some body ∧ OpenBlock body
  firstImports : afterImports first = currentValues before beforeImports
  secondImports : afterImports second = currentValues before beforeImports

theorem branch_ssa (types : List VTy) (makeTerm : BlockId → BlockId → Term)
    (targetShape : ∀ first second, (makeTerm first second).successors ⊆ [first, second])
    (env : LEnv) (state : LS) (imports : ImportedValues) (checked : ImportedState state imports)
    {source : BlockId} (current : state.cur = some source)
    (operands : AvailableValues state imports (makeTerm state.blocks.size (state.blocks.size + 1)).uses) :
    let action : B Unit := do
      let (first, _) ← newBlock []
      let (second, _) ← newBlock types
      emitTerm (makeTerm first second)
    ∃ nextImports, BranchSSA state (action env state).2 imports nextImports
      state.blocks.size (state.blocks.size + 1) := by
  dsimp only
  let values := currentValues state imports
  let first := (newBlock [] env state).2
  let firstImports := extendImports imports state.blocks.size values
  let second := (newBlock types env first).2
  let secondImports := extendImports firstImports first.blocks.size values
  let term := makeTerm state.blocks.size (state.blocks.size + 1)
  let closed := (emitTerm term env second).2
  have sourceBound := checked.opened.bound source current
  have firstSize : first.blocks.size = state.blocks.size + 1 := by simp [first, newBlock0_run]
  have secondSize : second.blocks.size = state.blocks.size + 2 := by
    change (first.blocks.push _).size = _
    simp [firstSize, Nat.add_assoc]
  have firstBound : state.blocks.size < first.blocks.size := by rw [firstSize]; exact Nat.lt_succ_self _
  have secondCurrent : second.cur = some source := current
  have one := checked.allocate_current [] env
  have two := one.checked.allocate types values (by intro empty; rw [firstSize] at empty; omega)
    (by simpa [first, newBlock0_run] using
      currentValues_bounded checked.definitions checked.opened.bound checked.importsBounded) env
  have oldValues : AvailableValues state imports values := by
    intro block live value member
    have equal : source = block := Option.some.inj (current.symm.trans live)
    subst block
    exact available_of_exitValues sourceBound (by simpa [values, currentValues, current] using member)
  have allValues : AvailableValues second secondImports values := two.frame values (one.frame values oldValues)
  have termOperands : AvailableValues second secondImports term.uses :=
    two.frame _ (one.frame _ operands)
  have targetBounds : ∀ target ∈ term.successors, target < second.blocks.size := by
    intro target member
    have member := targetShape state.blocks.size (state.blocks.size + 1) member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    have bound : target < state.blocks.size + 2 := by
      rcases member with rfl | rfl
      · exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
      · exact Nat.lt_succ_self _
    exact Nat.lt_of_lt_of_le bound (Nat.le_of_eq secondSize.symm)
  have leftImports : secondImports state.blocks.size = values := by
    simp [secondImports, firstImports, extendImports, firstSize]
  have rightImports : secondImports (state.blocks.size + 1) = values := by
    simp [secondImports, extendImports, firstSize]
  have edgeValues : ∀ target ∈ term.successors, AvailableValues second secondImports (secondImports target) := by
    intro target member
    have member := targetShape state.blocks.size (state.blocks.size + 1) member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simpa only [leftImports] using allValues
    · simpa only [rightImports] using allValues
  have closedChecked := two.checked.emitTerm term env termOperands targetBounds edgeValues
  have closing := advB_emitTerm term env second _ _ rfl
  have closedSize : closed.blocks.size = second.blocks.size := by
    dsimp only [closed]
    rw [emitTerm_run term env secondCurrent]
    simp
  have leftOpen : ∃ body, closed.blocks[state.blocks.size]? = some body ∧ OpenBlock body := by
    obtain ⟨body, row, opened⟩ := newBlock_open state env []
    have secondRow : second.blocks[state.blocks.size]? = some body :=
      (newBlock_other first env types state.blocks.size firstBound).trans row
    have different : second.cur ≠ some state.blocks.size := by
      rw [secondCurrent]
      exact fun same => Nat.ne_of_lt sourceBound (Option.some.inj same)
    exact ⟨body, closing.keep _ body different secondRow, opened⟩
  have rightOpen : ∃ body, closed.blocks[state.blocks.size + 1]? = some body ∧ OpenBlock body := by
    obtain ⟨body, row, opened⟩ := newBlock_open first env types
    rw [firstSize] at row
    have different : second.cur ≠ some (state.blocks.size + 1) := by
      rw [secondCurrent]
      exact fun same => Nat.ne_of_lt (Nat.lt_succ_of_lt sourceBound) (Option.some.inj same)
    exact ⟨body, closing.keep _ body different row, opened⟩
  have actionState :
      ((do
        let (first, _) ← newBlock []
        let (second, _) ← newBlock types
        emitTerm (makeTerm first second) : B Unit) env state).2 = closed := by
    simp only [bind_run, newBlock0_run]
    change (emitTerm (makeTerm state.blocks.size first.blocks.size) env second).2 = closed
    rw [firstSize]
  rw [actionState]
  refine ⟨secondImports, closedChecked, one.advance.trans (two.advance.trans closing), ?_,
    by simp [current], ?_, ?_, Nat.le_refl _, Nat.le_succ _, leftOpen, rightOpen, leftImports, rightImports⟩
  · intro block bound
    exact (two.imports block (Nat.lt_of_lt_of_le bound one.advance.ext.1)).trans (one.imports block bound)
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      (Nat.le_of_eq (secondSize.symm.trans closedSize.symm))
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_of_eq (secondSize.symm.trans closedSize.symm))

theorem SSAResult.select_imports {before after : LS} {beforeImports afterImports : ImportedValues}
    (checked : ImportedState after afterImports) (advance : before.Adv after)
    (imports : ∀ block, block < before.blocks.size → afterImports block = beforeImports block)
    (live : before.cur.isSome = true) {target : BlockId}
    (bound : target < after.blocks.size) (fresh : before.blocks.size ≤ target)
    (openTarget : ∃ body, after.blocks[target]? = some body ∧ OpenBlock body)
    (targetImports : afterImports target = currentValues before beforeImports) (env : LEnv) :
    SSAResult before (setCur (some target) env after).2 beforeImports afterImports [] := by
  obtain ⟨body, row, opened⟩ := openTarget
  refine ⟨checked.select row opened env,
    adv_setCur_step (le := env) advance (Or.inr fresh) bound rfl, imports, ?_, ?_⟩
  · intro values available block current value member
    have equal : target = block := by
      rw [setCur_run] at current
      exact Option.some.inj current
    subst block
    cases oldCurrent : before.cur with
    | none => simp [oldCurrent] at live
    | some oldBlock =>
      have imported : value ∈ currentValues before beforeImports := by
        simpa only [currentValues, oldCurrent] using
          (available oldBlock oldCurrent value member).exitValues
      refine ⟨body, ?_, Or.inl ?_⟩
      · simpa only [setCur_run] using row
      · exact targetImports.symm ▸ imported
  · simp [AvailableValues]

theorem BranchSSA.select {before after : LS} {beforeImports afterImports : ImportedValues}
    {first second target : BlockId} (branch : BranchSSA before after beforeImports afterImports first second)
    (bound : target < after.blocks.size) (fresh : before.blocks.size ≤ target)
    (openTarget : ∃ body, after.blocks[target]? = some body ∧ OpenBlock body)
    (targetImports : afterImports target = currentValues before beforeImports) (env : LEnv) :
    SSAResult before (setCur (some target) env after).2 beforeImports afterImports [] :=
  SSAResult.select_imports branch.checked branch.advance branch.imports branch.live
    bound fresh openTarget targetImports env

theorem ssa_fork (condition : ValueId) (env : LEnv) (state : LS) (imports : ImportedValues)
    (checked : ImportedState state imports) {source : BlockId} (current : state.cur = some source)
    (operands : AvailableValues state imports [condition]) :
    ∃ nextImports, BranchSSA state (fork condition env state).2 imports nextImports
      state.blocks.size (state.blocks.size + 1) := by
  have branch := branch_ssa [] (fun first second => .condbr condition first [] second [])
    (by intro first second; simp [Term.successors]) env state imports checked current operands
  simpa only [fork, bind_run, pure_run] using branch

theorem ssa_scFork (isAnd : Bool) (condition : ValueId) (env : LEnv) (state : LS)
    (imports : ImportedValues) (checked : ImportedState state imports)
    {source : BlockId} (current : state.cur = some source)
    (operands : AvailableValues state imports [condition]) :
    ∃ nextImports, BranchSSA state (scFork isAnd condition env state).2 imports nextImports
      state.blocks.size (state.blocks.size + 1) := by
  let action : B Unit := do
    let (first, _) ← newBlock []
    let (second, _) ← newBlock [.data .bool]
    emitTerm (scTerm isAnd condition first second)
  have branch := branch_ssa [.data .bool] (scTerm isAnd condition)
    (by intro first second; cases isAnd <;> simp [scTerm, Term.successors]) env state imports checked current
    (operands.subset (by cases isAnd <;> simp [scTerm, Term.uses]))
  have same : (scFork isAnd condition env state).2 = (action env state).2 := by
    cases isAnd <;> rfl
  rw [same]
  exact branch

theorem scFork_join_row (isAnd : Bool) (condition : ValueId) (env : LEnv) (state : LS)
    {source : BlockId} (current : state.cur = some source) (bound : source < state.blocks.size) :
    (scFork isAnd condition env state).2.blocks[state.blocks.size + 1]? =
      some ⟨[(state.vals.size, .data .bool)], #[]⟩ := by
  rw [scFork_run isAnd condition env current]
  have different : source ≠ state.blocks.size + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt bound)
  simp only [Array.getElem?_modify, different, ite_false, Array.getElem?_push,
    Array.size_push, ite_true]

theorem advance_current_ne_old {before after : LS} (advance : before.Adv after)
    {block : BlockId} (bound : block < before.blocks.size) (different : before.cur ≠ some block) :
    after.cur ≠ some block := by
  intro equal
  rcases advance.cur with stopped | same | ⟨fresh, current, freshBound, _⟩
  · rw [stopped] at equal
    cases equal
  · exact different (same.symm.trans equal)
  · have same : fresh = block := Option.some.inj (current.symm.trans equal)
    subst fresh
    exact Nat.not_le_of_gt bound freshBound

end Goose.Lower.Validation
