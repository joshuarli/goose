import Goose.Lower.Validation.CfgSourceDominanceFork

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_shortCircuit (loop : Option LoopCtx) (isAnd : Bool) (value : ValueId)
    {rhs : B ValueId} (source : SSARun loop [] (fun value => [value]) rhs) :
    SSARun loop [value] (fun result => [result]) (shortCircuit isAnd value rhs) := by
  intro env before result after run imports checked ready arguments
  cases current : before.cur with
  | none =>
    rw [shortCircuit, whenLive_none _ _ env current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨imports, SSAResult.of_current checked (.refl before) (Or.inr rfl)
      (by simp [AvailableValues, current])⟩
  | some start =>
    rw [shortCircuit, whenLive_some _ _ env current] at run
    obtain ⟨⟨right, join, parameter⟩, forked, forkRun, _, started, startRun,
      rhsValue, child, childRun, _, closed, closeRun, _, joined, joinRun, finalRun⟩ :=
      (by simpa only [bind_eq] using run)
    obtain ⟨ids, _⟩ := scFork_ids forkRun
    obtain ⟨rightId, rest⟩ := Prod.mk.inj ids
    obtain ⟨joinId, parameterId⟩ := Prod.mk.inj rest
    subst rightId joinId parameterId
    obtain ⟨resultEqual, stateEqual⟩ := pure_eq.mp finalRun
    subst resultEqual stateEqual
    obtain ⟨forkImports, forkState⟩ := ssa_scFork isAnd value env before imports checked current arguments
    rw [forkRun] at forkState
    have selected := forkState.select forkState.firstBound forkState.firstFresh
      forkState.firstOpen forkState.firstImports env
    rw [startRun] at selected
    obtain ⟨childImports, childState⟩ := source env started rhsValue child childRun forkImports
      selected.checked (selected.loop ready) (by simp [AvailableValues])
    have joinBoundStarted : before.blocks.size + 1 < started.blocks.size := by
      simpa only [← setCur_blocks startRun] using forkState.secondBound
    have joinBoundChild : before.blocks.size + 1 < child.blocks.size :=
      Nat.lt_of_lt_of_le joinBoundStarted childState.advance.ext.1
    have joinImports : childImports (before.blocks.size + 1) = currentValues before imports :=
      (childState.imports _ joinBoundStarted).trans forkState.secondImports
    have beforeValues : AvailableValues before imports (currentValues before imports) := by
      intro block live used member
      have equal : start = block := Option.some.inj (current.symm.trans live)
      subst block
      exact available_of_exitValues (checked.opened.bound start current)
        (by simpa only [currentValues, current] using member)
    have childValues := childState.frame _ (selected.frame _ beforeValues)
    have closedChecked := childState.checked.emitTerm (.br (before.blocks.size + 1) [rhsValue]) env
      childState.available (by
        intro target member
        have same : target = before.blocks.size + 1 := by simpa [Term.successors] using member
        exact same.symm ▸ joinBoundChild)
      (by
        intro target member
        have same : target = before.blocks.size + 1 := by simpa [Term.successors] using member
        subst target
        simpa only [joinImports] using childValues)
    rw [closeRun] at closedChecked
    have closing := advB_emitTerm (.br (before.blocks.size + 1) [rhsValue]) env child _ closed closeRun
    have joinBoundClosed := Nat.lt_of_lt_of_le joinBoundChild closing.ext.1
    have forkRow := scFork_join_row isAnd value env before current (checked.opened.bound start current)
    rw [forkRun] at forkRow
    have startRow : started.blocks[before.blocks.size + 1]? =
        some ⟨[(before.vals.size, .data .bool)], #[]⟩ := by
      simpa only [← setCur_blocks startRun] using forkRow
    have notCurrent : started.cur ≠ some (before.blocks.size + 1) := by
      have selectedCurrent : started.cur = some before.blocks.size := by
        rw [setCur_run] at startRun
        exact congrArg LS.cur (Prod.mk.inj startRun).2.symm
      rw [selectedCurrent]
      exact fun equal => Nat.ne_of_lt (Nat.lt_succ_self _) (Option.some.inj equal)
    have childRow := childState.advance.keep _ _ notCurrent startRow
    have closedRow := closing.keep _ _ (advance_current_ne_old childState.advance joinBoundStarted notCurrent) childRow
    have importsPrefix : ∀ block, block < before.blocks.size → childImports block = imports block := by
      intro block bound
      exact (childState.imports block (Nat.lt_of_lt_of_le bound selected.advance.ext.1)).trans
        (selected.imports block bound)
    have resultState := SSAResult.select_imports closedChecked
      (selected.advance.trans (childState.advance.trans closing)) importsPrefix (by simp [current])
      joinBoundClosed (Nat.le_succ _) ⟨_, closedRow, open_empty _⟩ joinImports env
    rw [joinRun] at resultState
    refine ⟨childImports, { resultState with available := ?_ }⟩
    intro block live used member
    have sameValue : used = before.vals.size := by simpa using member
    subst used
    have joinedCurrent : joined.cur = some (before.blocks.size + 1) := by
      rw [setCur_run] at joinRun
      exact congrArg LS.cur (Prod.mk.inj joinRun).2.symm
    have sameBlock : block = before.blocks.size + 1 := Option.some.inj (live.symm.trans joinedCurrent)
    subst block
    refine ⟨⟨[(before.vals.size, .data .bool)], #[]⟩, ?_, Or.inr ?_⟩
    · simpa only [← setCur_blocks joinRun] using closedRow
    · simp [cfgBlock, GIR.Block.defs]

end Goose.Lower.Validation
