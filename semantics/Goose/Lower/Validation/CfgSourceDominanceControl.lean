import Goose.Lower.Validation.CfgSourceDominanceJoin

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_ifS_none_core (loop : Option LoopCtx) (condition : ValueId) {body : B ValueId}
    (source : SSARun loop [] (fun _ => []) body) :
    SSARun loop [condition] (fun _ => []) (whenLive () fun _ => do
      let (thenBlock, joinBlock) ← fork condition
      setCur (some thenBlock)
      let _ ← body
      emitTerm (.br joinBlock [])
      setCur (some joinBlock)) := by
  intro env before result after run imports checked ready arguments
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨imports, SSAResult.of_current checked (.refl before) (Or.inr rfl)
      (by simp [AvailableValues])⟩
  | some start =>
    rw [whenLive_some _ _ env current] at run
    obtain ⟨⟨thenBlock, joinBlock⟩, forked, forkRun, _, started, startRun,
      value, child, childRun, _, closed, closeRun, joinRun⟩ := (by simpa only [bind_eq] using run)
    obtain ⟨ids, _⟩ := fork_ids forkRun
    obtain ⟨thenId, joinId⟩ := Prod.mk.inj ids
    subst thenId joinId
    obtain ⟨forkImports, forkState⟩ := ssa_fork condition env before imports checked current arguments
    rw [forkRun] at forkState
    have selected := forkState.select forkState.firstBound forkState.firstFresh
      forkState.firstOpen forkState.firstImports env
    rw [startRun] at selected
    obtain ⟨childImports, childState⟩ := source env started value child childRun forkImports
      selected.checked (selected.loop ready) (by simp [AvailableValues])
    have joinBoundStarted : before.blocks.size + 1 < started.blocks.size := by
      simpa only [← setCur_blocks startRun] using forkState.secondBound
    have joinBoundChild := Nat.lt_of_lt_of_le joinBoundStarted childState.advance.ext.1
    have joinImports : childImports (before.blocks.size + 1) = currentValues before imports :=
      (childState.imports _ joinBoundStarted).trans forkState.secondImports
    have notCurrent : started.cur ≠ some (before.blocks.size + 1) := by
      have selectedCurrent : started.cur = some before.blocks.size := by
        rw [setCur_run] at startRun
        exact congrArg LS.cur (Prod.mk.inj startRun).2.symm
      rw [selectedCurrent]
      exact fun equal => Nat.ne_of_lt (Nat.lt_succ_self _) (Option.some.inj equal)
    obtain ⟨joinBody, forkRow, joinOpen⟩ := forkState.secondOpen
    have startRow : started.blocks[before.blocks.size + 1]? = some joinBody := by
      simpa only [← setCur_blocks startRun] using forkRow
    have childRow := childState.advance.keep _ _ notCurrent startRow
    have completed := (selected.trans childState).close_join checked.opened.bound (by simp [current])
      joinBoundChild (Nat.le_succ _) childRow joinOpen
      (advance_current_ne_old childState.advance joinBoundStarted notCurrent) joinImports []
      (by simp [AvailableValues]) env
    exact ⟨childImports, by simpa only [bind_run, closeRun, joinRun] using completed⟩

theorem ssa_assert_core (loop : Option LoopCtx) (condition : ValueId) (origin : OriginId) :
    SSARun loop [condition] (fun _ => []) (whenLive () fun _ => do
      let (passBlock, failBlock) ← fork condition
      setCur (some failBlock)
      emitTerm (.abort .assert (some origin))
      setCur (some passBlock)) := by
  intro env before result after run imports checked ready arguments
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨imports, SSAResult.of_current checked (.refl before) (Or.inr rfl)
      (by simp [AvailableValues])⟩
  | some start =>
    rw [whenLive_some _ _ env current] at run
    obtain ⟨⟨passBlock, failBlock⟩, forked, forkRun, _, started, startRun,
      _, child, childRun, joinRun⟩ := (by simpa only [bind_eq] using run)
    obtain ⟨ids, _⟩ := fork_ids forkRun
    obtain ⟨passId, failId⟩ := Prod.mk.inj ids
    subst passId failId
    obtain ⟨forkImports, forkState⟩ := ssa_fork condition env before imports checked current arguments
    rw [forkRun] at forkState
    have selected := forkState.select forkState.secondBound forkState.secondFresh
      forkState.secondOpen forkState.secondImports env
    rw [startRun] at selected
    obtain ⟨childImports, childState⟩ := ssa_emitTerm loop (.abort .assert (some origin)) (by simp [Term.successors])
      env started _ child childRun forkImports selected.checked (selected.loop ready) (by simp [AvailableValues, Term.uses])
    have passBoundStarted : before.blocks.size < started.blocks.size := by
      simpa only [← setCur_blocks startRun] using forkState.firstBound
    have passBoundChild := Nat.lt_of_lt_of_le passBoundStarted childState.advance.ext.1
    have passImports : childImports before.blocks.size = currentValues before imports :=
      (childState.imports _ passBoundStarted).trans forkState.firstImports
    have notCurrent : started.cur ≠ some before.blocks.size := by
      have selectedCurrent : started.cur = some (before.blocks.size + 1) := by
        rw [setCur_run] at startRun
        exact congrArg LS.cur (Prod.mk.inj startRun).2.symm
      rw [selectedCurrent]
      exact fun equal => Nat.ne_of_lt (Nat.lt_succ_self _) (Option.some.inj equal).symm
    obtain ⟨passBody, forkRow, passOpen⟩ := forkState.firstOpen
    have startRow : started.blocks[before.blocks.size]? = some passBody := by
      simpa only [← setCur_blocks startRun] using forkRow
    have childRow := childState.advance.keep _ _ notCurrent startRow
    have combined := selected.trans childState
    have completed := SSAResult.select_imports childState.checked combined.advance combined.imports
      (by simp [current]) passBoundChild (Nat.le_refl _) ⟨_, childRow, passOpen⟩ passImports env
    rw [joinRun] at completed
    exact ⟨childImports, completed⟩

end Goose.Lower.Validation
