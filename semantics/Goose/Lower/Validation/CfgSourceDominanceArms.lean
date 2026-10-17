import Goose.Lower.Validation.CfgSourceDominanceJoinValue

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure ArmSSA (before state : LS) (beforeImports imports : ImportedValues)
    (want : Bool) (endBlock : Option BlockId) (value : ValueId) : Prop where
  bounds : ∀ block, endBlock = some block → block < state.blocks.size
  owned : ∀ block, endBlock = some block → Mine before block
  operand : want = true → ∀ block, endBlock = some block → BuilderAvailable state imports block value
  transport : ∀ block, endBlock = some block → ∀ used ∈ currentValues before beforeImports,
    BuilderAvailable state imports block used

theorem ArmSSA.of_result {before state : LS} {beforeImports imports : ImportedValues}
    {want : Bool} {value : ValueId}
    (result : SSAResult before state beforeImports imports (if want then [value] else []))
    (bounded : LiveBound before) : ArmSSA before state beforeImports imports want state.cur value := by
  refine ⟨fun block current => result.checked.opened.bound block current,
    fun _ current => result.advance.mine_cur current, ?_, ?_⟩
  · intro wanted block current
    exact result.available block current value (by simp [wanted])
  · intro block current used member
    exact result.frame _ (currentValues_available bounded) block current used member

theorem ArmSSA.of_ext {before state after : LS} {beforeImports imports nextImports : ImportedValues}
    {want : Bool} {endBlock : Option BlockId} {value : ValueId}
    (arm : ArmSSA before state beforeImports imports want endBlock value)
    (extension : state.Ext after)
    (preserved : ∀ block, block < state.blocks.size → nextImports block = imports block) :
    ArmSSA before after beforeImports nextImports want endBlock value := by
  refine ⟨fun block current => Nat.lt_of_lt_of_le (arm.bounds block current) extension.1,
    arm.owned, ?_, ?_⟩
  · intro wanted block current
    exact (arm.operand wanted block current).of_ext extension preserved
  · intro block current used member
    exact (arm.transport block current used member).of_ext extension preserved

structure ArmsSSA (before state : LS) (beforeImports imports : ImportedValues)
    (want : Bool) (endThen : Option BlockId) (thenValue : ValueId)
    (endElse : Option BlockId) (elseValue : ValueId) : Prop where
  history : SSAResult before state beforeImports imports []
  thenArm : ArmSSA before state beforeImports imports want endThen thenValue
  elseArm : ArmSSA before state beforeImports imports want endElse elseValue

theorem ssa_arms (loop : Option LoopCtx) (want : Bool) (condition : ValueId)
    {thenAction elseAction : B ValueId}
    (thenSource : SSARun loop [] (fun value => if want then [value] else []) thenAction)
    (elseSource : SSARun loop [] (fun value => if want then [value] else []) elseAction)
    {env : LEnv} {before forked thenStart thenEnd elseStart elseEnd : LS}
    {thenBlock elseBlock thenValue elseValue : Nat} {u₁ u₂ : Unit}
    (forkRun : fork condition env before = ((thenBlock, elseBlock), forked))
    (thenStartRun : setCur (some thenBlock) env forked = (u₁, thenStart))
    (thenRun : thenAction env thenStart = (thenValue, thenEnd))
    (elseStartRun : setCur (some elseBlock) env thenEnd = (u₂, elseStart))
    (elseRun : elseAction env elseStart = (elseValue, elseEnd))
    (imports : ImportedValues) (initial : ImportedState before imports)
    (ready : LoopImportsReady loop before imports) {source : BlockId} (current : before.cur = some source)
    (arguments : AvailableValues before imports [condition]) :
    ∃ nextImports, ArmsSSA before elseEnd imports nextImports want thenEnd.cur thenValue elseEnd.cur elseValue := by
  obtain ⟨ids, _⟩ := fork_ids forkRun
  obtain ⟨thenId, elseId⟩ := Prod.mk.inj ids
  subst thenId elseId
  obtain ⟨forkImports, forkState⟩ := ssa_fork condition env before imports initial current arguments
  rw [forkRun] at forkState
  have thenSelected := forkState.select forkState.firstBound forkState.firstFresh
    forkState.firstOpen forkState.firstImports env
  rw [thenStartRun] at thenSelected
  obtain ⟨thenImports, thenState⟩ := thenSource env thenStart thenValue thenEnd thenRun forkImports
    thenSelected.checked (thenSelected.loop ready) (by simp [AvailableValues])
  have thenHistory := thenSelected.trans thenState
  have elseBoundStart : before.blocks.size + 1 < thenStart.blocks.size := by
    simpa only [← setCur_blocks thenStartRun] using forkState.secondBound
  have elseBoundEnd := Nat.lt_of_lt_of_le elseBoundStart thenState.advance.ext.1
  have elseImports : thenImports (before.blocks.size + 1) = currentValues before imports :=
    (thenState.imports _ elseBoundStart).trans forkState.secondImports
  have notCurrent : thenStart.cur ≠ some (before.blocks.size + 1) := by
    have selected : thenStart.cur = some before.blocks.size := by
      rw [setCur_run] at thenStartRun
      exact congrArg LS.cur (Prod.mk.inj thenStartRun).2.symm
    rw [selected]
    exact fun equal => Nat.ne_of_lt (Nat.lt_succ_self _) (Option.some.inj equal)
  obtain ⟨elseBody, forkRow, elseOpen⟩ := forkState.secondOpen
  have startRow : thenStart.blocks[before.blocks.size + 1]? = some elseBody := by
    simpa only [← setCur_blocks thenStartRun] using forkRow
  have thenRow := thenState.advance.keep _ _ notCurrent startRow
  have elseSelected := SSAResult.select_imports thenState.checked thenHistory.advance thenHistory.imports
    (by simp [current]) elseBoundEnd (Nat.le_succ _) ⟨_, thenRow, elseOpen⟩ elseImports env
  rw [elseStartRun] at elseSelected
  obtain ⟨nextImports, elseState⟩ := elseSource env elseStart elseValue elseEnd elseRun thenImports
    elseSelected.checked (elseSelected.loop ready) (by simp [AvailableValues])
  have elseHistory := elseSelected.trans elseState
  have extension : thenEnd.Ext elseStart := by
    refine ⟨?_, ?_⟩
    · rw [setCur_blocks elseStartRun]
      exact Nat.le_refl _
    · intro block body row
      exact ⟨body, by simpa only [← setCur_blocks elseStartRun] using row, rfl, [], by simp⟩
  have thenArm := (ArmSSA.of_result thenHistory initial.opened.bound).of_ext
    (extension.trans elseState.advance.ext)
    (fun block bound => elseState.imports block (by simpa only [← setCur_blocks elseStartRun] using bound))
  have finalHistory : SSAResult before elseEnd imports nextImports [] :=
    { elseHistory with available := by simp [AvailableValues] }
  exact ⟨nextImports, finalHistory, thenArm, ArmSSA.of_result elseHistory initial.opened.bound⟩

end Goose.Lower.Validation
