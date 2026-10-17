import Goose.Lower.Validation.StorageWalkActions
import Goose.Lower.Validation.ScopeFlowControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkConfiguration.fork {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (condition : ValueId) (env : LEnv) :
    StorageWalkConfiguration slots (forkScopeMap before entry) (forkScopeMap before exit)
      (Goose.Lower.fork condition env before).2 := by
  let first : LS := { before with blocks := before.blocks.push ⟨[], #[]⟩ }
  let firstEntry := fun block => if block = before.blocks.size then before.stack else entry block
  let firstExit := fun block => if block = before.blocks.size then before.stack else exit block
  have one : StorageWalkConfiguration slots firstEntry firstExit first := config.newBlock [] env
  have two := one.newBlock [] env
  have secondSize : (Goose.Lower.newBlock [] env first).2.blocks.size =
      before.blocks.size + 2 := by
    rw [newBlock0_run]
    simp [first]
  have closed := two.emitTerm (.condbr condition before.blocks.size [] (before.blocks.size + 1) []) rfl env (by
    intro target member
    simp only [Term.successors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst target <;>
      simp [first, firstEntry, newBlock0_run]) (by
    intro target member
    simp only [Term.successors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · subst target
      rw [secondSize]
      exact Nat.lt_succ_of_lt (Nat.lt_succ_self before.blocks.size)
    · subst target
      rw [secondSize]
      simpa [Nat.add_assoc] using Nat.lt_succ_self (before.blocks.size + 1))
  have entryEq : (fun block => if block = first.blocks.size then first.stack else firstEntry block) =
      forkScopeMap before entry := by
    simpa [first, firstEntry] using forkScopeMap_nested before entry
  have exitEq : (fun block => if block = first.blocks.size then first.stack else firstExit block) =
      forkScopeMap before exit := by
    simpa [first, firstExit] using forkScopeMap_nested before exit
  rw [entryEq, exitEq] at closed
  simp only [Goose.Lower.fork, bind_run, newBlock0_run, pure_run]
  simpa only [newBlock0_run, first, Array.size_push] using closed

theorem StorageWalkAction.fork {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (condition : ValueId) :
    StorageWalkAction slots stack loop (Goose.Lower.fork condition) := by
  refine ⟨advB_fork condition, ?_⟩
  intro env before entry exit config context stackEq
  have advance := advB_fork condition env before _ _ rfl
  have maps := forkScopeMap_advance before entry exit
  have nextContext := ScopeLoopContext.advance context advance maps
  have nextConfig := config.fork condition env
  exact ⟨forkScopeMap before entry, forkScopeMap before exit, nextConfig, maps⟩

end Goose.Lower.Validation
