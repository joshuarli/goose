import Goose.Lower.Validation.CfgCurrentOpen

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem fork_open_targets {state : LS} {source : BlockId} (current : state.cur = some source)
    (bound : source < state.blocks.size) (condition : ValueId) (env : LEnv) :
    let (pair, after) := fork condition env state
    (∃ body, after.blocks[pair.1]? = some body ∧ OpenBlock body) ∧
      (∃ body, after.blocks[pair.2]? = some body ∧ OpenBlock body) := by
  rw [fork_run condition env current]
  refine ⟨⟨⟨[], #[]⟩, ?_, open_empty _⟩, ⟨⟨[], #[]⟩, ?_, open_empty _⟩⟩
  · simp [Array.getElem?_modify, Nat.ne_of_lt bound, Array.getElem?_push]
  · have distinct : source ≠ state.blocks.size + 1 := by nat_omega
    simp only [Array.getElem?_modify, distinct, ite_false, Array.getElem?_push, Array.size_push, ite_true]

theorem scFork_open_targets {state : LS} {source : BlockId} (current : state.cur = some source)
    (bound : source < state.blocks.size) (isAnd : Bool) (value : ValueId) (env : LEnv) :
    let (pair, after) := scFork isAnd value env state
    (∃ body, after.blocks[pair.1]? = some body ∧ OpenBlock body) ∧
      (∃ body, after.blocks[pair.2.1]? = some body ∧ OpenBlock body) := by
  rw [scFork_run isAnd value env current]
  refine ⟨⟨⟨[], #[]⟩, ?_, open_empty _⟩,
    ⟨⟨[(state.vals.size, .data .bool)], #[]⟩, ?_, open_empty _⟩⟩
  · simp [Array.getElem?_modify, Nat.ne_of_lt bound, Array.getElem?_push]
  · have distinct : source ≠ state.blocks.size + 1 := by nat_omega
    simp only [Array.getElem?_modify, distinct, ite_false, Array.getElem?_push, Array.size_push, ite_true]

theorem patchBrs_other (target : BlockId) (incoming : List (BlockId × ValueId)) (env : LEnv)
    (state : LS) (other : BlockId) (different : ∀ pair ∈ incoming, pair.1 ≠ other) :
    (patchBrs target incoming env state).2.blocks[other]? = state.blocks[other]? := by
  induction incoming generalizing state with
  | nil => rfl
  | cons pair rest ih =>
    simp only [patchBrs, bind_run]
    rw [ih _ (fun next member => different next (by simp [member]))]
    exact patchTerm_other state env pair.1 other (different pair (by simp)) _

theorem patchBrs0_other (target : BlockId) (incoming : List BlockId) (env : LEnv)
    (state : LS) (other : BlockId) (different : ∀ block ∈ incoming, block ≠ other) :
    (patchBrs0 target incoming env state).2.blocks[other]? = state.blocks[other]? := by
  induction incoming generalizing state with
  | nil => rfl
  | cons block rest ih =>
    simp only [patchBrs0, bind_run]
    rw [ih _ (fun next member => different next (by simp [member]))]
    exact patchTerm_other state env block other (different block (by simp)) _

theorem joinLive_currentOpen {state : LS} (incoming : List (BlockId × ValueId))
    (bounded : ∀ pair ∈ incoming, pair.1 < state.blocks.size) (env : LEnv) :
    let action : B ValueId := do
      let valueTy ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [valueTy]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)
    CurrentOpen (action env state).2 := by
  cases run : valTy (incoming.headD (0, 0)).2 env state with
  | mk ty same =>
    have unchanged := valTy_run (incoming.headD (0, 0)).2 env state
    rw [run] at unchanged
    dsimp only at unchanged
    subst same
    simp only [bind_run, run, newBlock1_run, pure_run]
    apply CurrentOpen.setCur (body := ⟨[(state.vals.size, ty)], #[]⟩)
    · rw [patchBrs_other _ _ _ _ _ (fun pair member => Nat.ne_of_lt (bounded pair member))]
      simp
    · exact open_empty _

theorem joinValue_currentOpen (state : LS) (endT endF : Option BlockId) (valueT valueF : ValueId)
    (thenBound : ∀ block, endT = some block → block < state.blocks.size)
    (elseBound : ∀ block, endF = some block → block < state.blocks.size) (env : LEnv) :
    CurrentOpen (joinValue endT valueT endF valueF env state).2 := by
  cases endT with
  | none =>
    cases endF with
    | none => exact currentOpen_none rfl
    | some block =>
      simpa only [joinValue, Option.map_none, Option.map_some, Option.toList_none,
        Option.toList_some, List.nil_append] using joinLive_currentOpen [(block, valueF)]
        (by intro pair member; simp only [List.mem_singleton] at member; subst pair; exact elseBound block rfl) env
  | some block =>
    cases endF with
    | none =>
      simpa only [joinValue, Option.map_none, Option.map_some, Option.toList_none,
        Option.toList_some, List.append_nil] using joinLive_currentOpen [(block, valueT)]
        (by intro pair member; simp only [List.mem_singleton] at member; subst pair; exact thenBound _ rfl) env
    | some other =>
      simpa only [joinValue, Option.map_some, Option.toList_some, List.cons_append, List.nil_append] using
        joinLive_currentOpen [(block, valueT), (other, valueF)]
          (by
            intro pair member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact thenBound _ rfl
            · exact elseBound _ rfl) env

theorem joinEmpty_currentOpen (state : LS) (incoming : List BlockId)
    (bounded : ∀ block ∈ incoming, block < state.blocks.size) (env : LEnv) :
    let action : B Unit := do
      let (join, _) ← newBlock []
      patchBrs0 join incoming
      setCur (some join)
    CurrentOpen (action env state).2 := by
  simp only [bind_run, newBlock0_run]
  apply CurrentOpen.setCur (body := ⟨[], #[]⟩)
  · rw [patchBrs0_other _ _ _ _ _ (fun block member => Nat.ne_of_lt (bounded block member))]
    simp
  · exact open_empty _

theorem joinArms_currentOpen (state : LS) (endT endF : Option BlockId)
    (thenBound : ∀ block, endT = some block → block < state.blocks.size)
    (elseBound : ∀ block, endF = some block → block < state.blocks.size) (env : LEnv) :
    CurrentOpen (joinArms endT endF env state).2 := by
  cases endT with
  | none =>
    cases endF with
    | none => exact currentOpen_none rfl
    | some block =>
      simpa only [joinArms, Option.toList_none, Option.toList_some, List.nil_append] using
        joinEmpty_currentOpen state [block]
          (by intro target member; simp only [List.mem_singleton] at member; subst target; exact elseBound block rfl) env
  | some block =>
    cases endF with
    | none =>
      simpa only [joinArms, Option.toList_none, Option.toList_some, List.append_nil] using
        joinEmpty_currentOpen state [block]
          (by intro target member; simp only [List.mem_singleton] at member; subst target; exact thenBound _ rfl) env
    | some other =>
      simpa only [joinArms, Option.toList_some, List.cons_append, List.nil_append] using
        joinEmpty_currentOpen state [block, other]
          (by
            intro target member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact thenBound _ rfl
            · exact elseBound _ rfl) env

end Goose.Lower.Validation
