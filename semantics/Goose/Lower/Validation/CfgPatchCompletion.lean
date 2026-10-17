import Goose.Lower.Validation.CfgCompletion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem patchTerm_complete {state : LS} (shaped : ShapedBlocks state)
    {block : BlockId} {body : BlockB} (row : state.blocks[block]? = some body)
    (openBody : OpenBlock body) (term : Term) (env : LEnv) :
    ShapedBlocks (patchTerm block term env state).2 ∧
      OpenCount (patchTerm block term env state).2 + 1 = OpenCount state := by
  refine ⟨shaped.patchTerm block ?_ term env, ?_⟩
  · intro other otherRow
    have same := Option.some.inj (row.symm.trans otherRow)
    simpa [← same] using openBody
  · rw [patchTerm_run]
    exact openCount_push_term row openBody term

theorem patchBrs_complete (target : BlockId) (env : LEnv) (incoming : List (BlockId × ValueId))
    (unique : (incoming.map Prod.fst).Nodup) (state : LS) (shaped : ShapedBlocks state)
    (openIncoming : ∀ pair ∈ incoming, ∃ body, state.blocks[pair.1]? = some body ∧ OpenBlock body) :
    ShapedBlocks (patchBrs target incoming env state).2 ∧
      OpenCount (patchBrs target incoming env state).2 + incoming.length = OpenCount state := by
  induction incoming generalizing state with
  | nil => exact ⟨shaped, by simp [patchBrs, pure_run]⟩
  | cons pair rest ih =>
    have noRepeat : pair.1 ∉ rest.map Prod.fst := (List.nodup_cons.mp unique).1
    have restUnique : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp unique).2
    obtain ⟨body, row, openBody⟩ := openIncoming pair (by simp)
    obtain ⟨shapePatched, countPatched⟩ := patchTerm_complete shaped row openBody (.br target [pair.2]) env
    let patched := (patchTerm pair.1 (.br target [pair.2]) env state).2
    have restOpen : ∀ next ∈ rest, ∃ body, patched.blocks[next.1]? = some body ∧ OpenBlock body := by
      intro next member
      obtain ⟨body, oldRow, openBody⟩ := openIncoming next (by simp [member])
      have different : pair.1 ≠ next.1 := by
        intro equal
        exact noRepeat (List.mem_map.mpr ⟨next, member, equal.symm⟩)
      refine ⟨body, ?_, openBody⟩
      exact (patchTerm_other state env pair.1 next.1 different _).trans oldRow
    obtain ⟨shapeRest, countRest⟩ := ih restUnique patched shapePatched restOpen
    simp only [patchBrs, bind_run]
    refine ⟨shapeRest, ?_⟩
    simp only [List.length_cons]
    change OpenCount (patchBrs target rest env patched).2 + (rest.length + 1) = OpenCount state
    dsimp only [patched] at countRest ⊢
    omega

theorem patchBrs0_complete (target : BlockId) (env : LEnv) (incoming : List BlockId)
    (unique : incoming.Nodup) (state : LS) (shaped : ShapedBlocks state)
    (openIncoming : ∀ pair ∈ incoming, ∃ body, state.blocks[pair]? = some body ∧ OpenBlock body) :
    ShapedBlocks (patchBrs0 target incoming env state).2 ∧
      OpenCount (patchBrs0 target incoming env state).2 + incoming.length = OpenCount state := by
  induction incoming generalizing state with
  | nil => exact ⟨shaped, by simp [patchBrs0, pure_run]⟩
  | cons pair rest ih =>
    have noRepeat : pair ∉ rest := (List.nodup_cons.mp unique).1
    have restUnique : (rest).Nodup := (List.nodup_cons.mp unique).2
    obtain ⟨body, row, openBody⟩ := openIncoming pair (by simp)
    obtain ⟨shapePatched, countPatched⟩ := patchTerm_complete shaped row openBody (.br target []) env
    let patched := (patchTerm pair (.br target []) env state).2
    have restOpen : ∀ next ∈ rest, ∃ body, patched.blocks[next]? = some body ∧ OpenBlock body := by
      intro next member
      obtain ⟨body, oldRow, openBody⟩ := openIncoming next (by simp [member])
      have different : pair ≠ next := by
        intro equal
        exact noRepeat (equal ▸ member)
      refine ⟨body, ?_, openBody⟩
      exact (patchTerm_other state env pair next different _).trans oldRow
    obtain ⟨shapeRest, countRest⟩ := ih restUnique patched shapePatched restOpen
    simp only [patchBrs0, bind_run]
    refine ⟨shapeRest, ?_⟩
    simp only [List.length_cons]
    change OpenCount (patchBrs0 target rest env patched).2 + (rest.length + 1) = OpenCount state
    dsimp only [patched] at countRest ⊢
    omega

end Goose.Lower.Validation
