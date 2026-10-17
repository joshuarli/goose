import Goose.Lower.Validation.CfgBuilderPaths

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReachableBuilder.of_blocks {before after : LS} (paths : ReachableBuilder before)
    (blocks : after.blocks = before.blocks) : ReachableBuilder after := by
  have extension : before.Ext after := by
    refine ⟨by rw [blocks]; exact Nat.le_refl _, ?_⟩
    intro block body row
    exact ⟨body, by simpa [blocks] using row, rfl, [], by simp⟩
  exact paths.of_ext extension (by rw [blocks]; exact Nat.le_refl _)

theorem BuilderPath.patchTerm_target {state : LS} {source target : BlockId}
    (path : BuilderPath state source) (sourceBound : source < state.blocks.size)
    (targetBound : target < state.blocks.size) (term : Term) (successor : target ∈ term.successors)
    (env : LEnv) : BuilderPath (patchTerm source term env state).2 target := by
  have extension := (LS.Ext.refl state).modify (appends_push (.term term)) source
  obtain ⟨body, row⟩ : ∃ body, state.blocks[source]? = some body :=
    ⟨state.blocks[source], Array.getElem?_eq_getElem sourceBound⟩
  rw [patchTerm_run]
  apply BuilderPath.next (path.mono extension)
    (body := { body with insts := body.insts.push (.term term) })
  · simp [Array.getElem?_modify, row]
  · simp only [cfgBlock, GIR.Block.terms, Array.toList_push, List.filterMap_append,
      List.filterMap_cons, Inst.term?, List.filterMap_nil, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.mem_append_right _ successor
  · simpa using targetBound

theorem ReachableBuilder.newBlock1_patchBrs {state : LS} (paths : ReachableBuilder state)
    {source : BlockId} (sourceBound : source < state.blocks.size) (value : ValueId)
    (rest : List (BlockId × ValueId)) (ty : VTy) (env : LEnv) :
    let initial := (newBlock [ty] env state).2
    ReachableBuilder (patchBrs state.blocks.size ((source, value) :: rest) env initial).2 := by
  let initial := (newBlock [ty] env state).2
  have created : state.Ext initial := (advB_newBlock1 ty env state _ _ rfl).ext
  have sourceInitial : source < initial.blocks.size := Nat.lt_of_lt_of_le sourceBound created.1
  have targetInitial : state.blocks.size < initial.blocks.size := by simp [initial, newBlock1_run]
  have sourcePath := (paths source sourceBound).mono created
  have newPath := sourcePath.patchTerm_target sourceInitial targetInitial
    (.br state.blocks.size [value]) (by simp [Term.successors]) env
  let one := (Goose.Lower.patchTerm source (.br state.blocks.size [value]) env initial).2
  have patched : one.Ext (patchBrs state.blocks.size rest env one).2 := adv_patchBrs_ext rest rfl
  have allPatched := adv_patchBrs_ext (jb := state.blocks.size) ((source, value) :: rest)
    (le := env) (ls1 := initial) rfl
  have allSize := patchBrs_size (jb := state.blocks.size) ((source, value) :: rest) (le := env) (ls1 := initial) rfl
  apply paths.of_ext_one (created.trans allPatched)
    (by rw [← allSize]; simp [initial, newBlock1_run])
  exact newPath.mono patched

theorem joinLive_reachable {state : LS} (paths : ReachableBuilder state)
    {source : BlockId} (sourceBound : source < state.blocks.size) (value : ValueId)
    (rest : List (BlockId × ValueId)) (env : LEnv) :
    let incoming := (source, value) :: rest
    let action : B ValueId := do
      let valueTy ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [valueTy]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)
    ReachableBuilder (action env state).2 := by
  cases run : valTy value env state with
  | mk ty same =>
    have unchanged := valTy_run value env state
    rw [run] at unchanged
    dsimp only at unchanged
    subst same
    simp only [List.headD_cons, bind_run, run, setCur_run, pure_run]
    apply ReachableBuilder.of_blocks (paths.newBlock1_patchBrs sourceBound value rest ty env)
    rfl

theorem ReachableBuilder.joinValue {state : LS} (paths : ReachableBuilder state)
    (endT endF : Option BlockId) (valueT valueF : ValueId)
    (thenBound : ∀ block, endT = some block → block < state.blocks.size)
    (elseBound : ∀ block, endF = some block → block < state.blocks.size) (env : LEnv) :
    ReachableBuilder (joinValue endT valueT endF valueF env state).2 := by
  cases endT with
  | none =>
    cases endF with
    | none =>
      apply paths.of_blocks
      rfl
    | some block =>
      simpa only [Goose.Lower.joinValue, Option.map_none, Option.map_some, Option.toList_none,
        Option.toList_some, List.nil_append] using
        joinLive_reachable paths (elseBound block rfl) valueF [] env
  | some block =>
    cases endF with
    | none =>
      simpa only [Goose.Lower.joinValue, Option.map_none, Option.map_some, Option.toList_none,
        Option.toList_some, List.append_nil] using
        joinLive_reachable paths (thenBound block rfl) valueT [] env
    | some other =>
      simpa only [Goose.Lower.joinValue, Option.map_some, Option.toList_some, List.cons_append,
        List.nil_append] using
        joinLive_reachable paths (thenBound block rfl) valueT [(other, valueF)] env

theorem ReachableBuilder.newBlock0_patchBrs0 {state : LS} (paths : ReachableBuilder state)
    {source : BlockId} (sourceBound : source < state.blocks.size)
    (rest : List BlockId) (env : LEnv) :
    let initial := (newBlock [] env state).2
    ReachableBuilder (patchBrs0 state.blocks.size (source :: rest) env initial).2 := by
  let initial := (newBlock [] env state).2
  have created : state.Ext initial := (advB_newBlock0 env state _ _ rfl).ext
  have sourceInitial : source < initial.blocks.size := Nat.lt_of_lt_of_le sourceBound created.1
  have targetInitial : state.blocks.size < initial.blocks.size := by simp [initial, newBlock0_run]
  have sourcePath := (paths source sourceBound).mono created
  have newPath := sourcePath.patchTerm_target sourceInitial targetInitial
    (.br state.blocks.size []) (by simp [Term.successors]) env
  let one := (Goose.Lower.patchTerm source (.br state.blocks.size []) env initial).2
  have patched : one.Ext (patchBrs0 state.blocks.size rest env one).2 := adv_patchBrs0_ext rest rfl
  have allPatched := adv_patchBrs0_ext (jb := state.blocks.size) (source :: rest)
    (le := env) (ls1 := initial) rfl
  have allSize := patchBrs0_size (jb := state.blocks.size) (source :: rest) (le := env) (ls1 := initial) rfl
  apply paths.of_ext_one (created.trans allPatched)
    (by rw [← allSize]; simp [initial, newBlock0_run])
  exact newPath.mono patched

theorem ReachableBuilder.joinArms {state : LS} (paths : ReachableBuilder state)
    (endT endF : Option BlockId)
    (thenBound : ∀ block, endT = some block → block < state.blocks.size)
    (elseBound : ∀ block, endF = some block → block < state.blocks.size) (env : LEnv) :
    ReachableBuilder (joinArms endT endF env state).2 := by
  cases endT with
  | none =>
    cases endF with
    | none => exact paths.of_blocks rfl
    | some block =>
      simp only [Goose.Lower.joinArms, Option.toList_none, Option.toList_some,
        List.nil_append, bind_run, newBlock0_run, setCur_run]
      exact (paths.newBlock0_patchBrs0 (elseBound block rfl) [] env).of_blocks rfl
  | some block =>
    cases endF with
    | none =>
      simp only [Goose.Lower.joinArms, Option.toList_none, Option.toList_some,
        List.append_nil, bind_run, newBlock0_run, setCur_run]
      exact (paths.newBlock0_patchBrs0 (thenBound block rfl) [] env).of_blocks rfl
    | some other =>
      simp only [Goose.Lower.joinArms, Option.toList_some, List.cons_append,
        List.nil_append, bind_run, newBlock0_run, setCur_run]
      exact (paths.newBlock0_patchBrs0 (thenBound block rfl) [other] env).of_blocks rfl

end Goose.Lower.Validation
