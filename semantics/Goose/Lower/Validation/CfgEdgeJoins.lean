import Goose.Lower.Validation.CfgEdgeForks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem edge_newBlock1_parameter {env : LEnv} {before after : LS} {result : BlockId × List ValueId}
    {ty : VTy} (run : newBlock [ty] env before = (result, after)) :
    after.vals[result.2.headD 0]? = some (some ty) := by
  rw [newBlock1_run] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  simp

theorem edge_patchBrs_at (join : BlockId) (incoming : List (BlockId × ValueId))
    (env : LEnv) (before after : LS) (result : Unit)
    (run : patchBrs join incoming env before = (result, after)) (checked : BuilderEdgeArguments before)
    (arguments : ∀ pair ∈ incoming, EdgeArguments before join [pair.2]) :
    EdgeExtension before after ∧ BuilderEdgeArguments after := by
  induction incoming generalizing before with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact ⟨.refl before, checked⟩
  | cons pair rest ih =>
    obtain ⟨ignored, middle, patched, tail⟩ := bind_eq.mp run
    have headEdge := arguments pair (by simp)
    obtain ⟨firstExtension, firstChecked⟩ := edge_patchTerm_at pair.1 (.br join [pair.2]) env before middle ignored patched checked headEdge
    obtain ⟨lastExtension, lastChecked⟩ := ih middle tail firstChecked
      (fun next member => (arguments next (by simp [member])).extend firstExtension)
    exact ⟨firstExtension.trans lastExtension, lastChecked⟩

theorem edge_patchBrs0_at (join : BlockId) (incoming : List BlockId)
    (env : LEnv) (before after : LS) (result : Unit)
    (run : patchBrs0 join incoming env before = (result, after)) (checked : BuilderEdgeArguments before)
    (arguments : EdgeArguments before join []) : EdgeExtension before after ∧ BuilderEdgeArguments after := by
  induction incoming generalizing before with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact ⟨.refl before, checked⟩
  | cons block rest ih =>
    obtain ⟨ignored, middle, patched, tail⟩ := bind_eq.mp run
    obtain ⟨firstExtension, firstChecked⟩ := edge_patchTerm_at block (.br join []) env before middle ignored patched checked arguments
    obtain ⟨lastExtension, lastChecked⟩ := ih middle tail firstChecked (arguments.extend firstExtension)
    exact ⟨firstExtension.trans lastExtension, lastChecked⟩

theorem edge_joinLive_at (incoming : List (BlockId × ValueId)) (ty : VTy)
    (env : LEnv) (before after : LS) (result : ValueId)
    (run : (do
      let valueTy ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [valueTy]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)) env before = (result, after))
    (checked : BuilderEdgeArguments before)
    (headTyped : before.vals[(incoming.headD (0, 0)).2]? = some (some ty))
    (allTyped : ∀ pair ∈ incoming, before.vals[pair.2]? = some (some ty)) :
    EdgeExtension before after ∧ BuilderEdgeArguments after ∧ after.vals[result]? = some (some ty) := by
  have readTy : valTy (incoming.headD (0, 0)).2 env before = (ty, before) := by
    simp only [valTy, bind_run, get_apply]
    rw [headTyped]
    rfl
  simp only [bind_eq] at run
  obtain ⟨valueTy, first, readRun, ⟨join, params⟩, allocated, created,
    ignored, patched, patchRun, ignored', selected, selectRun, finished⟩ := run
  rw [readTy] at readRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj readRun
  rw [pure_run] at finished
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj finished
  obtain ⟨createdExtension, createdChecked⟩ := edge_newBlock1 ty env before _ allocated created checked
  have arguments : ∀ pair ∈ incoming, EdgeArguments allocated join [pair.2] := by
    intro pair member
    exact edge_newBlock1_target created (allTyped pair member)
  obtain ⟨patchedExtension, patchedChecked⟩ := edge_patchBrs_at join incoming env allocated patched _ patchRun createdChecked arguments
  obtain ⟨selectedExtension, selectedChecked⟩ := edge_setCur _ env patched _ selected selectRun patchedChecked
  have parameter := edge_newBlock1_parameter created
  have finalType := selectedExtension.types (params.headD 0) ty (patchedExtension.types _ _ parameter)
  exact ⟨createdExtension.trans (patchedExtension.trans selectedExtension), selectedChecked, finalType⟩

theorem edge_joinArms (yes no : Option BlockId) : EdgeRun (joinArms yes no) := by
  intro env before result after run checked
  unfold joinArms at run
  split at run
  · exact edge_setCur none env before result after run checked
  · obtain ⟨⟨join, params⟩, allocated, created, ignored, patched, patchRun, selectRun⟩ := (by simpa only [bind_eq] using run)
    obtain ⟨createdExtension, createdChecked⟩ := edge_newBlock0 env before _ allocated created checked
    obtain ⟨patchedExtension, patchedChecked⟩ := edge_patchBrs0_at join _ env allocated patched _ patchRun createdChecked (edge_newBlock0_target created)
    obtain ⟨selectedExtension, selectedChecked⟩ := edge_setCur _ env patched result after selectRun patchedChecked
    exact ⟨createdExtension.trans (patchedExtension.trans selectedExtension), selectedChecked⟩

theorem edge_joinValue_at (yes no : Option BlockId) (yesValue noValue : ValueId) (ty : VTy)
    (env : LEnv) (before after : LS) (result : ValueId)
    (run : joinValue yes yesValue no noValue env before = (result, after)) (checked : BuilderEdgeArguments before)
    (yesTyped : ∀ block, yes = some block → before.vals[yesValue]? = some (some ty))
    (noTyped : ∀ block, no = some block → before.vals[noValue]? = some (some ty)) :
    EdgeExtension before after ∧ BuilderEdgeArguments after ∧
      (after.cur.isSome = true → after.vals[result]? = some (some ty)) := by
  unfold joinValue at run
  split at run
  · obtain ⟨ignored, selected, selectedRun, finished⟩ := bind_eq.mp run
    have pair := pure_eq.mp finished
    obtain ⟨extension, selectedChecked⟩ := edge_setCur none env before ignored selected selectedRun checked
    have stopped : selected.cur = none := by
      rw [setCur_run] at selectedRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj selectedRun
      rfl
    rw [← pair.2]
    exact ⟨extension, selectedChecked, fun live => by simp [stopped] at live⟩
  · let incoming := (yes.map fun block => (block, yesValue)).toList ++
        (no.map fun block => (block, noValue)).toList
    have allTyped : ∀ pair ∈ incoming, before.vals[pair.2]? = some (some ty) := by
      intro pair member
      simp only [incoming, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at member
      rcases member with ⟨block, present, same⟩ | ⟨block, present, same⟩
      · cases same
        exact yesTyped block present
      · cases same
        exact noTyped block present
    have nonempty : incoming ≠ [] := by
      cases yes <;> cases no <;> simp_all [incoming]
    have headMember : incoming.headD (0, 0) ∈ incoming := by
      cases row : incoming with
      | nil => exact False.elim (nonempty row)
      | cons pair rest => simp
    obtain ⟨extension, afterChecked, resultTyped⟩ := edge_joinLive_at incoming ty env before after result
      run checked (allTyped _ headMember) allTyped
    exact ⟨extension, afterChecked, fun _ => resultTyped⟩

end Goose.Lower.Validation
