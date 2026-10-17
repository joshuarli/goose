import Goose.Lower.Validation.SourceReadyBlocks
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyControlSeeds

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem ready_fork {state : State} {env : LEnv} {before : LS} {condition : ValueId}
    (available : before.cur.isSome = true → flowAt state.values condition ≠ .pending) :
    EmitsOnly (ReadyOperands state) before (fork condition env before).2 := by
  let first := newBlock [] env before
  let second := newBlock [] env first.2
  have one := emitsOnly_newBlock (ReadyOperands state) [] env before first.1 first.2 rfl
  have two := emitsOnly_newBlock (ReadyOperands state) [] env first.2 second.1 second.2 rfl
  have closed : EmitsOnly (ReadyOperands state) second.2
      (emitTerm (.condbr condition first.1.1 [] second.1.1 []) env second.2).2 :=
    ready_emitTerm rfl (by
      intro live value member
      have same : value = condition := by simpa [Inst.uses, Term.uses] using member
      subst value
      exact available live)
  simpa only [fork, bind_run, pure_run, first, second] using one.trans (two.trans closed)

theorem ready_patchBrs {state : State} {env : LEnv} {before : LS} {target : BlockId}
    {incoming : List (BlockId × ValueId)}
    (available : ∀ pair ∈ incoming, flowAt state.values pair.2 ≠ .pending) :
    EmitsOnly (ReadyOperands state) before (patchBrs target incoming env before).2 := by
  induction incoming generalizing before with
  | nil => exact .refl _ _
  | cons pair rest ih =>
    have first := emitsOnly_pushInst pair.1 (.term (.br target [pair.2])) (show ReadyOperands state _ from by
      unfold ReadyOperands
      constructor
      · intro value member
        have same : value = pair.2 := by simpa [Inst.uses, Term.uses] using member
        subst value
        exact available pair (by simp)
      · simp [loadedResults]) env before _ _ rfl
    have tail := ih (before := (patchTerm pair.1 (.br target [pair.2]) env before).2)
      (by intro next member; exact available next (by simp [member]))
    exact first.trans tail

theorem patchTerm_member {env : LEnv} {before : LS} {source : BlockId} {term : Term}
    (bounded : source < before.blocks.size) :
    Inst.term term ∈ (patchTerm source term env before).2.insts := by
  rw [patchTerm_run]
  let body := before.blocks[source]
  have row : before.blocks[source]? = some body := by simp [body]
  have updated : (before.blocks.modify source (fun b => { b with insts := b.insts.push (.term term) }))[source]? =
      some { body with insts := body.insts.push (.term term) } := by
    simp [Array.getElem?_modify, row]
  exact List.mem_flatMap.mpr ⟨_, Array.mem_toList_iff.mpr (Array.mem_of_getElem? updated), by simp⟩

theorem patchBrs_member {env : LEnv} {before : LS} {target : BlockId}
    {incoming : List (BlockId × ValueId)} {selected : BlockId × ValueId}
    (member : selected ∈ incoming) (bounded : selected.1 < before.blocks.size) :
    Inst.term (.br target [selected.2]) ∈ (patchBrs target incoming env before).2.insts := by
  induction incoming generalizing before with
  | nil => cases member
  | cons pair rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst pair
      exact extension_inst_member (adv_patchBrs_ext rest rfl) (patchTerm_member (env := env) bounded)
    · apply ih later
      simpa only [patchTerm_run, Array.size_modify] using bounded

theorem SourceReadyFrame.joinLive {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {incoming : List (BlockId × ValueId)}
    (frame : SourceReadyFrame module callees func types state completed)
    (nonempty : incoming ≠ [])
    (bounded : ∀ pair ∈ incoming, pair.1 < before.blocks.size)
    (available : ∀ pair ∈ incoming, flowAt state.values pair.2 ≠ .pending)
    (extension : ((do
      let type ← valTy (incoming.headD (0, 0)).2
      let (target, parameters) ← newBlock [type]
      patchBrs target incoming
      setCur (some target)
      pure (parameters.headD 0) : B ValueId) env before).2.Ext completed)
    (allocated : before.vals.size < completed.vals.size) :
    ValueReadyAt state (do
      let type ← valTy (incoming.headD (0, 0)).2
      let (target, parameters) ← newBlock [type]
      patchBrs target incoming
      setCur (some target)
      pure (parameters.headD 0)) env before := by
  let type := (valTy (incoming.headD (0, 0)).2 env before).1
  let created := (newBlock [type] env before).2
  let patched := (patchBrs before.blocks.size incoming env created).2
  have createdReady := emitsOnly_newBlock (ReadyOperands state) [type] env before _ created rfl
  have patchedReady := ready_patchBrs (env := env) (before := created) (target := before.blocks.size) available
  have createdExtension : created.Ext patched := adv_patchBrs_ext incoming rfl
  have patchedExtension : patched.Ext completed := by
    have same : patched.Ext ((do
      let t ← valTy (incoming.headD (0, 0)).2
      let (target, parameters) ← newBlock [t]
      patchBrs target incoming
      setCur (some target)
      pure (parameters.headD 0) : B ValueId) env before).2 := by
      apply (EmitsOnly.of_blocks (property := ReadyOperands state) ?_).extension
      simp only [bind_run, valTy_run, newBlock1_run, setCur_run, pure_run, type, created, patched]
    exact same.trans extension
  have targetRow : created.blocks[before.blocks.size]? = some ⟨[(before.vals.size, type)], #[]⟩ := by
    simp [created, newBlock1_run]
  have bound : before.vals.size < state.values.size := by rw [frame.shape.values, ← frame.values]; exact allocated
  obtain ⟨selected, selectedMember⟩ := List.exists_mem_of_ne_nil incoming nonempty
  have selectedBound : selected.1 < created.blocks.size := by
    have old := bounded selected selectedMember
    simpa only [created, newBlock1_run, Array.size_push] using Nat.lt.step old
  have branch := patchBrs_member (target := before.blocks.size) (env := env) selectedMember selectedBound
  obtain ⟨body, row, params, _⟩ := createdExtension.2 _ _ targetRow
  have ready := frame.branchParameter patchedExtension branch row
    (parameter := (before.vals.size, type)) (argument := selected.2)
    (by simp [params]) bound (available selected selectedMember)
  refine ⟨?_, ?_⟩
  · have finished := (createdReady.trans patchedReady).trans
      (show EmitsOnly (ReadyOperands state) patched { patched with cur := some before.blocks.size } from .of_blocks rfl)
    simpa only [bind_run, valTy_run, newBlock1_run, setCur_run, pure_run, List.headD_cons,
      type, created, patched] using finished
  · intro _
    simpa only [bind_run, valTy_run, newBlock1_run, setCur_run, pure_run, List.headD_cons] using ready

#print axioms ready_fork
#print axioms ready_patchBrs
#print axioms patchTerm_member
#print axioms patchBrs_member
#print axioms SourceReadyFrame.joinLive

end Goose.Lower.Validation.ReplacementContentFlowSource
