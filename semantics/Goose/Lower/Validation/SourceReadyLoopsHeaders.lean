import Goose.Lower.Validation.SourceReadyLoops

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFrame.headerParameter {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {type : VTy} {initial : ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (available : flowAt state.values initial ≠ .pending)
    (extension :
      let created := newBlock [type] env before
      (emitTerm (.br created.1.1 [initial]) env created.2).2.Ext completed)
    (allocated : before.vals.size < completed.vals.size) :
    let created := newBlock [type] env before
    let closed := (emitTerm (.br created.1.1 [initial]) env created.2).2
    EmitsOnly (ReadyOperands state) before closed ∧
      flowAt state.values (created.1.2.headD 0) ≠ .pending := by
  let created := newBlock [type] env before
  let closed := (emitTerm (.br created.1.1 [initial]) env created.2).2
  have newReady := emitsOnly_newBlock (ReadyOperands state) [type] env before created.1 created.2 rfl
  have closedReady : EmitsOnly (ReadyOperands state) created.2 closed := ready_emitTerm rfl (by
    intro _ value member
    have same : value = initial := by simpa [Inst.uses, Term.uses] using member
    subst value
    exact available)
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  have createdCurrent : created.2.cur = some block := current
  have createdBound : block < created.2.blocks.size := by
    have old := bounded block current
    simpa only [created, newBlock1_run, Array.size_push] using Nat.lt_succ_of_lt old
  have member := emitTerm_member (env := env) (term := .br created.1.1 [initial]) createdCurrent createdBound
  have initialRow : created.2.blocks[created.1.1]? = some ⟨[(before.vals.size, type)], #[]⟩ := by
    simp only [created, newBlock1_run, Array.getElem?_push_eq]
  obtain ⟨body, bodyRow, params, _⟩ := closedReady.extension.2 _ _ initialRow
  have valueBound : before.vals.size < state.values.size := by rw [frame.shape.values, ← frame.values]; exact allocated
  have ready := frame.branchParameter extension member bodyRow (parameter := (before.vals.size, type))
    (argument := initial) (by simp [params]) valueBound available
  exact ⟨newReady.trans closedReady, by simpa only [created, newBlock1_run, List.headD_cons] using ready⟩

#print axioms SourceReadyFrame.headerParameter

end Goose.Lower.Validation.ReplacementContentFlowSource
