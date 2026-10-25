import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem typedStatementLoopSimulation_zero (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (stmt : Stmt) :
    TypedStatementLoopSimulation 0 cfg results loop stmt := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  simp only [execStmt]
  exact SimEAt.of_simG SimG.of_timeout_bind state

theorem typedStatementLoopSimulation_abort {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} (message : String) (org : OriginId) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.abort message org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  simp only [lowerStmt] at hlow
  obtain ⟨_, _, _, instruction⟩ := emitTerm_facts hlow hpp hext
  simp only [execStmt, abortAt, M.stop, bind_apply]
  exact (SimE.abort_term instruction).at_state state

theorem typedStatementLoopSimulation_return_none (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (org : OriginId) :
    TypedStatementLoopSimulation n cfg results loop (.ret none org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  rw [prepareLoopFlow_execStmt_return_none]
  exact (SimEAt.of_simG (stmt_ret_none_prepared n loop org _ ls ls' result pt cfg env cx fr
    hlow hpp hext hrel) state).mono fun flow _ pt' fr' _ ⟨hflow, hsite⟩ =>
      Or.inr (Or.inl ⟨.unit, org, hflow, hsite⟩)

theorem typedStatementLoopSimulation_break (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (org : OriginId) :
    TypedStatementLoopSimulation n cfg results loop (.brk org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  cases loop with
  | none =>
    have hzero := hloops.mp rfl
    have typed := source.typed
    simp only [tyStmt, hzero, ite_true] at typed
    inv at typed
  | some context =>
    rw [prepareLoopFlow_execStmt_break]
    exact (SimEAt.of_simG (stmt_brk_prepared_sim n context org _ ls ls' result pt cfg env cx fr
      hlow hpp hext hrel htargets.breakBlock) state).mono
        fun flow _ pt' fr' _ ⟨hflow, hpost⟩ =>
          Or.inr (Or.inr ⟨context, rfl, Or.inl ⟨hflow, hpost.exitedAt _⟩⟩)

theorem typedStatementLoopSimulation_continue (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (org : OriginId) :
    TypedStatementLoopSimulation n cfg results loop (.cont org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  cases loop with
  | none =>
    have hzero := hloops.mp rfl
    have typed := source.typed
    simp only [tyStmt, hzero, ite_true] at typed
    inv at typed
  | some context =>
    rw [prepareLoopFlow_execStmt_continue]
    cases hkind : context.cont with
    | jump header =>
      have htarget := htargets.continueBlock
      rw [hkind] at htarget
      exact (SimEAt.of_simG (stmt_cont_jump_prepared_sim n context header org hkind
        _ ls ls' result pt cfg env cx fr hlow hpp hext hrel htarget) state).mono
          fun flow _ pt' fr' _ ⟨hflow, hpost⟩ =>
            Or.inr (Or.inr ⟨context, rfl, Or.inr ⟨hflow, hpost.continuedAt hkind _⟩⟩)
    | next header hint counter =>
      have htarget := htargets.continueBlock
      rw [hkind] at htarget
      simp only [LoopCounterAt, hkind] at hcounter
      obtain ⟨hbound, runtimeTy, current, hcell⟩ := hcounter
      exact (SimEAt.of_simG (stmt_cont_next_prepared_sim n context header hint runtimeTy counter
        current org hkind _ ls ls' result pt cfg env cx fr hcell hbound hlow hpp hext hrel htarget)
        state).mono fun flow _ pt' fr' _ ⟨hflow, hpost⟩ =>
          Or.inr (Or.inr ⟨context, rfl, Or.inr ⟨hflow, hpost.continuedAt hkind hcell⟩⟩)

end Goose.Lower
