import Goose.Lower.ECall
import Goose.Lower.CallChecks

namespace Goose.Lower.ECallChecks

open Goose.Core Goose.GIR Goose.Lower.CallChecks

def referenceEntry : Impl :=
  { name := "main", params := #[], results := #[], vars := variables,
    body := .mk 0 [.letS 0 (.lit .i64 42) 0,
      .expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0] none, summary := .unknown }

private theorem reference_stmt (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    StatementESimulation n ⟨profile, referenceSource⟩ lc
      (.expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0) := by
  cases n with
  | zero => exact statementESimulation_zero _ _ _
  | succ n => exact stmt_exprE_sim n _ lc _ 0 (concrete_reference_call_expression profile n)

private theorem nil_stmts (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    StatementsESimulation n ⟨profile, referenceSource⟩ lc [] := by
  cases n with
  | zero => exact statementsESimulation_zero _ _ _
  | succ n => exact statementsE_nil n _ lc

private theorem reference_tail (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    StatementsESimulation n ⟨profile, referenceSource⟩ lc
      [.expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0] := by
  cases n with
  | zero => exact statementsESimulation_zero _ _ _
  | succ n =>
    exact statementsE_cons n _ lc _ [] (reference_stmt profile n lc) (nil_stmts profile n lc)

theorem reference_stmts (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    StatementsESimulation n ⟨profile, referenceSource⟩ lc referenceEntry.body.stmts := by
  cases n with
  | zero => exact statementsESimulation_zero _ _ _
  | succ n =>
    exact statementsE_cons n _ lc (.letS 0 (.lit .i64 42) 0) _
      (statementESimulation_fragment n _ lc _ rfl) (reference_tail profile n lc)

theorem reference_block (profile : NumProfile) (n : Nat) (pre : List (VarId × Val)) :
    BlockESimulation n ⟨profile, referenceSource⟩ none (callPre referenceEntry) pre
      false referenceEntry.body := by
  cases n with
  | zero => exact blockESimulation_zero _ _ _ _ _ _
  | succ n =>
    exact blockESimulation_succ n _ none _ pre false 0 _ none
      (reference_stmts profile n none) trivial

theorem actual_calling_callee_block (profile : NumProfile) (n : Nat) :
    CalleeBlockClaim n ⟨profile, referenceSource⟩ 1 referenceEntry :=
  calleeBlockClaim_of_simulation rfl profile n (reference_block profile n)

theorem actual_calling_entry (profile : NumProfile) (n : Nat) :
    CalleeCallClaim n ⟨profile, referenceSource⟩ referenceSource.entry := by
  cases n with
  | zero => exact calleeCallClaim_zero _ _
  | succ n =>
    exact calleeCallClaim_noResults_of_body (ctx := ⟨1, "main", [], [], []⟩)
      (impl := referenceEntry) rfl rfl rfl profile n (actual_calling_callee_block profile n)

theorem actual_calling_module_agree (profile : NumProfile) (n : Nat) (state : St) :
    EventualM (Core.runModule n ⟨profile, referenceSource⟩)
      (fun fuel => GIR.runModule fuel ⟨profile, lower referenceSource⟩) state := by
  have hglobals : referenceSource.globals.size = 0 := rfl
  have hgirGlobals : (lower referenceSource).globals.size = 0 := by simp [lower, referenceSource]
  have hentry : (lower referenceSource).entry = 1 := rfl
  simp only [Core.runModule, GIR.runModule, hglobals, hgirGlobals, hentry,
    List.range_zero, Core.initGlobals, GIR.initGlobals, pure_bind]
  exact EventualM.bind (actual_calling_entry profile n 0 [] state)
    (fun _ after _ => EventualM.refl (pure ()) after)

theorem actual_calling_module_correct (n : Nat) (p : NumProfile)
    (o : Outcome) (t : String) (h : eval n p referenceSource = .done o t) :
    ∃ k, GIR.run k p (lower referenceSource) = .done o t := by
  have hA := actual_calling_module_agree p n St.initial
  unfold eval at h
  unfold GIR.run
  cases hr : Goose.Core.runModule n ⟨p, referenceSource⟩ St.initial with
  | ok a s =>
    rw [hr] at h
    simp only [Result.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨K, hK⟩ := hA.1 a s hr
    have hK' : GIR.runModule K ⟨p, lower referenceSource⟩ St.initial = Res.ok a s := hK K (Nat.le_refl _)
    exact ⟨K, by rw [hK']⟩
  | stop e s =>
    rw [hr] at h
    cases e with
    | abort k org =>
      simp only [Result.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨K, hK⟩ := hA.2 _ s hr trivial
      have hK' : GIR.runModule K ⟨p, lower referenceSource⟩ St.initial = Res.stop (Stop.abort k org) s :=
        hK K (Nat.le_refl _)
      exact ⟨K, by rw [hK']⟩
    | exit code =>
      simp only [Result.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨K, hK⟩ := hA.2 _ s hr trivial
      have hK' : GIR.runModule K ⟨p, lower referenceSource⟩ St.initial = Res.stop (Stop.exit code) s :=
        hK K (Nat.le_refl _)
      exact ⟨K, by rw [hK']⟩
    | fault k => simp at h
    | timeout => simp at h

end Goose.Lower.ECallChecks
