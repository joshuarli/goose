import Goose.Lower.TypedEntry
import Goose.Lower.ECall
import Goose.Lower.CallChecks

namespace Goose.Lower.ECallChecks

open Goose.Core Goose.GIR Goose.Lower.CallChecks

def referenceEntry : Impl :=
  { name := "main", params := #[], results := #[], vars := variables,
    body := .mk 0 [.letS 0 (.lit .i64 42) 0,
      .expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0] none, summary := .unknown }

private theorem reference_stmt (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    TypedStatementLoopSimulation n ⟨profile, referenceSource⟩ [] lc
      (.expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0) := by
  cases n with
  | zero => exact typedStatementLoopSimulation_zero _ _ _ _
  | succ n =>
    exact typedStatementLoopSimulation_expr (concrete_reference_call_expression profile n [])

private theorem reference_tail (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    TypedStatementsLoopSimulation n ⟨profile, referenceSource⟩ [] lc
      [.expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0] := by
  cases n with
  | zero => exact typedStatementsLoopSimulation_zero _ _ _ _
  | succ n =>
    exact typedStatementsLoopSimulation_cons n _ [] lc _ [] (reference_stmt profile n lc)
      (typedStatementsLoopSimulation_nil n _ [] lc)

theorem reference_stmts (profile : NumProfile) (n : Nat) (lc : Option LoopCtx) :
    TypedStatementsLoopSimulation n ⟨profile, referenceSource⟩ [] lc referenceEntry.body.stmts := by
  cases n with
  | zero => exact typedStatementsLoopSimulation_zero _ _ _ _
  | succ n =>
    apply typedStatementsLoopSimulation_cons
    · cases n with
      | zero => exact typedStatementLoopSimulation_zero _ _ _ _
      | succ n => exact typedStatementLoopSimulation_let (typedExprClaim_lit n _ [] .i64 42)
    · exact reference_tail profile n lc

theorem reference_block (profile : NumProfile) (n : Nat) (pre : List (VarId × Val)) :
    TypedBlockLoopSimulation n ⟨profile, referenceSource⟩ [] none (callPre referenceEntry) pre
      false referenceEntry.body := by
  cases n with
  | zero => exact typedBlockLoopSimulation_zero _ _ _ _ _ _ _
  | succ n =>
    apply typedBlockLoopSimulation_succ
    · exact reference_stmts profile n none
    · trivial

theorem actual_calling_entry (profile : NumProfile) (n : Nat) :
    EventualM (enterCall (n + 1) ⟨profile, referenceSource⟩ 0 referenceSource.entry [])
      (fun fuel => callFn fuel ⟨profile, lower referenceSource⟩ 0 (lower referenceSource).entry [])
      St.initial := by
  apply typedEntry_simulation n 1 (by cbv) (by rfl)
  intro context impl contextAt implAt
  have contextEq : context = ⟨1, "main", [], [], []⟩ := by
    simpa [referenceSource] using contextAt.symm
  subst context
  have implEq : impl = referenceEntry := by simpa [referenceSource, referenceEntry] using implAt.symm
  subst impl
  exact reference_block profile n []

theorem actual_calling_module_agree (profile : NumProfile) (n : Nat) :
    EventualM (Core.runModule n ⟨profile, referenceSource⟩)
      (fun fuel => GIR.runModule fuel ⟨profile, lower referenceSource⟩) St.initial := by
  cases n with
  | zero =>
    refine ⟨fun value after done => ?_, fun err after done final => ?_⟩
    · simp [Core.runModule, referenceSource, Core.initGlobals, enterCall, Core.timeout,
        bind_apply, pure_apply, M.stop, Functor.map, M.bind', M.pure'] at done
    · simp [Core.runModule, referenceSource, Core.initGlobals, enterCall, Core.timeout,
        bind_apply, pure_apply, M.stop, Functor.map, M.bind', M.pure'] at done
      obtain ⟨rfl, rfl⟩ := done
      cases final
  | succ n =>
    apply typedModule_simulation_succ n (by cbv)
    · intro id global globalAt
      simp [referenceSource] at globalAt
    · intro context impl contextAt implAt
      have contextEq : context = ⟨1, "main", [], [], []⟩ := by
        simpa [referenceSource] using contextAt.symm
      subst context
      have implEq : impl = referenceEntry := by simpa [referenceSource, referenceEntry] using implAt.symm
      subst impl
      exact reference_block profile n []

theorem actual_calling_module_correct (n : Nat) (p : NumProfile)
    (o : Outcome) (t : String) (h : eval n p referenceSource = .done o t) :
    ∃ k, GIR.run k p (lower referenceSource) = .done o t := by
  have hA := actual_calling_module_agree p n
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
