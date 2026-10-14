import Goose.Lower.Control
import Goose.Lower.ReturnChecks

namespace Goose.Lower.ControlChecks

open Goose.Core Goose.GIR Goose.Lower.UnwindChecks

def returnedSeven : Stmt := .ret (some (.lit .i64 7)) 0

def nestedBlock : Core.Block := .mk 2
  [.ifS (.bool true)
    (.mk 3 [.ifS (.bool false) (.mk 4 [Goose.Lower.ReturnChecks.returningStmt] none)
      (some (.mk 5 [returnedSeven] none)) 0] none)
    (some (.mk 6 [Goose.Lower.ReturnChecks.returningStmt] none)) 0] none

def nestedResult (m : Core.Module) : ValueId × LS :=
  lowerBlock none [] false nestedBlock (lowerEnv m variables) scopedBuilder

def nestedBuilder (m : Core.Module) : LS := (nestedResult m).2

def nestedFunction (m : Core.Module) : Func :=
  { scopeFunction with blocks := finishBlocks (nestedBuilder m).blocks }

theorem concrete_nested_returning_block (cfg : Cfg) (fuel : Nat) :
    SimG ⟨⟨cfg.profile, lower cfg.mod⟩, nestedFunction cfg.mod⟩ (0, 0) beforeFrame
      (execBlock fuel cfg beforeEnv [] nestedBlock >>= prepareReturn beforeEnv)
      (BlockFlowPost cfg beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, nestedFunction cfg.mod⟩
        scopedBuilder beforeFrame (nestedBuilder cfg.mod) nestedBlock false (nestedResult cfg.mod).1) := by
  apply (flowClaims fuel).block none [] [] false nestedBlock rfl cfg beforeEnv
    (by simp) (lowerEnv cfg.mod variables) scopedBuilder (nestedBuilder cfg.mod) (nestedResult cfg.mod).1
    (0, 0) ⟨⟨cfg.profile, lower cfg.mod⟩, nestedFunction cfg.mod⟩ beforeFrame
  · exact (Prod.eta (nestedResult cfg.mod)).symm
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (nestedBuilder cfg.mod)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · trivial

#guard match (execBlock 30 ⟨.release, Goose.Lower.ReturnChecks.sourceModule⟩ beforeEnv []
    nestedBlock >>= prepareReturn beforeEnv) localState with
  | .ok (.ret (Val.int IntTy.i64 7)) state =>
    (state.store.roots[RootInst.local 0 11 0]?).isNone
  | _ => false

#guard match runAt ⟨⟨.release, lower Goose.Lower.ReturnChecks.sourceModule⟩,
    nestedFunction Goose.Lower.ReturnChecks.sourceModule⟩ (0, 0) beforeFrame 100 localState with
  | .ok (Val.int IntTy.i64 7) state =>
    (state.store.roots[RootInst.local 0 11 0]?).isNone
  | _ => false

def nestedEntryBody : Core.Block :=
  .mk 0 [.ifS (.bool true)
    (.mk 1 [.ifS (.bool false) (.mk 2 [.ret none 0] none)
      (some (.mk 3 [.print [.text "nested"] 0, .ret none 0] none)) 0] none)
    (some (.mk 4 [.ret none 0] none)) 0] none

def nestedModule : Core.Module :=
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := nestedEntryBody, summary := .unknown }
  { files := #["control.goose"], types := #[], globals := #[], impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0, origins := #[⟨0, 1, "control"⟩] }

#guard match Core.validate nestedModule, GIR.validate (lower nestedModule) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard Goose.Proofs.Lower.moduleOk nestedModule
#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 30 profile nestedModule, GIR.run 100 profile (lower nestedModule) with
  | .done .returned "nested\n", .done .returned "nested\n" => true
  | _, _ => false

theorem nested_module_correct (fuel : Nat) (profile : NumProfile) (outcome : Outcome)
    (trace : String) (h : Core.eval fuel profile nestedModule = .done outcome trace) :
    ∃ loweredFuel, GIR.run loweredFuel profile (lower nestedModule) = .done outcome trace :=
  Goose.Proofs.Lower.lower_correct_ctl nestedModule (by
    have hglobals : (#[].all fun (g : Core.Global) => exprOk g.init) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro global hglobal
      simp at hglobal
    simp only [Goose.Proofs.Lower.moduleOk, nestedModule, hglobals, Array.getElem?_singleton,
      ite_true, eq_self, Bool.true_and, Array.isEmpty_empty]
    change flowBlockOk nestedEntryBody = true
    simp only [nestedEntryBody, flowBlockOk.eq_def, flowStmtsOk.eq_def, flowStmtOk.eq_def,
      stmtReturnOk, stmtOk.eq_def, printOk.eq_def, exprOk.eq_def, Bool.true_and, Bool.and_true])
    fuel profile outcome trace h

end Goose.Lower.ControlChecks
