import Goose.Lower.Control
import Goose.Lower.ReturnChecks
import Goose.Lower.TypedIf
import Goose.Lower.TypedStatements
import Goose.Lower.TypedTransfers
import Goose.Lower.TypedLists

namespace Goose.Lower.ControlChecks

open Goose.Core Goose.GIR Goose.Lower.UnwindChecks

def returnedSeven : Stmt := .ret (some (.lit .i64 7)) 0

def nestedChoice : Stmt :=
  .ifS (.bool false) (.mk 4 [Goose.Lower.ReturnChecks.returningStmt] none)
    (some (.mk 5 [returnedSeven] none)) 0

def nestedBlock : Core.Block := .mk 2
  [.ifS (.bool true)
    (.mk 3 [nestedChoice] none)
    (some (.mk 6 [Goose.Lower.ReturnChecks.returningStmt] none)) 0] none

def nestedResult (m : Core.Module) : ValueId × LS :=
  lowerBlock none [] false nestedBlock (lowerEnv m variables [.int .i64]) scopedBuilder

def nestedBuilder (m : Core.Module) : LS := (nestedResult m).2

def nestedFunction (m : Core.Module) : Func :=
  { scopeFunction with results := [.int .i64], blocks := finishBlocks (nestedBuilder m).blocks }

private theorem singleBlockClaim (cfg : Cfg) (results : List Ty) (scope : Nat) (stmt : Stmt)
    (statement : ∀ n, TypedStatementLoopSimulation n cfg results none stmt) (n : Nat) :
    TypedBlockLoopSimulation n cfg results none [] [] false (.mk scope [stmt] none) := by
  cases n with
  | zero => exact typedBlockLoopSimulation_zero _ _ _ _ _ _ _
  | succ n =>
    apply typedBlockLoopSimulation_succ
    · cases n with
      | zero => exact typedStatementsLoopSimulation_zero _ _ _ _
      | succ k =>
        exact typedStatementsLoopSimulation_cons k cfg results none stmt []
          (statement k) (typedStatementsLoopSimulation_nil k cfg results none)
    · trivial

private theorem returnedLocalClaim (cfg : Cfg) (n : Nat) :
    TypedStatementLoopSimulation n cfg [.int .i64] none ReturnChecks.returningStmt := by
  cases n with
  | zero => exact typedStatementLoopSimulation_zero _ _ _ _
  | succ n =>
    apply typedStatementLoopSimulation_return_some
    cases n with
    | zero => exact typedExprClaim_zero _ _ _
    | succ k =>
      exact typedExprClaim_read (typedPlaceClaim_var k cfg [.int .i64] 0)

private theorem returnedSevenClaim (cfg : Cfg) (n : Nat) :
    TypedStatementLoopSimulation n cfg [.int .i64] none returnedSeven := by
  cases n with
  | zero => exact typedStatementLoopSimulation_zero _ _ _ _
  | succ n =>
    exact typedStatementLoopSimulation_return_some
      (typedExprClaim_lit n cfg [.int .i64] .i64 7)

private theorem nestedChoiceClaim (cfg : Cfg) (n : Nat) :
    TypedStatementLoopSimulation n cfg [.int .i64] none nestedChoice := by
  cases n with
  | zero => exact typedStatementLoopSimulation_zero _ _ _ _
  | succ n =>
    exact typedStatementLoopSimulation_if_some
      (typedExprClaim_bool n cfg [.int .i64] false)
      (singleBlockClaim cfg [.int .i64] 4 _ (returnedLocalClaim cfg) n)
      (singleBlockClaim cfg [.int .i64] 5 _ (returnedSevenClaim cfg) n)

private theorem nestedBlockClaim (cfg : Cfg) (n : Nat) :
    TypedBlockLoopSimulation n cfg [.int .i64] none [] [] false nestedBlock := by
  apply singleBlockClaim
  intro fuel
  cases fuel with
  | zero => exact typedStatementLoopSimulation_zero _ _ _ _
  | succ k =>
    exact typedStatementLoopSimulation_if_some
      (typedExprClaim_bool k cfg [.int .i64] true)
      (singleBlockClaim cfg [.int .i64] 3 _ (nestedChoiceClaim cfg) k)
      (singleBlockClaim cfg [.int .i64] 6 _ (returnedLocalClaim cfg) k)

theorem concrete_nested_returning_block (cfg : Cfg) (fuel : Nat) (state : St)
    (source : BlockSource cfg beforeEnv [] nestedBlock state)
    (metadata : SourceResults source.typingEnv source.rootsEnv [.int .i64])
    (loops : source.typingEnv.loops = 0) :
    SimEAt ⟨⟨cfg.profile, lower cfg.mod⟩, nestedFunction cfg.mod⟩ (0, 0) beforeFrame
      (execBlock fuel cfg beforeEnv [] nestedBlock >>= prepareReturn beforeEnv)
      (BlockFlowPost cfg beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, nestedFunction cfg.mod⟩
        scopedBuilder beforeFrame (nestedBuilder cfg.mod) nestedBlock false (nestedResult cfg.mod).1) state := by
  apply (nestedBlockClaim cfg fuel).function beforeEnv state source metadata loops
    scopedBuilder (nestedBuilder cfg.mod) (nestedResult cfg.mod).1 (0, 0)
    ⟨⟨cfg.profile, lower cfg.mod⟩, nestedFunction cfg.mod⟩ beforeFrame
  · exact (Prod.eta (nestedResult cfg.mod)).symm
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (nestedBuilder cfg.mod)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · trivial
  · rfl
  · rfl

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
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0, origins := #[⟨0, 1, "if"⟩] }

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

def returningLoopBody : Core.Block :=
  .mk 0 [.while (.bool true)
    (.mk 1 [.ifS (.bool true)
      (.mk 2 [.print [.text "loop"] 0, .ret none 0] none) none 0] none) 0] none

def returningLoopModule : Core.Module :=
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := returningLoopBody, summary := .unknown }
  { files := #["loop-return.goose"], types := #[], globals := #[], impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0, origins := #[⟨0, 1, "while"⟩] }

#guard match Core.validate returningLoopModule, GIR.validate (lower returningLoopModule) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard Goose.Proofs.Lower.moduleOk returningLoopModule
#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 30 profile returningLoopModule, GIR.run 100 profile (lower returningLoopModule) with
  | .done .returned "loop\n", .done .returned "loop\n" => true
  | _, _ => false

theorem returning_loop_module_correct (fuel : Nat) (profile : NumProfile) (outcome : Outcome)
    (trace : String) (h : Core.eval fuel profile returningLoopModule = .done outcome trace) :
    ∃ loweredFuel, GIR.run loweredFuel profile (lower returningLoopModule) = .done outcome trace :=
  Goose.Proofs.Lower.lower_correct_ctl returningLoopModule (by
    have hglobals : (#[].all fun (g : Core.Global) => exprOk g.init) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro global hglobal
      simp at hglobal
    simp only [Goose.Proofs.Lower.moduleOk, returningLoopModule, hglobals,
      Array.getElem?_singleton, ite_true, eq_self, Bool.true_and, Array.isEmpty_empty]
    change flowBlockOk returningLoopBody = true
    simp only [returningLoopBody, flowBlockOk.eq_def, flowStmtsOk.eq_def, flowStmtOk.eq_def,
      stmtReturnOk, stmtOk.eq_def, printOk.eq_def, exprOk.eq_def, Bool.true_and, Bool.and_true])
    fuel profile outcome trace h

end Goose.Lower.ControlChecks
