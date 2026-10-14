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

end Goose.Lower.ControlChecks
