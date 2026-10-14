import Goose.Lower.Flow
import Goose.Lower.ReturnChecks

namespace Goose.Lower.FlowChecks

open Goose.Core Goose.GIR Goose.Lower.UnwindChecks Goose.Lower.ReturnChecks

def returningBlock : Core.Block := .mk 2 [returningStmt] none

def blockBuilder (m : Core.Module) : LS :=
  (lowerBlock none [] false returningBlock (lowerEnv m variables []) scopedBuilder).2

def blockFunction (m : Core.Module) : Func :=
  { scopeFunction with blocks := finishBlocks (blockBuilder m).blocks }

theorem concrete_returning_block (cfg : Cfg) (fuel : Nat) :
    SimG ⟨⟨cfg.profile, lower cfg.mod⟩, blockFunction cfg.mod⟩ (0, 0) beforeFrame
      (execBlock fuel cfg beforeEnv [] returningBlock >>= prepareReturn beforeEnv)
      (BlockFlowPost cfg beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, blockFunction cfg.mod⟩
        scopedBuilder beforeFrame (blockBuilder cfg.mod) returningBlock false 0) := by
  apply blockReturnClaim fuel none [] [] false returningBlock rfl cfg beforeEnv
    (by simp) (lowerEnv cfg.mod variables []) scopedBuilder (blockBuilder cfg.mod) 0
    (0, 0) ⟨⟨cfg.profile, lower cfg.mod⟩, blockFunction cfg.mod⟩ beforeFrame
  · rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (blockBuilder cfg.mod)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · trivial

#guard match (execBlock 10 ⟨.release, sourceModule⟩ beforeEnv [] returningBlock >>=
    prepareReturn beforeEnv) localState with
  | .ok (.ret (Val.int IntTy.i64 9)) state =>
    (state.store.roots[RootInst.local 0 11 0]?).isNone
  | _ => false

#guard match runAt ⟨⟨.release, lower sourceModule⟩, blockFunction sourceModule⟩ (0, 0)
    beforeFrame 20 localState with
  | .ok (Val.int IntTy.i64 9) state =>
    (state.store.roots[RootInst.local 0 11 0]?).isNone
  | _ => false

end Goose.Lower.FlowChecks
