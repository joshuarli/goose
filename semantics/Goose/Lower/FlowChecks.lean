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
  cases fuel with
  | zero =>
    simp only [execBlock]
    exact SimG.of_timeout_bind
  | succ n =>
    let le := lowerEnv cfg.mod variables []
    let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, blockFunction cfg.mod⟩
    have hlow : lowerBlock none [] false (.mk 2 [returningStmt] none) le scopedBuilder =
        (0, blockBuilder cfg.mod) := rfl
    obtain ⟨entered, initialized, statements, valued, left, u0, u, result,
      henter, hinit, hstatements, hvalue, hleave, hfinal, hresult⟩ := prefixBlock_unfold hlow
    have hext : ExtT (blockBuilder cfg.mod) cx.fn.blocks := Goose.Proofs.Lower.extT_finish _
    have hextLeft : ExtT left cx.fn.blocks := by rw [hfinal] at hext; exact hext
    have hextValue := hextLeft.of_adv (adv_emitEffect hleave)
    have hextStatements := hextValue.of_adv (advB_lowerBlockValue false none _ _ _ _ hvalue)
    have hextInitialized := hextStatements.of_adv (advB_lowerStmts none [returningStmt] _ _ _ _ hstatements)
    simp only [initSlots, pure_run] at hinit
    obtain ⟨_, rfl⟩ := Prod.mk.inj hinit
    have hextEntered : ExtT entered cx.fn.blocks := hextInitialized
    have related : Rel cfg beforeEnv cx beforeFrame scopedBuilder := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [show returningBlock = .mk 2 [returningStmt] none from rfl, prepareReturn_execBlock]
    unfold preparedCoreBlock
    simp only [bindAll, pure_bind]
    refine SimG.bind (block_enter (show scopedBuilder.pp = some (0, 0) from rfl)
      henter hextEntered related) fun scopeInstance pt1 fr1 ⟨hpp1, _, _, hrel1⟩ => ?_
    have hppInner : ({ entered with stack := 2 :: entered.stack } : LS).pp = some pt1 := hpp1
    cases n with
    | zero =>
      simp only [execStmts, bind_assoc]
      exact SimG.of_timeout_bind
    | succ n =>
      obtain ⟨block, current, _, _⟩ := LS.pp_some hppInner
      have singleton : lowerStmts none [returningStmt] le { entered with stack := 2 :: entered.stack } =
          lowerStmt none returningStmt le { entered with stack := 2 :: entered.stack } := by
        simp [lowerStmts, bind_run, isLive_run current, pure_run]
      have hstatement := singleton.symm.trans hstatements
      rw [prepareReturn_execStmts, bind_assoc]
      refine SimG.bind (stmt_ret_some_prepared n none (.read (.var 0)) 0 rfl le rfl
        { entered with stack := 2 :: entered.stack } statements u pt1 cfg
        { beforeEnv with scopes := (2, scopeInstance) :: beforeEnv.scopes } cx fr1
        hstatement hppInner hextStatements hrel1)
        fun flow pt2 fr2 returned => ?_
      obtain ⟨value, returned, site⟩ := returned
      subst flow
      simp only [returnStmtsTail, pure_bind]
      exact SimG.ret (Or.inr ⟨value, 0, rfl, site⟩)


private def unitReturningBlock : Core.Block := .mk 2 [.ret none 0] none

private def unitReturningBuilder (m : Core.Module) : LS :=
  (lowerBlock none [] false unitReturningBlock (lowerEnv m variables []) scopedBuilder).2

private def unitReturningFunction (m : Core.Module) : Func :=
  { scopeFunction with blocks := finishBlocks (unitReturningBuilder m).blocks }

theorem concrete_unit_returning_block (cfg : Cfg) (fuel : Nat) :
    SimG ⟨⟨cfg.profile, lower cfg.mod⟩, unitReturningFunction cfg.mod⟩ (0, 0) beforeFrame
      (execBlock fuel cfg beforeEnv [] unitReturningBlock >>= prepareReturn beforeEnv)
      (BlockFlowPost cfg beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, unitReturningFunction cfg.mod⟩
        scopedBuilder beforeFrame (unitReturningBuilder cfg.mod) unitReturningBlock false 0) := by
  apply blockReturnClaim fuel none [] [] false unitReturningBlock rfl cfg beforeEnv
    (by simp) (lowerEnv cfg.mod variables []) scopedBuilder (unitReturningBuilder cfg.mod) 0
    (0, 0) ⟨⟨cfg.profile, lower cfg.mod⟩, unitReturningFunction cfg.mod⟩ beforeFrame
  · rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (unitReturningBuilder cfg.mod)
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
