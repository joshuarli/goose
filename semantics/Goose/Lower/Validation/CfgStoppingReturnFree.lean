import Goose.Lower.Validation.CfgSourceReturnFree
import Goose.Lower.Validation.CfgSourceStopping

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem cfg_stopped_lowerStmts_run (context : Option LoopCtx) (stmts : List Stmt)
    (env : LEnv) (state : LS) (stopped : state.cur = none) :
    lowerStmts context stmts env state = ((), state) := by
  cases stmts with
  | nil => rfl
  | cons stmt rest =>
    simp only [lowerStmts, bind_run, isLive_none stopped, Bool.false_eq_true, ite_false, pure_run]

mutual

theorem returnFree_stopping_lowerStmt (context : Option LoopCtx) (stmt : Stmt) (env : LEnv)
    (before after : LS) (result : Unit) (free : ReturnFreeStoppingStmt env.mod.noReturn stmt)
    (stopped : stmt.stops env.mod.noReturn = true)
    (run : lowerStmt context stmt env before = (result, after)) (checked : BuilderNoReturn before) :
    BuilderNoReturn after := by
  cases stmt <;> try contradiction
  case abort message origin =>
    exact returnFree_emitTerm (.abort .userAbort (some origin)) (by intro values org same; cases same)
      env before result after run checked
  case exit expression origin =>
    exact ReturnFreeRun.bind (returnFree_lowerExpr expression free)
      (fun value => returnFree_emitTerm (.exit value (some origin)) (by intro values org same; cases same))
      env before result after run checked
  case expr expression origin =>
    cases expression <;> try contradiction
    case call callee args callOrigin =>
      exact ReturnFreeRun.bind (ReturnFreeRun.bind (returnFree_lowerArgs args free)
        (fun values => returnFree_call callee values (some callOrigin))) (fun _ => returnFree_pure ())
        env before result after run checked
  case ifS condition yes no origin =>
    cases no with
    | none => contradiction
    | some no =>
      have both := Bool.and_eq_true_iff.mp stopped
      simp only [lowerStmt, bind_eq] at run
      obtain ⟨value, tested, conditionRun, tail⟩ := run
      have conditionChecked := returnFree_lowerExpr condition free.1 env before value tested conditionRun checked
      cases current : tested.cur with
      | none =>
        rw [whenLive_none _ _ env current] at tail
        obtain ⟨_, rfl⟩ := Prod.mk.inj tail
        exact conditionChecked
      | some block =>
        rw [whenLive_some _ _ env current] at tail
        simp only [bind_eq] at tail
        obtain ⟨⟨yesBlock, noBlock⟩, forked, forkRun, ignored, selectedYes, selectYes,
          yesValue, yesEnd, yesRun, yesCurrent, savedYes, saveYes, ignored', selectedNo, selectNo,
          noValue, noEnd, noRun, noCurrent, savedNo, saveNo, joined⟩ := tail
        have forkChecked := returnFree_fork value env tested _ forked forkRun conditionChecked
        have selectedYesChecked := returnFree_setCur _ env forked _ selectedYes selectYes forkChecked
        have yesChecked := returnFree_stopping_lowerBlock context [] false yes env selectedYes yesEnd
          yesValue free.2.1 both.1 yesRun selectedYesChecked
        have savedYesChecked := returnFree_curBlock env yesEnd _ savedYes saveYes yesChecked
        have selectedNoChecked := returnFree_setCur _ env savedYes _ selectedNo selectNo savedYesChecked
        have noChecked := returnFree_stopping_lowerBlock context [] false no env selectedNo noEnd
          noValue free.2.2 both.2 noRun selectedNoChecked
        have savedNoChecked := returnFree_curBlock env noEnd _ savedNo saveNo noChecked
        exact returnFree_joinArms yesCurrent noCurrent env savedNo result after joined savedNoChecked

theorem returnFree_stopping_lowerStmts (context : Option LoopCtx) (stmts : List Stmt) (env : LEnv)
    (before after : LS) (result : Unit) (free : ReturnFreeStoppingStmts env.mod.noReturn stmts)
    (stopped : stmtsStop env.mod.noReturn stmts = true)
    (run : lowerStmts context stmts env before = (result, after)) (checked : BuilderNoReturn before) :
    BuilderNoReturn after := by
  cases stmts with
  | nil => contradiction
  | cons stmt rest =>
    simp only [lowerStmts, bind_eq] at run
    obtain ⟨live, middle, tested, tail⟩ := run
    have stable : middle = before := by
      change (before.cur.isSome, before) = (live, middle) at tested
      exact (Prod.mk.inj tested).2.symm
    subst middle
    cases live with
    | false =>
      simp only [Bool.false_eq_true, ite_false, pure_run] at tail
      obtain ⟨_, rfl⟩ := Prod.mk.inj tail
      exact checked
    | true =>
      simp only [ite_true, bind_eq] at tail
      obtain ⟨ignored, first, headRun, restRun⟩ := tail
      cases headStops : stmt.stops env.mod.noReturn with
      | false =>
        simp only [ReturnFreeStoppingStmts, headStops, Bool.false_eq_true, ite_false] at free
        have firstChecked := returnFree_lowerStmt context stmt free.1 env before ignored first headRun checked
        have restStops : stmtsStop env.mod.noReturn rest = true := by
          have both : stmt.isPlain = true ∧ stmtsStop env.mod.noReturn rest = true := by
            simpa only [stmtsStop, headStops, Bool.false_or, Bool.and_eq_true] using stopped
          exact both.2
        exact returnFree_stopping_lowerStmts context rest env first after result free.2 restStops restRun firstChecked
      | true =>
        simp only [ReturnFreeStoppingStmts, headStops, ite_true] at free
        have firstChecked := returnFree_stopping_lowerStmt context stmt env before first ignored free headStops headRun checked
        have firstStopped := cfg_stops_lowerStmt context stmt env before first ignored headStops headRun
        rw [cfg_stopped_lowerStmts_run context rest env first firstStopped] at restRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj restRun
        exact firstChecked

theorem returnFree_stopping_lowerBlock (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (want : Bool) (block : Core.Block) (env : LEnv) (before after : LS) (result : ValueId)
    (free : ReturnFreeStoppingBlock env.mod.noReturn block)
    (stopped : block.stops env.mod.noReturn = true)
    (run : lowerBlock context pre want block env before = (result, after)) (checked : BuilderNoReturn before) :
    BuilderNoReturn after := by
  cases block with
  | mk scope stmts value =>
    simp only [lowerBlock, inScope, bind_eq] at run
    obtain ⟨ignored, entered, enterRun, ignored', pushed, pushRun, returned, actionEnd, actionRun,
      ignored'', popped, popRun, finished⟩ := run
    obtain ⟨initializedResult, initialized, initRun, ignored''', bodyEnd, bodyRun,
      valueResult, valued, valueRun, ignored'''', left, leaveRun, yielded⟩ := actionRun
    have enterChecked := returnFree_emitEffect _ env before _ entered enterRun checked
    have pushedChecked : BuilderNoReturn pushed := enterChecked.of_blocks (by
      rw [pushScope_run] at pushRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj pushRun
      rfl)
    have initChecked := returnFree_initSlots pre env pushed _ initialized initRun pushedChecked
    have bodyChecked := returnFree_stopping_lowerStmts context stmts env initialized bodyEnd _ free.1 stopped bodyRun initChecked
    have valueChecked := returnFree_lowerBlockValue want value free.2 env bodyEnd _ valued valueRun bodyChecked
    have leaveChecked := returnFree_emitEffect _ env valued _ left leaveRun valueChecked
    rw [pure_run] at yielded
    obtain ⟨_, rfl⟩ := Prod.mk.inj yielded
    rw [popScope_run] at popRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj popRun
    rw [pure_run] at finished
    obtain ⟨_, rfl⟩ := Prod.mk.inj finished
    exact leaveChecked

end

end Goose.Lower.Validation
