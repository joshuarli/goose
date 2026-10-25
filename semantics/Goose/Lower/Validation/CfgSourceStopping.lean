import Goose.Lower.Validation.DeadFrontier
import Goose.Lower.Validation.CfgCoreNoReturn

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem cfg_emitTerm_stopped (term : Term) (env : LEnv) (before : LS) :
    (emitTerm term env before).2.cur = none := by
  cases current : before.cur with
  | none => rw [emitTerm_none term env current]; exact current
  | some block => rw [emitTerm_run term env current]

theorem cfg_stopped_call (callee : ContextId) (args : List ValueId) (origin : Option OriginId)
    (env : LEnv) (before : LS) (stops : env.mod.noReturn callee = true) :
    ((do
      let value ← emitDef (.call callee args origin)
      if (← read).mod.noReturn callee then emitTerm .unreachable
      pure value) env before).2.cur = none := by
  change ((if env.mod.noReturn callee then
    (do emitTerm .unreachable; pure (emitDef (.call callee args origin) env before).1)
    else pure (emitDef (.call callee args origin) env before).1)
    env (emitDef (.call callee args origin) env before).2).2.cur = none
  rw [stops]
  simp only [ite_true, bind_run, pure_run]
  exact cfg_emitTerm_stopped .unreachable env _

mutual

theorem cfg_stops_lowerStmt (context : Option LoopCtx) (stmt : Stmt) (env : LEnv)
    (before after : LS) (result : Unit) (stopped : stmt.stops env.mod.noReturn = true)
    (run : lowerStmt context stmt env before = (result, after)) : after.cur = none := by
  cases stmt <;> try contradiction
  case abort message origin =>
    have output := cfg_emitTerm_stopped (.abort .userAbort (some origin)) env before
    change emitTerm (.abort .userAbort (some origin)) env before = (result, after) at run
    rw [run] at output
    exact output
  case exit expression origin =>
    simp only [lowerStmt, bind_eq] at run
    obtain ⟨value, middle, emitted, closed⟩ := run
    have output := cfg_emitTerm_stopped (.exit value (some origin)) env middle
    rw [closed] at output
    exact output
  case expr expression origin =>
    cases expression <;> try contradiction
    case call callee args callOrigin =>
      simp only [lowerStmt, bind_eq] at run
      obtain ⟨value, middle, callRun, finished⟩ := run
      rw [pure_run] at finished
      obtain ⟨_, rfl⟩ := Prod.mk.inj finished
      change env.mod.noReturn callee = true at stopped
      rw [lowerExpr] at callRun
      obtain ⟨values, arguments, argsRun, called⟩ := bind_eq.mp callRun
      have output := cfg_stopped_call callee values (some callOrigin) env arguments stopped
      rw [called] at output
      exact output
  case ifS condition yes no origin =>
    cases no with
    | none => contradiction
    | some no =>
      have both := Bool.and_eq_true_iff.mp stopped
      simp only [lowerStmt, bind_eq] at run
      obtain ⟨value, tested, conditionRun, tail⟩ := run
      cases current : tested.cur with
      | none =>
        rw [whenLive_none _ _ env current] at tail
        obtain ⟨_, rfl⟩ := Prod.mk.inj tail
        exact current
      | some block =>
        rw [whenLive_some _ _ env current] at tail
        simp only [bind_eq] at tail
        obtain ⟨⟨yesBlock, noBlock⟩, forked, forkRun, ignored, selectedYes, selectYes,
          yesValue, yesEnd, yesRun, yesCurrent, savedYes, saveYes, ignored', selectedNo, selectNo,
          noValue, noEnd, noRun, noCurrent, savedNo, saveNo, joined⟩ := tail
        have yesStopped := cfg_stops_lowerBlock context [] false yes env selectedYes yesEnd yesValue both.1 yesRun
        have noStopped := cfg_stops_lowerBlock context [] false no env selectedNo noEnd noValue both.2 noRun
        rw [curBlock_run, yesStopped] at saveYes
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveYes
        rw [curBlock_run, noStopped] at saveNo
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveNo
        change setCur none env noEnd = (result, after) at joined
        rw [setCur_run] at joined
        obtain ⟨_, rfl⟩ := Prod.mk.inj joined
        rfl

theorem cfg_stops_lowerStmts (context : Option LoopCtx) (stmts : List Stmt) (env : LEnv)
    (before after : LS) (result : Unit) (stopped : stmtsStop env.mod.noReturn stmts = true)
    (run : lowerStmts context stmts env before = (result, after)) : after.cur = none := by
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
      have dead : before.cur.isSome = false := (Prod.mk.inj tested).1
      cases current : before.cur with
      | none => rfl
      | some block => simp [current] at dead
    | true =>
      simp only [ite_true, bind_eq] at tail
      obtain ⟨ignored, first, headRun, restRun⟩ := tail
      simp only [stmtsStop, Bool.or_eq_true, Bool.and_eq_true] at stopped
      rcases stopped with headStops | ⟨_, restStops⟩
      · exact dead_lowerStmts context rest env first result after restRun
          (cfg_stops_lowerStmt context stmt env before first ignored headStops headRun)
      · exact cfg_stops_lowerStmts context rest env first after result restStops restRun

theorem cfg_stops_lowerBlock (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (want : Bool) (block : Core.Block) (env : LEnv) (before after : LS) (result : ValueId)
    (stopped : block.stops env.mod.noReturn = true)
    (run : lowerBlock context pre want block env before = (result, after)) : after.cur = none := by
  cases block with
  | mk scope stmts value =>
    simp only [lowerBlock, inScope, bind_eq] at run
    obtain ⟨ignored, entered, enterRun, ignored', pushed, pushRun, returned, actionEnd, actionRun,
      ignored'', popped, popRun, finished⟩ := run
    obtain ⟨initializedResult, initialized, initRun, ignored''', bodyEnd, bodyRun,
      valueResult, valued, valueRun, ignored'''', left, leaveRun, yielded⟩ := actionRun
    have stoppedBody := cfg_stops_lowerStmts context stmts env initialized bodyEnd _ stopped bodyRun
    have stoppedValue := dead_lowerBlockValue want value env bodyEnd valueResult valued valueRun stoppedBody
    have stoppedLeave := dead_emitEffect (.leave scope) env valued _ left leaveRun stoppedValue
    rw [pure_run] at yielded
    obtain ⟨_, rfl⟩ := Prod.mk.inj yielded
    rw [popScope_run] at popRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj popRun
    rw [pure_run] at finished
    obtain ⟨_, rfl⟩ := Prod.mk.inj finished
    exact stoppedLeave

end

end Goose.Lower.Validation
