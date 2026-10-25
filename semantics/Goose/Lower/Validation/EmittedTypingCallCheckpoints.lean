import Goose.Lower.Validation.EmittedTypingCalls
import Goose.Lower.Validation.EmittedTypingCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_passable_values_bound {state : LS} {params : List Ty} {values : List ValueId}
    (typed : PassableValues state params values) : ∀ value ∈ values, value < state.vals.size := by
  induction typed with
  | nil => intro value member; cases member
  | @cons param value params values head tail inductionHypothesis =>
    intro operand member
    rcases List.mem_cons.mp member with rfl | rest
    · obtain ⟨actual, recorded, permission⟩ := head
      exact (Array.getElem?_eq_some_iff.mp recorded).1
    · exact inductionHypothesis operand rest

theorem emitted_checked_lowerExpr_call {env : Core.TEnv} {context : ContextId} {args : List Arg}
    {origin : OriginId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (type, finish))
    (results : List Ty) {initial before : LS}
    (arguments : EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerArgs args (lowerEnv env.mod env.vars results) before).2)
    (passing : ∀ ctx callee, env.mod.contexts[context]? = some ctx → env.mod.impls[ctx.impl]? = some callee →
      ∀ block, (lowerArgs args (lowerEnv env.mod env.vars results) before).2.cur = some block →
      PassableValues (lowerArgs args (lowerEnv env.mod env.vars results) before).2
        (callee.params.toList.map (tyOfVar callee ·.var))
        (lowerArgs args (lowerEnv env.mod env.vars results) before).1) :
    EmittedBuilder (lowerEnv env.mod env.vars results) initial
      (lowerExpr (.call context args origin) (lowerEnv env.mod env.vars results) before).2 := by
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt,
    length, argsSource, resultSource⟩ := tyExpr_call_tables source
  let le := lowerEnv env.mod env.vars results
  let loweredArgs := lowerArgs args le before
  have callBuilder := arguments.emitDef (.call context loweredArgs.1 (some origin)) (by
    intro active
    change loweredArgs.2.cur.isSome = true at active
    cases current : loweredArgs.2.cur with
    | none => simp [current] at active
    | some block =>
      exact ⟨.data type, call_resultTy_of_passable
        (lower_context_sigs_at env.vars results contextAt calleeAt)
        (passing ctx callee contextAt calleeAt block current) resultSource origin⟩) (by
    intro active operand member
    change loweredArgs.2.cur.isSome = true at active
    cases current : loweredArgs.2.cur with
    | none => simp [current] at active
    | some block =>
      have actual : operand ∈ loweredArgs.1 := by simpa [Op.uses] using member
      exact emitted_passable_values_bound (passing ctx callee contextAt calleeAt block current) operand actual)
  generalize run : lowerExpr (.call context args origin) le before = output
  obtain ⟨value, after⟩ := output
  dsimp only
  simp only [lowerExpr, bind_eq] at run
  obtain ⟨values, argsEnd, argsRun, result, called, callRun, reader, readEnd, readRun, tailRun⟩ := run
  have argsRunExact : lowerArgs args (lowerEnv env.mod env.vars results) before = (values, argsEnd) := argsRun
  have actualCall : EmittedBuilder le initial
      (Goose.Lower.emitDef (.call context values (some origin)) le argsEnd).2 := by
    simpa only [loweredArgs, argsRun, argsRunExact] using callBuilder
  rw [callRun] at actualCall
  dsimp only at actualCall
  rw [read_apply] at readRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj readRun
  cases noReturn : le.mod.noReturn context
  · simp only [noReturn, Bool.false_eq_true, reduceIte, pure_run] at tailRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
    exact actualCall
  · simp only [noReturn, reduceIte, bind_eq] at tailRun
    obtain ⟨u, stopped, stopRun, pureRun⟩ := tailRun
    rw [pure_run] at pureRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pureRun
    have stoppedBuilder := actualCall.emitTerm .unreachable (by intro active value member; simp [Term.uses] at member)
    rw [stopRun] at stoppedBuilder
    exact stoppedBuilder

end Goose.Lower.Validation
