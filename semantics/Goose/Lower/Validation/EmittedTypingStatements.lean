import Goose.Lower.Validation.EmittedTypingControlCheckpoints
import Goose.Lower.Validation.EmittedTypingLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_lowerStmt_abort {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (loop : Option LoopCtx)
    (message : String) (origin : OriginId) :
    EmittedBuilder le initial (lowerStmt loop (.abort message origin) le before).2 := by
  apply builder.emitTerm (.abort .userAbort (some origin))
  intro active value member
  simp [Term.uses] at member

theorem emitted_checked_lowerStmt_break {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (loop : Option LoopCtx) (origin : OriginId) :
    EmittedBuilder le initial (lowerStmt loop (.brk origin) le before).2 := by
  cases loop with
  | none => exact builder
  | some context =>
    apply (builder.leaveTo context.depth).emitTerm (.br context.breakTo [])
    intro active value member
    simp [Term.uses] at member

theorem emitted_checked_lowerStmt_continue {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (loop : Option LoopCtx)
    (typed : EmittedLoopTypes loop before) (origin : OriginId) :
    EmittedBuilder le initial (lowerStmt loop (.cont origin) le before).2 := by
  cases loop with
  | none => exact builder
  | some context =>
    have left := builder.leaveTo context.depth
    cases continuation : context.cont with
    | jump header =>
      have branched := left.emitTerm (.br header []) (by
        intro active value member
        simp [Term.uses] at member)
      simpa only [lowerStmt, continuation, bind_run] using branched
    | next header type counter =>
      have counterTyped : before.vals[counter]? = some (some (.data (.int type))) := by
        simpa [EmittedLoopTypes, continuation] using typed
      have retained := (EmittedRun.leaveTo context.depth le before).prefix.typed
      have counterAfter := retained _ _ counterTyped
      have advanced := left.emitDef (.next type counter) (by
        intro active
        exact ⟨.data (.int type), by
          simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, counterAfter,
            pure, Except.pure, bind, Except.bind]⟩) (by
        intro active operand member
        have same : operand = counter := by simpa [Op.uses] using member
        subst operand
        exact (Array.getElem?_eq_some_iff.mp counterAfter).1)
      have branched := advanced.emitTerm
        (.br header [(emitDef (.next type counter) le (leaveTo context.depth le before).2).1]) (by
          intro active operand member
          have same : operand = (emitDef (.next type counter) le (leaveTo context.depth le before).2).1 := by
            simpa [Term.uses] using member
          subst operand
          exact value_emitDef (.next type counter) _ _ _ _ rfl active)
      simpa only [lowerStmt, continuation, bind_run] using branched

theorem emitted_checked_lowerStmt_expression {le : LEnv} {initial before : LS}
    (loop : Option LoopCtx) (expr : Expr) (origin : OriginId)
    (child : EmittedBuilder le initial (lowerExpr expr le before).2) :
    EmittedBuilder le initial (lowerStmt loop (.expr expr origin) le before).2 := child

end Goose.Lower.Validation
