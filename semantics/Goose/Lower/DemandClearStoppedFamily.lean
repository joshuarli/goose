import Goose.Lower.DemandStoppedSequenceFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_clear_runtime_stop {cfg : Cfg} {env : Env} {place : Place} {origin : OriginId}
    {state addressedState after : St} (source : StmtSource cfg env (.clear place origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.clear place origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location addressedState)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (extended : ExtT (lowerStmt loop (.clear place origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, addressedState⟩ stop after)
    (nonTimeout : stop ≠ .timeout) :
    execStmt (fuel + 1) cfg env (.clear place origin) state = .stop stop after := by
  have site := GeneratedDemandInstruction.clear_auto occurrence rows post.pp extended
  have cell := post.has ((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location)) (by simp)
  cases stopped with
  | timeout => exact (nonTimeout rfl).elim
  | definition instruction execution => cases site.instruction.symm.trans instruction
  | effect instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    simp only [execEff, getVal_of cell, expectRef, bind_apply, pure_apply] at execution
    cases truncated : truncateLoc location 0 addressedState with
    | ok value final => simp [truncated] at execution
    | stop error final =>
      simp only [truncated, Res.stop.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      simp only [execStmt, bind_apply, placed, truncated]

theorem accepted_generated_global_clear_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (global : GlobalId) (origin : OriginId) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.clear (.global global) origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace (.global global) le before
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set addressed.1 (.val (.ref ⟨.global global, []⟩)), state⟩
  obtain ⟨child, _, _, rootsEq, _, _, _, _, canonical⟩ := source.clearChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place (.global global)) before := by
    rw [canonical.path]
    exact .clearPlace occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.clearPlace occurrence) required := .clearPlace rows
    simpa only [rootsEq, canonical.path] using inherited
  have site := GeneratedDemandInstruction.globalAddress_auto childOccurrence childRows input.atPoint
    (generated_clear_place_extended extended)
  have post := (Post.def_leaf (Post.init input.related input.atPoint)
    (show emitDef (.globalAddr global) le before = (addressed.1, addressed.2) from rfl)
    (generated_clear_place_extended extended) (.val (.ref ⟨.global global, []⟩))).1
  have placed : evalPlace 1 cfg env (.global global) state = .ok ⟨.global global, []⟩ state := by
    simp only [evalPlace, pure_apply]
  have firstStep (fuel : Nat) : DemandInstructionStep cx fuel ⟨start, initial, state⟩ middle := by
    apply DemandInstructionStep.definition site.instruction
    simp only [execOp, execPure, pure_apply]
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨length, current, rfl, actual, tail⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (firstStep targetFuel)).elim
  · obtain ⟨fuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
    have same := actualStep.deterministic (firstStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, boundary, rfl, cleared, residual⟩
    · have done := accepted_generated_clear_runtime_stop source occurrence rows placed post extended stopped nonTimeout
      refine .aborted 2 ?_
      simp only [bind_apply, done]
    · obtain ⟨_, _, _, _, _, _, _, evaluated, finalPost, result, finalBounded, demanded⟩ :=
        accepted_generated_clear_runtime_step source occurrence rows coverage admitted bounded realized placed post extended cleared
      have prepared : (execStmt 2 cfg env (.clear (.global global) origin) >>= prepareLoopFlow env loop) state =
          .ok (.normal .unit) boundary.state := by
        simp only [bind_apply, evaluated]
        cases loop <;> rfl
      exact .complete (by omega) (.next actual (.next cleared (.zero _))) residual prepared
        (.normal finalPost result finalBounded demanded.operands)

inductive StoppedControlStatements : List Stmt → Prop
  | nil : StoppedControlStatements []
  | clear (global : GlobalId) (origin : OriginId) {rest : List Stmt} (tail : StoppedControlStatements rest) :
      StoppedControlStatements (.clear (.global global) origin :: rest)
  | expression {expression : Expr} (origin : OriginId) (form : ReadStoppedExpression expression)
      {rest : List Stmt} (tail : StoppedControlStatements rest) : StoppedControlStatements (.expr expression origin :: rest)

theorem accepted_generated_control_statements_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (before : LS) (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (block : Core.Block) {statements : List Stmt} (fragment : StoppedControlStatements statements) :
    GeneratedStoppedSequencePrefixFamily cx results selected before loop bindings want block statements := by
  induction fragment with
  | nil => exact accepted_generated_stopped_sequence_nil selected before loop bindings want block
  | clear global origin tail ih =>
    intro state
    exact accepted_generated_stopped_sequence_cons selected before loop bindings want block
      (accepted_generated_global_clear_stopped_family selected loop global origin) ih
  | @expression expression origin form rest tail ih =>
    have head : GeneratedStoppedStatementPrefixFamily cx results selected loop (.expr expression origin) := by
      intro state
      exact accepted_generated_expression_statement_stopped_family selected loop expression origin
        (accepted_generated_read_stopped_expressions selected loop form)
    intro state
    exact accepted_generated_stopped_sequence_cons selected before loop bindings want block head ih

#print axioms accepted_generated_control_statements_stopped
#print axioms accepted_generated_clear_runtime_stop
#print axioms accepted_generated_global_clear_stopped_family

end Goose.Lower
