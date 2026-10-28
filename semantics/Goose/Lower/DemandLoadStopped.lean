import Goose.Lower.DemandGeneratedLoad
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_load_runtime_stop {cfg : Cfg} {env : Env} {place : Place}
    {state addressedState after : St} (source : ExprSource cfg env (.read place) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.read place)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location addressedState)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial
      (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (extended : ExtT (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, addressedState⟩ stop after)
    (nonTimeout : stop ≠ .timeout) :
    evalExpr (fuel + 1) cfg env (.read place) state = .stop stop after := by
  have site := GeneratedDemandInstruction.load_auto occurrence rows post.pp extended
  have cell := post.has ((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location)) (by simp)
  cases stopped with
  | timeout => exact (nonTimeout rfl).elim
  | definition instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    simp only [execOp, execPure, getVal_of cell, expectRef, bind_apply, pure_apply] at execution
    cases read : readLoc location addressedState with
    | ok value nextState => simp [read] at execution
    | stop error nextState =>
      simp only [read, Res.stop.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      simp only [evalExpr, bind_apply, placed, read]
  | effect instruction execution => cases site.instruction.symm.trans instruction

#print axioms accepted_generated_load_runtime_stop

end Goose.Lower
