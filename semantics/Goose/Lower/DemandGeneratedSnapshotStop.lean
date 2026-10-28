import Goose.Lower.DemandGeneratedSnapshot
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_snapshot_runtime_stop {cfg : Cfg} {env : Env} {place : Place}
    {state sampledState after : St} (source : ViewSource cfg env (.of place) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.view (.of place)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location sampledState)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (extended : ExtT (lowerView (.of place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop} (nonTimeout : stop ≠ .timeout)
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, sampledState⟩ stop after) :
    evalView (fuel + 1) cfg env (.of place) state = .stop stop after := by
  have site := GeneratedDemandInstruction.snapshot_auto occurrence rows post.pp extended
  have cell := post.has ((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location)) (by simp)
  cases stopped with
  | timeout => exact (nonTimeout rfl).elim
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | definition instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    simp only [execOp, execPure, getVal_of cell, expectRef, bind_apply, pure_apply] at execution
    simp only [evalView, bind_apply, placed]
    cases read : readLoc location sampledState with
    | stop reason final =>
      simp only [read, Res.stop.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      rfl
    | ok value final =>
      simp only [read] at execution ⊢
      cases array : expectArray value final with
      | stop reason after =>
        simp only [array, Res.stop.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        rfl
      | ok sample after => simp only [array] at execution; cases execution

#print axioms accepted_generated_snapshot_runtime_stop
end Goose.Lower
