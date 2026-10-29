import Goose.Lower.DemandCallActualReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem DemandInstructionStop.monoFuel {cx : FnCtx} {fuel larger : Nat} {point : DemandRuntimePoint}
    {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel point stop after)
    (nonTimeout : stop ≠ .timeout) (bound : fuel ≤ larger) :
    DemandInstructionStop cx larger point stop after := by
  cases stopped with
  | timeout => exact (nonTimeout rfl).elim
  | @definition fuel point id op stop after instruction execution =>
    cases larger with
    | zero => omega
    | succ larger =>
      exact .definition instruction (Goose.Proofs.GIRFuel.execOp_stop_fuel_mono (by omega) nonTimeout execution)
  | @effect fuel point effect stop after instruction execution =>
    cases larger with
    | zero => omega
    | succ larger => exact .effect instruction execution

theorem DemandRuntimePrefix.runAt_stop {cx : FnCtx} {length : Nat} {before reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx length before reached) {fuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx fuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    ∃ targetFuel, GIR.runAt cx before.point before.frame targetFuel before.state = .stop stop after := by
  obtain ⟨extra, fueled⟩ := steps.fueled
  let targetFuel := length + extra + fuel + 1
  have raised := fueled.monoFuel (show length + extra + 1 ≤ targetFuel by dsimp [targetFuel]; omega)
  have stopRaised := stopped.monoFuel nonTimeout (show fuel ≤ targetFuel - length by dsimp [targetFuel]; omega)
  exact ⟨targetFuel, raised.runAt.trans stopRaised.runAt⟩

#print axioms DemandInstructionStop.monoFuel
#print axioms DemandRuntimePrefix.runAt_stop
end Goose.Lower
