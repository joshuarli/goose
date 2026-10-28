import Goose.Lower.DemandCallPrefixCompare

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive DemandEffectPrefix (cx : FnCtx) : Nat → DemandRuntimePoint → DemandRuntimePoint → Prop
  | zero (point : DemandRuntimePoint) : DemandEffectPrefix cx 0 point point
  | next {length : Nat} {point : Pt} {frame nextFrame : GIR.Frame} {state nextState : St}
      {effect : Effect} {after : DemandRuntimePoint}
      (instruction : instAt cx.fn point = some (.eff effect))
      (execution : execEff cx.fn frame effect state = .ok nextFrame nextState)
      (rest : DemandEffectPrefix cx length ⟨(point.1, point.2 + 1), nextFrame, nextState⟩ after) :
      DemandEffectPrefix cx (length + 1) ⟨point, frame, state⟩ after

theorem DemandEffectPrefix.runtime {cx : FnCtx} {length : Nat} {before after : DemandRuntimePoint}
    (steps : DemandEffectPrefix cx length before after) : DemandRuntimePrefix cx length before after := by
  induction steps with
  | zero => exact .zero _
  | next instruction execution tail ih => exact .next (.effect instruction execution) ih

theorem DemandEffectPrefix.compare_maximal {cx : FnCtx} {expectedLength actualLength fuel : Nat}
    {start expectedEnd actualEnd : DemandRuntimePoint}
    (expected : DemandEffectPrefix cx expectedLength start expectedEnd)
    (actual : DemandRuntimePrefix cx actualLength start actualEnd)
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel actualEnd next) :
    ∃ rest, expectedLength + rest = actualLength ∧ DemandRuntimePrefix cx rest expectedEnd actualEnd := by
  induction expected generalizing actualLength actualEnd with
  | zero => exact ⟨_, by simp, actual⟩
  | @next length point frame nextFrame state nextState effect after instruction execution tail ih =>
    rcases actual.uncons with ⟨rfl, rfl⟩ | ⟨actualTailLength, actualMiddle, rfl, actualStep, actualTail⟩
    · exact (maximal _ (.effect instruction execution)).elim
    · obtain ⟨actualFuel, actualInstruction⟩ := runtimeStep_demandInstructionStep actualStep
      have expectedInstruction : DemandInstructionStep cx actualFuel ⟨point, frame, state⟩
          ⟨(point.1, point.2 + 1), nextFrame, nextState⟩ := .effect instruction execution
      have equal := expectedInstruction.deterministic actualInstruction
      have equalPoints : actualMiddle = ⟨(point.1, point.2 + 1), nextFrame, nextState⟩ := by
        have eta : actualMiddle = ⟨actualMiddle.point, actualMiddle.frame, actualMiddle.state⟩ := by cases actualMiddle; rfl
        exact eta.trans equal.symm
      subst actualMiddle
      obtain ⟨rest, count, later⟩ := ih actualTail maximal
      exact ⟨rest, by omega, later⟩

#print axioms DemandEffectPrefix.runtime
#print axioms DemandEffectPrefix.compare_maximal
end Goose.Lower
