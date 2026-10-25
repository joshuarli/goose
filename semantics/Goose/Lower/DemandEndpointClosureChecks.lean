import Goose.Lower.ReflectionChecks
import Goose.Evidence.Execution

namespace Goose.Lower.DemandEndpointClosureChecks

open Goose.Core Goose.GIR Goose.Evidence

private def entryFrame : GIR.Frame := ⟨0, [], {}, 1⟩
private def entryState : St := { St.initial with nextAct := 1 }
private def headerFrame : GIR.Frame := { entryFrame with scopes := [(0, 0)] }
private def headerState : St := { entryState with nextScope := 1 }

private def sourceBody (fuel : Nat) : M Flow :=
  Core.execBlock fuel ⟨.release, ReflectionChecks.infiniteSource⟩ ⟨#[], 0, [], 1⟩ []
    (.mk 0 [.while (.bool true) (.mk 1 [] none) 0] none)

private def beforeHeader (point : Pt) (_frame : GIR.Frame) (_state : St) : Prop := point ≠ (1, 0)

theorem actual_loop_entry :
    RuntimePoint ⟨.release, lower ReflectionChecks.infiniteSource⟩ ReflectionChecks.loopFunction
      (0, 0) entryFrame entryState := by
  apply RuntimePoint.entry (fuel := 2) (before := St.initial)
  · decide
  · simp [lower, ReflectionChecks.infiniteSource, GIR.initGlobals, pure_apply]
  · exact ReflectionChecks.actual_lowered_loop
  · refine ⟨rfl, 0, entryState, rfl, ?_⟩
    simp [enterBlock, ReflectionChecks.loopFunction, instsAt, bindParams, entryFrame,
      pure_apply]

theorem actual_loop_header :
    RuntimePoint ⟨.release, lower ReflectionChecks.infiniteSource⟩ ReflectionChecks.loopFunction
      (1, 0) headerFrame headerState := by
  have entered : RuntimePoint ⟨.release, lower ReflectionChecks.infiniteSource⟩ ReflectionChecks.loopFunction
      (0, 1) headerFrame headerState := by
    apply RuntimePoint.step actual_loop_entry
    apply RuntimeStep.effect (effect := .enter 0)
    · rfl
    · rfl
  apply RuntimePoint.step entered
  apply RuntimeStep.branch (args := []) (values := []) (readState := headerState)
  · rfl
  · rfl
  · simp [enterBlock, ReflectionChecks.loopFunction, instsAt, bindParams, pure_apply]

theorem every_fuel_endpoint_before_header (fuel : Nat) :
    ReflectAtFuel fuel ReflectionChecks.loopContext (0, 0) entryFrame sourceBody
      (fun _ after point frame => beforeHeader point frame after) entryState := by
  intro result nonTimeout executed
  obtain ⟨after, timedOut⟩ := ReflectionChecks.entry_timeout fuel entryFrame entryState
  exact (nonTimeout after (executed.symm.trans timedOut)).elim

private def EndpointPrefixClosure : Prop :=
  ∀ invariant : Pt → GIR.Frame → St → Prop,
    invariant (0, 0) entryFrame entryState →
    (∀ fuel, ReflectAtFuel fuel ReflectionChecks.loopContext (0, 0) entryFrame sourceBody
      (fun _ after point frame => invariant point frame after) entryState) →
    ∀ point frame state,
      RuntimePoint ⟨.release, lower ReflectionChecks.infiniteSource⟩ ReflectionChecks.loopFunction
        point frame state → invariant point frame state

theorem accepted_endpoint_prefix_closure_is_false :
    Core.validate ReflectionChecks.infiniteSource = .ok () ∧ ¬ EndpointPrefixClosure := by
  refine ⟨ReflectionChecks.infiniteSource_accepted, ?_⟩
  intro closure
  have impossible := closure beforeHeader (by simp [beforeHeader]) every_fuel_endpoint_before_header
    (1, 0) headerFrame headerState actual_loop_header
  exact impossible rfl

end Goose.Lower.DemandEndpointClosureChecks
