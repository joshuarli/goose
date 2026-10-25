import Goose.Proofs.ConstructionDeliveryFlowSoundnessComposition

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem controlFlow_dispatch (first second : List StaticFlow)
    (firstResult : α → StaticFlow) (secondResult : β → StaticFlow)
    (action : EvalM α) (next : α → EvalM β)
    (head : ControlFlowAction activation first firstResult action)
    (jumpsIncluded : ∀ scope kind, jumpControlFlow scope kind ∈ first → jumpControlFlow scope kind ∈ second)
    (tail : ∀ value, firstResult value ∈ first → ControlFlowAction activation second secondResult (next value)) :
    ControlFlowAction activation second secondResult (action >>= next) := by
  constructor
  · intro before bounded
    have reached := head.outcome before bounded
    have framed := head.frame before bounded
    cases evaluated : action before with
    | ok value middle =>
        simp only [evaluated, ControlFlowOutcome] at reached
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        have continued := (tail value reached).frame middle (framed.bounded bounded)
        cases finished : next value middle <;> simp only [finished] at continued
        all_goals simp only [bind, Bind.bind, evaluated, finished]
        all_goals change BreakStackFrame before _
        all_goals exact framed.trans continued
    | stop reason middle =>
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        simp only [bind, Bind.bind, evaluated]
        change BreakStackFrame before middle
        exact framed
    | escape address carriers middle =>
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        simp only [bind, Bind.bind, evaluated]
        change BreakStackFrame before middle
        exact framed
    | jump id kind middle =>
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        simp only [bind, Bind.bind, evaluated]
        change BreakStackFrame before middle
        exact framed
  · intro before bounded
    have reached := head.outcome before bounded
    have framed := head.frame before bounded
    cases evaluated : action before with
    | ok value middle =>
        simp only [evaluated, ControlFlowOutcome] at reached
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        have continued := (tail value reached).outcome middle (framed.bounded bounded)
        cases finished : next value middle with
        | ok result after => simpa only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome] using continued
        | stop reason after => simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
        | escape address carriers after => simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
        | jump id kind after =>
            simp only [finished, ControlFlowOutcome] at continued
            rcases continued with ⟨target, member, selected, compatible, equal, permitted⟩
            simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
            exact ⟨target, by simpa only [framed.stack] using member,
              by simpa only [framed.stack] using selected, compatible, equal, permitted⟩
    | stop reason middle => simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
    | escape address carriers middle => simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
    | jump id kind middle =>
        simp only [evaluated, ControlFlowOutcome] at reached
        rcases reached with ⟨target, member, selected, compatible, equal, permitted⟩
        simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
        exact ⟨target, member, selected, compatible, equal, jumpsIncluded _ _ permitted⟩

theorem controlFlow_loopDispatch (first jumps second : List StaticFlow)
    (secondResult : β → StaticFlow) (action : EvalM Flow) (next : Flow → EvalM β)
    (head : ControlFlowAction activation first resultControlFlow action)
    (iteration : ControlFlowAction activation jumps (fun _ => normalFlow) action)
    (jumpsIncluded : ∀ scope kind, jumpControlFlow scope kind ∈ jumps → jumpControlFlow scope kind ∈ second)
    (tail : ∀ value, resultControlFlow value ∈ first → ControlFlowAction activation second secondResult (next value)) :
    ControlFlowAction activation second secondResult (action >>= next) := by
  constructor
  · intro before bounded
    have reached := head.outcome before bounded
    have framed := head.frame before bounded
    cases evaluated : action before with
    | ok value middle =>
        simp only [evaluated, ControlFlowOutcome] at reached
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        have continued := (tail value reached).frame middle (framed.bounded bounded)
        cases finished : next value middle <;> simp only [finished] at continued
        all_goals simp only [bind, Bind.bind, evaluated, finished]
        all_goals change BreakStackFrame before _
        all_goals exact framed.trans continued
    | stop reason middle =>
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        simp only [bind, Bind.bind, evaluated]
        change BreakStackFrame before middle
        exact framed
    | escape address carriers middle =>
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        simp only [bind, Bind.bind, evaluated]
        change BreakStackFrame before middle
        exact framed
    | jump id kind middle =>
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        simp only [bind, Bind.bind, evaluated]
        change BreakStackFrame before middle
        exact framed
  · intro before bounded
    have reached := head.outcome before bounded
    have framed := head.frame before bounded
    cases evaluated : action before with
    | ok value middle =>
        simp only [evaluated, ControlFlowOutcome] at reached
        simp only [evaluated] at framed
        change BreakStackFrame before middle at framed
        have continued := (tail value reached).outcome middle (framed.bounded bounded)
        cases finished : next value middle with
        | ok result after => simpa only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome] using continued
        | stop reason after => simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
        | escape address carriers after => simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
        | jump id kind after =>
            simp only [finished, ControlFlowOutcome] at continued
            rcases continued with ⟨target, member, selected, compatible, equal, permitted⟩
            simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
            exact ⟨target, by simpa only [framed.stack] using member,
              by simpa only [framed.stack] using selected, compatible, equal, permitted⟩
    | stop reason middle => simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
    | escape address carriers middle => simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
    | jump id kind middle =>
        have iterationOutcome := iteration.outcome before bounded
        simp only [evaluated, ControlFlowOutcome] at iterationOutcome
        rcases iterationOutcome with ⟨target, member, selected, compatible, equal, permitted⟩
        simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
        exact ⟨target, member, selected, compatible, equal, jumpsIncluded _ _ permitted⟩

theorem controlFlow_map (allowed : List StaticFlow) (resultFlow : β → StaticFlow)
    (action : EvalM α) (transform : α → β)
    (body : ControlFlowAction activation allowed (fun value => resultFlow (transform value)) action) :
    ControlFlowAction activation allowed resultFlow (do pure (transform (← action))) := by
  apply controlFlow_dispatch allowed allowed _ _ action _ body
  · intro scope kind present
    exact present
  · intro value present
    exact controlFlow_pure allowed resultFlow (transform value) present

#print axioms controlFlow_dispatch
#print axioms controlFlow_loopDispatch
#print axioms controlFlow_map

end Goose.Proofs.ConstructionDelivery
