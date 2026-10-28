import Goose.Proofs.ConstructionExecutionProtocolLifecycle

namespace Goose.Proofs.ConstructionRunTraceDiscipline
open Goose.Construct Goose.Core

def terminalBudget : DestinationTracePhase → Nat
  | .unseen | .live _ _ => 1
  | .published | .abandoned => 0

private theorem terminal_step_budget {phase next : DestinationTracePhase} {observation : DestinationObservation}
    (accepted : destinationTraceStep phase observation = some next) :
    (if observation = .publish then 1 else 0) + (if observation = .abandon then 1 else 0) + terminalBudget next ≤ terminalBudget phase := by
  cases phase with
  | live staged wrote =>
    cases staged <;> cases wrote <;> cases observation <;> cases next <;>
      simp_all [destinationTraceStep, terminalBudget]
  | unseen | published | abandoned =>
    cases observation <;> cases next <;> simp_all [destinationTraceStep, terminalBudget]

private theorem terminal_observations_budget {phase final : DestinationTracePhase} {observations : List DestinationObservation}
    (accepted : runDestinationObservations phase observations = some final) :
    observations.count .publish + observations.count .abandon + terminalBudget final ≤ terminalBudget phase := by
  induction observations generalizing phase with
  | nil =>
    simp only [runDestinationObservations, Option.some.injEq] at accepted
    subst final
    simp
  | cons observation rest ih =>
    simp only [runDestinationObservations] at accepted
    cases step : destinationTraceStep phase observation with
    | none => simp [step] at accepted
    | some next =>
      have tail := ih (by simpa [step] using accepted)
      have head := terminal_step_budget step
      by_cases published : observation = .publish
      · subst observation
        simp [List.count_cons] at *
        omega
      · by_cases abandoned : observation = .abandon
        · subst observation
          simp [List.count_cons, published, Ne.symm published] at *
          omega
        · simp [List.count_cons, published, Ne.symm published, abandoned, Ne.symm abandoned] at *
          omega

theorem observations_no_stage_after_write {phase final : DestinationTracePhase}
    {before after : List DestinationObservation} {index : Nat}
    (accepted : runDestinationObservations phase (before ++ .write index :: after) = some final) :
    .stage ∉ after := by
  rw [runDestinationObservations_append] at accepted
  cases prior : runDestinationObservations phase before with
  | none => simp [prior] at accepted
  | some middle =>
    have tail : runDestinationObservations middle (.write index :: after) = some final := by
      simpa [prior] using accepted
    cases middle with
    | unseen | published | abandoned => simp [runDestinationObservations, destinationTraceStep] at tail
    | live staged wrote =>
      simp only [runDestinationObservations, destinationTraceStep, Option.bind_some] at tail
      have budget := runDestinationObservations_stage_budget tail
      simp only [DestinationTracePhase.stageBudget] at budget
      exact List.count_eq_zero.mp (by omega)

theorem runModule_trace_discipline (fuel : Nat) (config : EvalConfig) (id : DestinationId) :
    let events := (Goose.Proofs.Exit.stepState (runModule fuel config .initial)).construction.events
    ∃ phase, runDestinationTrace id .unseen events = some phase ∧
      (destinationObservations id events).count .begin ≤ 1 ∧
      (destinationObservations id events).count .stage ≤ 1 ∧
      (destinationObservations id events).count .publish + (destinationObservations id events).count .abandon ≤ 1 ∧
      ∀ before after index, destinationObservations id events = before ++ .write index :: after → .stage ∉ after := by
  let state := (Goose.Proofs.Exit.stepState (runModule fuel config .initial)).construction
  have protocol := Goose.Proofs.ConstructionExecutionProtocol.runModule_destination_trace_protocol fuel config id
  change match state.destinations[id]? with
    | none => runDestinationTrace id .unseen state.events = some .unseen
    | some destination => ∃ phase, runDestinationTrace id .unseen state.events = some phase ∧ phase.matchesDestination destination at protocol
  have accepted : ∃ phase, runDestinationTrace id .unseen state.events = some phase := by
    cases present : state.destinations[id]? with
    | none => exact ⟨.unseen, by simpa only [present] using protocol⟩
    | some row =>
      obtain ⟨phase, trace, compatible⟩ := by simpa only [present] using protocol
      exact ⟨phase, trace⟩
  obtain ⟨phase, trace⟩ := accepted
  refine ⟨phase, trace, runDestinationTrace_begin_once trace, runDestinationTrace_stage_once trace, ?_, ?_⟩
  · change (destinationObservations id state.events).count .publish +
      (destinationObservations id state.events).count .abandon ≤ 1
    have budget := terminal_observations_budget trace
    simp only [terminalBudget] at budget
    omega
  · intro before after index shape
    change destinationObservations id state.events = before ++ .write index :: after at shape
    have trace' : runDestinationObservations .unseen (destinationObservations id state.events) = some phase := trace
    rw [shape] at trace'
    exact observations_no_stage_after_write trace'

#print axioms observations_no_stage_after_write
#print axioms runModule_trace_discipline

end Goose.Proofs.ConstructionRunTraceDiscipline
