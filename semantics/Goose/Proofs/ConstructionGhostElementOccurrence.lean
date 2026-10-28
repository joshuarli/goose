import Goose.Proofs.ConstructionGhostArrayElementEvents
import Goose.Proofs.ConstructionGhostDeclarationFallback

namespace Goose.Proofs.ConstructionGhostElementOccurrence
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostDeclarationFallback Goose.Proofs.ConstructionGhostArrayElementEvents

inductive ElementOccurrence (config : EvalConfig) (environment : RuntimeActivation) (parent : Goose.Core.DestinationId)
    (element : Ty) (operand : Expr) (before : ExecutionState) : Option Goose.Core.DestinationId → ExecutionState → Prop
  | fixed (fixed : element.nonfixed = false) : ElementOccurrence config environment parent element operand before none before
  | nonfixed (layout : ReceivingLayout) (layoutReady : ExecutionState) (destination : Goose.Core.DestinationId) (ready : ExecutionState)
      (nonfixed : element.nonfixed = true)
      (layoutResult : receivingLayout config.layout element before = .ok layout layoutReady)
      (opened : receivingAction (expressionOrigin operand) parent (fun current => openChild current element layout) layoutReady = .ok destination ready) :
      ElementOccurrence config environment parent element operand before (some destination) ready

theorem ElementOccurrence.unique {config : EvalConfig} {environment : RuntimeActivation} {parent : Goose.Core.DestinationId}
    {element : Ty} {operand : Expr} {before firstReady secondReady : ExecutionState} {first second : Option Goose.Core.DestinationId}
    (left : ElementOccurrence config environment parent element operand before first firstReady)
    (right : ElementOccurrence config environment parent element operand before second secondReady) :
    first = second ∧ firstReady = secondReady := by
  cases left <;> cases right <;> simp_all

theorem element_occurrence_or_terminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (before : ExecutionState) :
    (∃ destination ready, ElementOccurrence config environment parent element operand before destination ready) ∨
    (∃ terminal : DeclarationTerminal, buildElement (fuel + 1) config environment parent element operand before = terminal.step) := by
  cases nonfixed : element.nonfixed with
  | false => exact Or.inl ⟨none, before, .fixed nonfixed⟩
  | true =>
      cases layoutResult : receivingLayout config.layout element before with
      | stop reason state =>
          right
          refine ⟨.stopped reason state, ?_⟩
          simp [buildElement, nonfixed, bind, layoutResult, DeclarationTerminal.step]
      | escape address carriers state =>
          right
          refine ⟨.escaped address carriers state, ?_⟩
          simp [buildElement, nonfixed, bind, layoutResult, DeclarationTerminal.step]
      | jump target kind state =>
          right
          refine ⟨.jumped target kind state, ?_⟩
          simp [buildElement, nonfixed, bind, layoutResult, DeclarationTerminal.step]
      | ok layout layoutReady =>
          cases opened : receivingAction (expressionOrigin operand) parent (fun current => openChild current element layout) layoutReady with
          | ok destination ready => exact Or.inl ⟨some destination, ready, .nonfixed layout layoutReady destination ready nonfixed layoutResult opened⟩
          | stop reason state =>
              right
              refine ⟨.stopped reason state, ?_⟩
              simp [buildElement, nonfixed, bind, layoutResult, opened, DeclarationTerminal.step]
          | escape address carriers state =>
              right
              refine ⟨.escaped address carriers state, ?_⟩
              simp [buildElement, nonfixed, bind, layoutResult, opened, DeclarationTerminal.step]
          | jump target kind state =>
              right
              refine ⟨.jumped target kind state, ?_⟩
              simp [buildElement, nonfixed, bind, layoutResult, opened, DeclarationTerminal.step]

theorem ElementOccurrence.historyAndEvents {config : EvalConfig} {environment : RuntimeActivation} {parent : Goose.Core.DestinationId}
    {element : Ty} {operand : Expr} {before ready : ExecutionState} {destination : Option Goose.Core.DestinationId}
    {fuel : Nat} {path : List Nat}
    (occurrence : ElementOccurrence config environment parent element operand before destination ready)
    (history : SourceHistory config (fuel + 1) path (.element environment parent element operand) before
      (buildElement (fuel + 1) config environment parent element operand before)) :
    match destination with
    | none => SourceHistory config fuel (path ++ [0]) (.value environment operand) ready (evalValue fuel config environment operand ready) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand ready)).construction.events
          (Goose.Proofs.Exit.stepState (buildElement (fuel + 1) config environment parent element operand before)).construction.events
    | some destination => SourceHistory config fuel (path ++ [0]) (.builder environment destination operand) ready
        (buildExpr fuel config environment destination operand ready) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination operand ready)).construction.events
          (Goose.Proofs.Exit.stepState (buildElement (fuel + 1) config environment parent element operand before)).construction.events := by
  cases occurrence with
  | fixed fixed => exact ⟨fixedElement_child_history history fuel environment parent element operand rfl rfl fixed,
      fixedElement_sourcePrefix fuel config environment parent element operand before fixed⟩
  | nonfixed layout layoutReady destination ready nonfixed layoutResult opened =>
      exact ⟨nonfixedElement_child_history history fuel environment parent element operand rfl rfl nonfixed layout layoutReady ready destination layoutResult opened,
        nonfixedElement_sourcePrefix fuel config environment parent element operand before layoutReady ready layout destination nonfixed layoutResult opened⟩

theorem element_history_or_earlyTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (before : ExecutionState) (path : List Nat)
    (history : SourceHistory config (fuel + 1) path (.element environment parent element operand) before
      (buildElement (fuel + 1) config environment parent element operand before)) :
    (∃ destination ready, ElementOccurrence config environment parent element operand before destination ready ∧
      (∀ other otherReady, ElementOccurrence config environment parent element operand before other otherReady →
        destination = other ∧ ready = otherReady) ∧
      match destination with
      | none => SourceHistory config fuel (path ++ [0]) (.value environment operand) ready (evalValue fuel config environment operand ready) ∧
          EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand ready)).construction.events
            (Goose.Proofs.Exit.stepState (buildElement (fuel + 1) config environment parent element operand before)).construction.events
      | some destination => SourceHistory config fuel (path ++ [0]) (.builder environment destination operand) ready
          (buildExpr fuel config environment destination operand ready) ∧
          EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination operand ready)).construction.events
            (Goose.Proofs.Exit.stepState (buildElement (fuel + 1) config environment parent element operand before)).construction.events) ∨
    ((∃ terminal : DeclarationTerminal, buildElement (fuel + 1) config environment parent element operand before = terminal.step) ∧
      ¬ ∃ destination ready, ElementOccurrence config environment parent element operand before destination ready) := by
  classical
  by_cases reached : ∃ destination ready, ElementOccurrence config environment parent element operand before destination ready
  · obtain ⟨destination, ready, occurrence⟩ := reached
    left
    refine ⟨destination, ready, occurrence, ?_, ?_⟩
    · intro other otherReady otherOccurrence
      exact ElementOccurrence.unique occurrence otherOccurrence
    · have actual := ElementOccurrence.historyAndEvents occurrence history
      cases destination <;> exact actual
  · right
    refine ⟨?_, reached⟩
    rcases element_occurrence_or_terminal fuel config environment parent element operand before with occurrence | terminal
    · exact False.elim (reached occurrence)
    · exact terminal

#print axioms element_history_or_earlyTerminal
#print axioms ElementOccurrence.unique
#print axioms element_occurrence_or_terminal
#print axioms ElementOccurrence.historyAndEvents
end Goose.Proofs.ConstructionGhostElementOccurrence
