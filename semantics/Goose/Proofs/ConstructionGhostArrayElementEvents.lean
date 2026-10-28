import Goose.Proofs.ConstructionGhostDeclarationArrayEvents
import Goose.Proofs.ConstructionGhostInvocationVisitEvents

namespace Goose.Proofs.ConstructionGhostArrayElementEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocationEvents
open Goose.Proofs.ConstructionGhostInvocationVisitEvents Goose.Proofs.ConstructionGhostElements
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationArrayEvents
open Goose.Proofs.ConstructionGhostInvocation

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

def elementSyntax : SourceOperation α → Option (RuntimeActivation × Goose.Core.DestinationId × Ty × Expr)
  | .element environment parent element operand => some (environment, parent, element, operand)
  | _ => none

theorem fixedElement_child_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : elementSyntax operation = some (environment, parent, element, operand))
    (fixed : element.nonfixed = false) :
    SourceHistory config sourceFuel (path ++ [0]) (.value environment operand) before (evalValue sourceFuel config environment operand before) := by
  cases history <;> simp_all [elementSyntax]
  case fixedElement =>
    rename_i child
    have actual := child.sound
    simp only [execute] at actual
    rw [actual]
    exact child

theorem nonfixedElement_child_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : elementSyntax operation = some (environment, parent, element, operand))
    (nonfixed : element.nonfixed = true) (layout : ReceivingLayout) (layoutReady ready : ExecutionState)
    (destination : Goose.Core.DestinationId)
    (layoutResult : receivingLayout config.layout element before = .ok layout layoutReady)
    (opened : receivingAction (expressionOrigin operand) parent (fun current => openChild current element layout) layoutReady =
      .ok destination ready) :
    SourceHistory config sourceFuel (path ++ [0]) (.builder environment destination operand) ready
      (buildExpr sourceFuel config environment destination operand ready) := by
  cases history <;> simp_all [elementSyntax]

theorem nonfixedElement_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (before layoutReady ready : ExecutionState)
    (layout : ReceivingLayout) (destination : Goose.Core.DestinationId) (nonfixed : element.nonfixed = true)
    (layoutResult : receivingLayout config.layout element before = .ok layout layoutReady)
    (opened : receivingAction (expressionOrigin operand) parent (fun current => openChild current element layout) layoutReady =
      .ok destination ready) :
    EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination operand ready)).construction.events
      (Goose.Proofs.Exit.stepState (buildElement (fuel + 1) config environment parent element operand before)).construction.events := by
  simp only [buildElement, nonfixed, ↓reduceIte, bind, layoutResult, opened]
  cases source : buildExpr fuel config environment destination operand ready with
  | ok unit state =>
      cases unit
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have preserved : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (do let completed ← completedReceivingDestination destination
              receivingAction (expressionOrigin operand) parent (fun parent => attachChild parent completed)) := by
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedReceivingDestination destination)
        · intro completed; kernel_protocol
      simpa [source, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant, bind] using preserved state List.prefix_rfl
  | stop | escape | jump => simp [source, Goose.Proofs.Exit.stepState, eventPrefix_refl]

#print axioms nonfixedElement_child_history
#print axioms nonfixedElement_sourcePrefix

theorem fixedElement_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) (before : ExecutionState)
    (fixed : element.nonfixed = false) :
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand before)).construction.events
      (Goose.Proofs.Exit.stepState (buildElement (fuel + 1) config environment parent element operand before)).construction.events := by
  rw [fixedElement_execution fuel config environment parent element operand before fixed]
  cases source : evalValue fuel config environment operand before with
  | ok value state =>
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have preserved : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (do let bytes ← liftExcept (fixedBytes fuel config.layout element value)
              receivingAction (expressionOrigin operand) parent (fun parent => writeElement parent bytes)) := by
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftExcept _)
        · intro bytes; kernel_protocol
      simpa [fixedElementContinuation, source, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using preserved state List.prefix_rfl
  | stop | escape | jump => simp [fixedElementContinuation, source, Goose.Proofs.Exit.stepState, eventPrefix_refl]

theorem array_fixedOperandEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (expressionOrigin origin : Goose.Core.OriginId)
    (before initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (occurrence : DeclarationOccurrence (fuel + 2) config environment localVar (.arrLit ty operands expressionOrigin)
      origin before (some incoming) initial)
    (renewed : liftConstruction expressionOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (found : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element) (fixed : element.nonfixed = false)
    (supported : ∀ operand ∈ operands, FuelSupport config (fuel + 1) (.element environment current element operand)) :
    ∃ outcome visits,
      OperandReplay (fun operand => buildElement (fuel + 1) config environment current element operand) 0 operands [] ready outcome visits ∧
      visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      ∀ visit ∈ visits,
        SourceHistory config fuel (((path ++ [0]) ++ [visit.ordinal]) ++ [0])
          (.value environment visit.operand) visit.before (evalValue fuel config environment visit.operand visit.before) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment visit.operand visit.before)).construction.events
          (Goose.Proofs.Exit.stepState (execStmt (fuel + 3) config environment (.letS localVar (.arrLit ty operands expressionOrigin) origin) before)).construction.events := by
  obtain ⟨outcome, visits, chunks, continuation, replay, histories, ordered, once, aligned, chunksEq, finalEq⟩ :=
    array_declaration_sourceEvents (fuel + 1) config environment path localVar incoming current ty operands expressionOrigin origin
      before initial prepared ready pending element occurrence renewed found elementFound supported
  have loopToFinal : EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 3) config environment (.letS localVar (.arrLit ty operands expressionOrigin) origin) before)).construction.events := by
    refine ⟨continuation, ?_⟩
    rw [chunksEq]
    exact finalEq
  have segments := replay_invocationEvents replay
    (fun operand => (evaluation_keepsEventPrefix (fuel + 1) config).element environment current element operand)
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  intro visit member
  have history := histories visit member
  have child := fixedElement_child_history history fuel environment current element visit.operand rfl rfl fixed
  have sourcePrefix := fixedElement_sourcePrefix fuel config environment current element visit.operand visit.before fixed
  rw [visit_executes replay visit member] at sourcePrefix
  exact ⟨child, eventPrefix_trans _ _ _ sourcePrefix (eventPrefix_trans _ _ _ (invocationEvents_visitPrefix segments visit member) loopToFinal)⟩

theorem array_nonfixedOperandEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (expressionOrigin origin : Goose.Core.OriginId)
    (before initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (occurrence : DeclarationOccurrence (fuel + 2) config environment localVar (.arrLit ty operands expressionOrigin)
      origin before (some incoming) initial)
    (renewed : liftConstruction expressionOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (found : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element) (nonfixed : element.nonfixed = true)
    (supported : ∀ operand ∈ operands, FuelSupport config (fuel + 1) (.element environment current element operand)) :
    ∃ outcome visits,
      OperandReplay (fun operand => buildElement (fuel + 1) config environment current element operand) 0 operands [] ready outcome visits ∧
      visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      ∀ visit ∈ visits, ∀ layout layoutReady childReady destination,
        receivingLayout config.layout element visit.before = .ok layout layoutReady →
        receivingAction (Goose.Construct.expressionOrigin visit.operand) current (fun parent => openChild parent element layout) layoutReady = .ok destination childReady →
        SourceHistory config fuel (((path ++ [0]) ++ [visit.ordinal]) ++ [0])
          (.builder environment destination visit.operand) childReady (buildExpr fuel config environment destination visit.operand childReady) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination visit.operand childReady)).construction.events
          (Goose.Proofs.Exit.stepState (execStmt (fuel + 3) config environment (.letS localVar (.arrLit ty operands expressionOrigin) origin) before)).construction.events := by
  obtain ⟨outcome, visits, chunks, continuation, replay, histories, ordered, once, aligned, chunksEq, finalEq⟩ :=
    array_declaration_sourceEvents (fuel + 1) config environment path localVar incoming current ty operands expressionOrigin origin
      before initial prepared ready pending element occurrence renewed found elementFound supported
  have loopToFinal : EventPrefix (Goose.Proofs.Exit.stepState outcome).construction.events
      (Goose.Proofs.Exit.stepState (execStmt (fuel + 3) config environment (.letS localVar (.arrLit ty operands expressionOrigin) origin) before)).construction.events := by
    refine ⟨continuation, ?_⟩
    rw [chunksEq]
    exact finalEq
  have segments := replay_invocationEvents replay
    (fun operand => (evaluation_keepsEventPrefix (fuel + 1) config).element environment current element operand)
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  intro visit member layout layoutReady childReady destination layoutResult opened
  have history := histories visit member
  have child := nonfixedElement_child_history history fuel environment current element visit.operand rfl rfl nonfixed
    layout layoutReady childReady destination layoutResult opened
  have sourcePrefix := nonfixedElement_sourcePrefix fuel config environment current element visit.operand visit.before layoutReady childReady
    layout destination nonfixed layoutResult opened
  rw [visit_executes replay visit member] at sourcePrefix
  exact ⟨child, eventPrefix_trans _ _ _ sourcePrefix (eventPrefix_trans _ _ _ (invocationEvents_visitPrefix segments visit member) loopToFinal)⟩

#print axioms array_nonfixedOperandEvents
#print axioms array_fixedOperandEvents
#print axioms fixedElement_child_history
#print axioms fixedElement_sourcePrefix
end Goose.Proofs.ConstructionGhostArrayElementEvents
