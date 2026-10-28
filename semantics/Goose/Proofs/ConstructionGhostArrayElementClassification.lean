import Goose.Proofs.ConstructionGhostElementOccurrence

namespace Goose.Proofs.ConstructionGhostArrayElementClassification
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionGhostInvocationEvents
open Goose.Proofs.ConstructionGhostInvocationVisitEvents Goose.Proofs.ConstructionGhostDeclarationOnce
open Goose.Proofs.ConstructionGhostDeclarationArrayEvents Goose.Proofs.ConstructionGhostDeclarationFallback
open Goose.Proofs.ConstructionGhostElementOccurrence

def ElementVisitClassification (config : EvalConfig) (environment : RuntimeActivation) (parent : Goose.Core.DestinationId)
    (element : Ty) (fuel : Nat) (path : List Nat) (visit : Invocation Expr Unit) (final : ExecutionState) : Prop :=
  (∃ destination ready, ElementOccurrence config environment parent element visit.operand visit.before destination ready ∧
    (∀ other otherReady, ElementOccurrence config environment parent element visit.operand visit.before other otherReady →
      destination = other ∧ ready = otherReady) ∧
    match destination with
    | none => SourceHistory config fuel ((path ++ [visit.ordinal]) ++ [0]) (.value environment visit.operand) ready
        (evalValue fuel config environment visit.operand ready) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment visit.operand ready)).construction.events final.construction.events
    | some destination => SourceHistory config fuel ((path ++ [visit.ordinal]) ++ [0]) (.builder environment destination visit.operand) ready
        (buildExpr fuel config environment destination visit.operand ready) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination visit.operand ready)).construction.events final.construction.events) ∨
  ((∃ terminal : DeclarationTerminal, visit.outcome = terminal.step) ∧
    ¬ ∃ destination ready, ElementOccurrence config environment parent element visit.operand visit.before destination ready)

theorem array_elementClassifications (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (expressionOrigin origin : Goose.Core.OriginId)
    (before initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (occurrence : DeclarationOccurrence (fuel + 2) config environment localVar (.arrLit ty operands expressionOrigin)
      origin before (some incoming) initial)
    (renewed : liftConstruction expressionOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (found : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element)
    (supported : ∀ operand ∈ operands, FuelSupport config (fuel + 1) (.element environment current element operand)) :
    ∃ outcome visits,
      OperandReplay (fun operand => buildElement (fuel + 1) config environment current element operand) 0 operands [] ready outcome visits ∧
      visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      ∀ visit ∈ visits, ElementVisitClassification config environment current element fuel (path ++ [0]) visit
        (Goose.Proofs.Exit.stepState (execStmt (fuel + 3) config environment (.letS localVar (.arrLit ty operands expressionOrigin) origin) before)) := by
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
  have actual := visit_executes replay visit member
  have history := histories visit member
  rw [← actual] at history
  have classification := element_history_or_earlyTerminal fuel config environment current element visit.operand visit.before
    ((path ++ [0]) ++ [visit.ordinal]) history
  rcases classification with ⟨destination, sourceReady, source, unique, child⟩ | early
  · left
    refine ⟨destination, sourceReady, source, unique, ?_⟩
    cases destination with
    | none =>
        obtain ⟨childHistory, sourcePrefix⟩ := child
        rw [actual] at sourcePrefix
        exact ⟨childHistory, eventPrefix_trans _ _ _ sourcePrefix
          (eventPrefix_trans _ _ _ (invocationEvents_visitPrefix segments visit member) loopToFinal)⟩
    | some destination =>
        obtain ⟨childHistory, sourcePrefix⟩ := child
        rw [actual] at sourcePrefix
        exact ⟨childHistory, eventPrefix_trans _ _ _ sourcePrefix
          (eventPrefix_trans _ _ _ (invocationEvents_visitPrefix segments visit member) loopToFinal)⟩
  · right
    obtain ⟨⟨terminal, terminalEq⟩, noSource⟩ := early
    exact ⟨⟨terminal, actual.symm.trans terminalEq⟩, noSource⟩

#print axioms array_elementClassifications
end Goose.Proofs.ConstructionGhostArrayElementClassification
