import Goose.Proofs.ConstructionGhostArrayElementEvents
import Goose.Proofs.ConstructionGhostBuilderCallEvents

namespace Goose.Proofs.ConstructionGhostArrayCallEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostArrayElementEvents
open Goose.Proofs.ConstructionGhostBuilderCallEvents

theorem array_constructedCallEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (expressionOrigin origin : Goose.Core.OriginId)
    (before initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (occurrence : DeclarationOccurrence (fuel + 3) config environment localVar (.arrLit ty operands expressionOrigin)
      origin before (some incoming) initial)
    (renewed : liftConstruction expressionOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (found : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element) (nonfixed : element.nonfixed = true)
    (supported : ∀ operand ∈ operands, FuelSupport config (fuel + 2) (.element environment current element operand)) :
    ∃ outcome visits,
      OperandReplay (fun operand => buildElement (fuel + 2) config environment current element operand) 0 operands [] ready outcome visits ∧
      visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
      ∀ visit ∈ visits, ∀ context arguments callOrigin layout layoutReady childReady child destination callReady,
        visit.operand = .call context arguments callOrigin →
        receivingLayout config.layout element visit.before = .ok layout layoutReady →
        receivingAction (Goose.Construct.expressionOrigin visit.operand) current (fun parent => openChild parent element layout) layoutReady = .ok child childReady →
        liftConstruction callOrigin (renewReceivingDestination child) childReady = .ok destination callReady →
        SourceHistory config fuel ((((path ++ [0]) ++ [visit.ordinal]) ++ [0]) ++ [0])
          (.channelCall environment context arguments [.construct destination] callOrigin) callReady
          (invokeCall fuel config environment context arguments [.construct destination] callOrigin callReady) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (invokeCall fuel config environment context arguments [.construct destination] callOrigin callReady)).construction.events
          (Goose.Proofs.Exit.stepState (execStmt (fuel + 4) config environment (.letS localVar (.arrLit ty operands expressionOrigin) origin) before)).construction.events := by
  obtain ⟨outcome, visits, replay, ordered, once, children⟩ :=
    array_nonfixedOperandEvents (fuel + 1) config environment path localVar incoming current ty operands expressionOrigin origin
      before initial prepared ready pending element occurrence renewed found elementFound nonfixed supported
  refine ⟨outcome, visits, replay, ordered, once, ?_⟩
  intro visit member context arguments callOrigin layout layoutReady childReady child destination callReady operandEq layoutResult opened callRenewed
  obtain ⟨builderHistory, builderPrefix⟩ := children visit member layout layoutReady childReady child layoutResult opened
  rw [operandEq] at builderHistory builderPrefix
  have callHistory := builderCall_child_history builderHistory fuel environment child destination context arguments callOrigin callReady rfl rfl callRenewed
  have callPrefix := builderCall_sourcePrefix fuel config environment child destination context arguments callOrigin childReady callReady callRenewed
  exact ⟨callHistory, eventPrefix_trans _ _ _ callPrefix builderPrefix⟩

#print axioms array_constructedCallEvents
end Goose.Proofs.ConstructionGhostArrayCallEvents
