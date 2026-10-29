import Goose.Proofs.ConstructionGhostBlockProducerCore
import Goose.Proofs.ConstructionGhostProducerChannel

namespace Goose.Proofs.ConstructionGhostResultLocalProducer
open Goose.Construct Goose.Proofs.ConstructionGhostBlockProducerTransition

def resultLocalAction (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (planned selected : List Channel) (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) : EvalM (List Carrier) := do
  match selected with
  | [.construct destination] =>
      let .stored stored ← readLoc fuel config.layout ⟨← rootOf environment localVar, []⟩ | fault .shape
      let named ← match planned with
        | [.completion token] => prepareNamedCarrierAt origin token destination stored
        | _ => prepareNamedCarrier origin destination stored
      match named with
      | some carrier => pure [carrier]
      | none =>
          buildExpr fuel config environment destination (.resultLocal localVar origin)
          pure [Carrier.completed (← completedReceivingDestination destination)]
  | [] => let _ ← evalValue fuel config environment (.resultLocal localVar origin); pure []
  | [.register _] => pure [.register (← evalValue fuel config environment (.resultLocal localVar origin))]
  | _ => fault .arity

theorem resultLocalProducer_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    evalProduce (fuel + 1) config environment channels (.resultLocal localVar origin) before =
      (do let planned ← prepareBlockProducerChannels channels origin
          let selected ← planned.mapM (selectCompletionChannel environment (.resultLocal localVar origin))
          resultLocalAction fuel config environment planned selected localVar origin) before := by
  simp only [evalProduce, expressionOrigin, prepareBlockProducerChannels, resultLocalAction,
    Goose.Proofs.ConstructionGhostGlobalStep.evalM_bind_assoc]
  rfl

theorem resultLocalProducer_fallback (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels planned : List Channel) (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId)
    (before plannedState ready readState buildState : ExecutionState) (destination : Goose.Core.DestinationId) (stored : StoredValue)
    (prepared : prepareBlockProducerChannels channels origin before = .ok planned plannedState)
    (selected : planned.mapM (selectCompletionChannel environment (.resultLocal localVar origin)) plannedState = .ok [.construct destination] ready)
    (read : (rootOf environment localVar >>= fun root => readLoc fuel config.layout ⟨root, []⟩) ready = .ok (.stored stored) readState)
    (named : (match planned with
      | [.completion token] => prepareNamedCarrierAt origin token destination stored
      | _ => prepareNamedCarrier origin destination stored) readState = .ok none buildState) :
    evalProduce (fuel + 1) config environment channels (.resultLocal localVar origin) before =
      (do buildExpr fuel config environment destination (.resultLocal localVar origin)
          pure [Carrier.completed (← completedReceivingDestination destination)]) buildState := by
  rw [resultLocalProducer_source]
  simp only [bind, prepared, selected, resultLocalAction]
  simp only [bind] at read
  cases root : rootOf environment localVar ready <;> simp_all [bind, pure]
  rename_i location next
  cases loaded : readLoc fuel config.layout ⟨location, []⟩ next <;> simp_all [bind, pure]
  cases planned with
  | nil => simp_all [bind, pure]
  | cons first rest =>
      cases first <;> cases rest <;> simp_all [bind, pure]

#print axioms resultLocalProducer_fallback

#print axioms resultLocalProducer_source
end Goose.Proofs.ConstructionGhostResultLocalProducer
