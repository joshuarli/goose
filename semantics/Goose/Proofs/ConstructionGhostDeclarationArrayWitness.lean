import Goose.Proofs.ConstructionGhostDeclarationArrayEvents

namespace Goose.Proofs.ConstructionGhostDeclarationArrayWitness
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostDeclarationOnce
open Goose.Proofs.ConstructionGhostDeclarationArrayEvents

private def element : Ty := .int .u8
private def descriptor : LocalVar := ⟨"bytes", .varr element, .immutable, 0, 0⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[descriptor], .mk 0 [] none, .unknown⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[], 0, #[], #[], #[]⟩⟩
private def operands : List Expr := [.lit .u8 65, .lit .u8 66]
private def expression : Expr := .arrLit (.varr element) operands 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def initial : ExecutionState := stepState (newDestination config.layout 4 descriptor.ty .value 0 none
  (producerCount? ⟨config.module, environment.vars⟩ expression) .initial)
private def prepared : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 0) initial)
private def ready : ExecutionState := stepState (getDestination 0 prepared)
private def pending : PendingDestination := (prepared.construction.destinations[0]?).get (by
  simp only [prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands]
  cbv)

theorem byteArray_declarationEvents : ∃ outcome visits chunks continuation,
    OperandReplay (fun operand => buildElement 38 config environment 0 element operand) 0 operands [] ready outcome visits ∧
    (∀ visit ∈ visits, SourceHistory config 38 [4, 0, 0, visit.ordinal]
      (.element environment 0 element visit.operand) visit.before visit.outcome) ∧
    (visits.map Invocation.ordinal).Nodup ∧ ChunksAlign visits chunks ∧
    chunks.flatten = [.write 0 0, .write 0 1] ∧
    (Goose.Proofs.Exit.stepState (execStmt 40 config environment (.letS 0 expression 0) .initial)).construction.events =
      ready.construction.events ++ chunks.flatten ++ continuation := by
  have occurrence : DeclarationOccurrence 39 config environment 0 expression 0 .initial (some 0) initial := by
    apply DeclarationOccurrence.direct descriptor (.local 4 1 0) .initial implementation .initial 0 initial
    all_goals first | exact DeclarationFallback.absent _ rfl | skip
    all_goals simp only [config, implementation, environment, descriptor, element, expression, operands, initial, stepState]
    all_goals cbv
  have renewed : liftConstruction 0 (renewReceivingDestination 0) initial = .ok 0 prepared := by
    simp only [prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands]
    cbv
  have found : getDestination 0 prepared = .ok pending ready := by
    simp only [ready, pending, prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands]
    cbv
  have elementFound : elementType pending.capability.logicalType = some element := by
    simp only [pending, prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands]
    cbv
  have supported : ∀ operand ∈ operands, FuelSupport config 38 (.element environment 0 element operand) := by
    intro operand member
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      exact .legacy 38 (.fixedElement environment 0 element _ rfl (.value environment (.integer .u8 _)))
  obtain ⟨outcome, visits, chunks, continuation, replay, histories, ordered, once, aligned, chunksEq, finalEq⟩ :=
    array_declaration_sourceEvents 38 config environment [4, 0] 0 0 0 (.varr element) operands 0 0
      .initial initial prepared ready pending element occurrence renewed found elementFound supported
  have loopResult : ∃ after, outcome = .ok [(), ()] after ∧ after.construction.events = ready.construction.events ++ [.write 0 0, .write 0 1] := by
    have actual := replay.execute
    let after := stepState (List.mapM.loop (fun operand => buildElement 38 config environment 0 element operand) operands [] ready)
    have result : List.mapM.loop (fun operand => buildElement 38 config environment 0 element operand) operands [] ready = .ok [(), ()] after := by
      simp only [after, stepState, ready, pending, prepared, initial, config, implementation, environment, descriptor, element, expression, operands]
      cbv
    refine ⟨after, actual.symm.trans result, ?_⟩
    simp only [after, stepState, ready, pending, prepared, initial, config, implementation, environment, descriptor, element, expression, operands]
    cbv
  obtain ⟨after, outcomeEq, events⟩ := loopResult
  rw [outcomeEq] at chunksEq
  have chunksActual : chunks.flatten = [.write 0 0, .write 0 1] := by
    apply (List.append_right_inj ready.construction.events).mp
    exact chunksEq.symm.trans events
  refine ⟨outcome, visits, chunks, continuation, replay, ?_, once, aligned, chunksActual, ?_⟩
  · simpa using histories
  · exact finalEq

#print axioms byteArray_declarationEvents
end Goose.Proofs.ConstructionGhostDeclarationArrayWitness
