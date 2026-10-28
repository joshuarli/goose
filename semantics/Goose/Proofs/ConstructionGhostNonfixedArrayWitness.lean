import Goose.Proofs.ConstructionGhostArrayElementEvents
import Goose.Proofs.ConstructionGhostReplayDeterminism

namespace Goose.Proofs.ConstructionGhostNonfixedArrayWitness
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostArrayElementEvents
open Goose.Proofs.ConstructionGhostReplayDeterminism

private def element : Ty := .varr (.int .u8)
private def descriptor : LocalVar := ⟨"nested", .varr element, .immutable, 0, 0⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[descriptor], .mk 0 [] none, .unknown⟩
private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[], 0, #[], #[], #[]⟩⟩
private def operand : Expr := .bytes element [65, 66] 0
private def operands : List Expr := [operand]
private def expression : Expr := .arrLit (.varr element) operands 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state
private def initial : ExecutionState := stepState (newDestination config.layout 4 descriptor.ty .value 0 none
  (producerCount? ⟨config.module, environment.vars⟩ expression) .initial)
private def prepared : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 0) initial)
private def ready : ExecutionState := stepState (getDestination 0 prepared)
private def pending : PendingDestination := (prepared.construction.destinations[0]?).get (by
  simp only [prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands, operand]
  cbv)
private def layout : ReceivingLayout := match receivingLayout config.layout element ready with
  | .ok value _ => value
  | _ => .packed
private def layoutReady : ExecutionState := stepState (receivingLayout config.layout element ready)
private def childReady : ExecutionState := stepState (receivingAction 0 0 (fun parent => openChild parent element layout) layoutReady)
private def elementAfter : ExecutionState := stepState (buildElement 39 config environment 0 element operand ready)

theorem nonfixedArray_childEvents :
    SourceHistory config 38 [4, 0, 0, 0, 0] (.builder environment 1 operand) childReady
      (buildExpr 38 config environment 1 operand childReady) ∧
    (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 1 operand childReady)).construction.events =
      childReady.construction.events ++ [.write 1 0, .write 1 1] ∧
    EventPrefix (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 1 operand childReady)).construction.events
      (Goose.Proofs.Exit.stepState (execStmt 41 config environment (.letS 0 expression 0) .initial)).construction.events := by
  have occurrence : DeclarationOccurrence 40 config environment 0 expression 0 .initial (some 0) initial := by
    apply DeclarationOccurrence.direct descriptor (.local 4 1 0) .initial implementation .initial 0 initial
    all_goals first | exact DeclarationFallback.absent _ rfl | skip
    all_goals simp only [config, implementation, environment, descriptor, element, expression, operands, operand, initial, stepState]
    all_goals cbv
  have renewed : liftConstruction 0 (renewReceivingDestination 0) initial = .ok 0 prepared := by
    simp only [prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands, operand]
    cbv
  have found : getDestination 0 prepared = .ok pending ready := by
    simp only [ready, pending, prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands, operand]
    cbv
  have elementFound : elementType pending.capability.logicalType = some element := by
    simp only [pending, prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands, operand]
    cbv
  have supported : ∀ child ∈ operands, FuelSupport config 39 (.element environment 0 element child) := by
    intro child member
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    subst child
    exact .legacy 39 (.nonfixedElement environment 0 element operand rfl
      (fun destination => .builderBytes environment destination element [65, 66] 0))
  obtain ⟨outcome, visits, replay, ordered, once, children⟩ :=
    array_nonfixedOperandEvents 38 config environment [4, 0] 0 0 0 (.varr element) operands 0 0
      .initial initial prepared ready pending element occurrence renewed found elementFound rfl supported
  have elementResult : buildElement 39 config environment 0 element operand ready = .ok () elementAfter := by
    simp only [elementAfter, stepState, ready, pending, prepared, initial, config, implementation, environment, descriptor, element, expression, operands, operand]
    cbv
  let visit : Invocation Expr Unit := ⟨0, operand, ready, .ok () elementAfter⟩
  have knownReplay : OperandReplay (fun child => buildElement 39 config environment 0 element child)
      0 operands [] ready (.ok [()] elementAfter) [visit] := .next elementResult (.done 1 [()] elementAfter)
  have same := operandReplay_deterministic replay knownReplay
  have visitsEq : visits = [visit] := same.2
  have member : visit ∈ visits := by rw [visitsEq]; simp
  have layoutResult : receivingLayout config.layout element ready = .ok layout layoutReady := by
    simp only [layout, layoutReady, ready, pending, prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands, operand]
    cbv
  have opened : receivingAction (expressionOrigin operand) 0 (fun parent => openChild parent element layout) layoutReady = .ok 1 childReady := by
    simp only [childReady, layout, layoutReady, ready, pending, prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands, operand]
    cbv
  obtain ⟨history, retained⟩ := children visit member layout layoutReady childReady 1 layoutResult opened
  have events : (Goose.Proofs.Exit.stepState (buildExpr 38 config environment 1 operand childReady)).construction.events =
      childReady.construction.events ++ [.write 1 0, .write 1 1] := by
    simp only [childReady, layout, layoutReady, ready, pending, prepared, initial, stepState, config, implementation, environment, descriptor, element, expression, operands, operand]
    cbv
  exact ⟨history, events, retained⟩

theorem nonfixedArray_succeeds :
    execStmt 41 config environment (.letS 0 expression 0) .initial =
      .ok (.normal .unit) (stepState (execStmt 41 config environment (.letS 0 expression 0) .initial)) := by
  simp only [stepState, config, implementation, environment, descriptor, element, expression, operands, operand]
  cbv

#print axioms nonfixedArray_succeeds
#print axioms nonfixedArray_childEvents
end Goose.Proofs.ConstructionGhostNonfixedArrayWitness
