import Goose.Proofs.ConstructionGhostSyntaxAggregateEvents

namespace Goose.Proofs.ConstructionGhostSyntaxAggregateEventsWitness
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostSyntaxAggregateEvents

private def context : Context := ⟨0, "source", [], [], []⟩
private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def implementation : Impl := ⟨"source", #[], #[], #[], .mk 0 [.expr bytes 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def operands : List Expr := [.call 0 [] 0, .call 0 [] 0]
private def expression : Expr := .arrLit (.arr .unit 2) operands 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem argumentsSyntax : ∀ id implementation start ready,
    getImplementation config 0 start = .ok (id, implementation) ready → ArgumentSyntax config implementation.params.toList [] := by
  intro id actualImplementation start ready lookup
  obtain ⟨actualContext, found, idEqual, implFound⟩ := implementation_lookup_source config 0 start ready id actualImplementation lookup
  have contextEq : actualContext = context := by simpa [config] using found.symm
  subst actualContext
  subst id
  have implEq : actualImplementation = implementation := by simpa [config, context] using implFound.symm
  subst actualImplementation
  exact .nil

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implFound
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implFound.symm
      subst actualImplementation
      refine ⟨0, [.expr bytes 0], none, rfl, ?_, .none⟩
      intro statement member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .expression bytes 0 (.bytes (.varr (.int .u8)) [65, 66] 0)
  | succ n => simp [config] at found

private theorem operandsSyntax : ∀ operand ∈ operands, ValueSyntax config operand := by
  intro operand member
  simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .channelCall 0 [] 0 argumentsSyntax

theorem aggregateEventChunks_nonempty : ∃ mapped visits chunks after,
    OperandReplay (evalValue 39 config environment) 0 operands [] .initial mapped visits ∧
    (∀ visit ∈ visits, SourceHistory config 39 [visit.ordinal] (.value environment visit.operand) visit.before visit.outcome) ∧
    visits.map Invocation.operand = operands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
    ChunksAlign visits chunks ∧ after.construction.events = chunks.flatten ∧
    evalValue 40 config environment expression .initial = .ok (.fixed #[.unit, .unit]) after ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0,
      .begin 1, .write 1 0, .write 1 1, .publish 1] := by
  have shape : ValueAggregate expression operands := .fixedArray (.arr .unit 2) operands 0 rfl
  obtain ⟨mapped, visits, chunks, replay, histories, ordered, once, aligned, finalEq⟩ :=
    aggregate_syntaxEventChunks 39 config closed environment [] expression operands .initial shape operandsSyntax
  let after := stepState (evalValue 40 config environment expression .initial)
  refine ⟨mapped, visits, chunks, after, replay, histories, ordered, once, aligned, ?_, ?_, ?_⟩
  · exact finalEq
  · unfold after stepState config context implementation environment expression operands bytes
    unfold evalValue
    cbv
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  · unfold after stepState config context implementation environment expression operands bytes
    unfold evalValue
    cbv
    unfold evalValue
    cbv
    unfold evalValue
    cbv

#print axioms aggregateEventChunks_nonempty
end Goose.Proofs.ConstructionGhostSyntaxAggregateEventsWitness
