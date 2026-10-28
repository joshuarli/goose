import Goose.Proofs.ConstructionGhostSourceMutual

namespace Goose.Proofs.ConstructionGhostSourceAggregate
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation

def aggregateResult (expression : Expr) : ExecutionStep (List Value) → ExecutionStep Value
  | .ok values state => match expression with
      | .arrLit _ _ _ => .ok (.fixed values.toArray) state
      | .structLit (.structT id _) _ => .ok (.record id values.toArray) state
      | _ => .stop (.fault .shape) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem aggregate_replay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (expression : Expr) (operands : List Expr) (before : ExecutionState)
    (shape : ValueAggregate expression operands)
    (supported : ∀ operand ∈ operands, SupportedOperation config (.value environment operand)) :
    ∃ mapped visits,
      OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits ∧
      (∀ visit ∈ visits, SourceHistory config fuel (path ++ [visit.ordinal])
        (.value environment visit.operand) visit.before visit.outcome) ∧
      visits.map Invocation.operand = operands.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      evalValue (fuel + 1) config environment expression before = aggregateResult expression mapped ∧
      SourceHistory config (fuel + 1) path (.value environment expression) before
        (evalValue (fuel + 1) config environment expression before) := by
  have execution : ∃ mapped visits,
      OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits ∧
      evalValue (fuel + 1) config environment expression before = aggregateResult expression mapped := by
    cases shape with
    | fixedArray ty operands origin fixed =>
        obtain ⟨mapped, visits, replay, source⟩ := fixedArray_replay fuel config environment ty operands origin before fixed
        exact ⟨mapped, visits, replay, by cases mapped <;> simpa [aggregateResult] using source⟩
    | record id fields operands =>
        obtain ⟨mapped, visits, replay, source⟩ := structLiteral_replay fuel config environment id fields operands before
        exact ⟨mapped, visits, replay, by cases mapped <;> simpa [aggregateResult] using source⟩
  obtain ⟨mapped, visits, replay, execution⟩ := execution
  refine ⟨mapped, visits, replay, ?_, replay.sourceOrder, replay.once, execution,
    history_exists (fuel + 1) config _ path before (.aggregate environment expression operands shape supported)⟩
  intro visit member
  have mappedMember : visit.operand ∈ visits.map Invocation.operand := List.mem_map_of_mem member
  rw [replay.sourceOrder] at mappedMember
  have operandMember : visit.operand ∈ operands := List.mem_of_mem_take mappedMember
  have child := history_exists fuel config (.value environment visit.operand) (path ++ [visit.ordinal]) visit.before
    (supported visit.operand operandMember)
  simp only [execute] at child
  rw [← visit_executes replay visit member]
  exact child

private def witnessContext : Context := ⟨0, "source", [], [], []⟩
private def witnessImplementation : Impl := ⟨"source", #[], #[], #[], .mk 0 [.print [.text "x"] 0] none, .unknown⟩
private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[witnessImplementation], #[witnessContext], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessOperands : List Expr := [.call 0 [] 0, .call 0 [] 0]
private def witnessExpression : Expr := .arrLit (.arr .unit 2) witnessOperands 0
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem witness_supported : ∀ operand ∈ witnessOperands,
    SupportedOperation witnessConfig (.value witnessEnvironment operand) := by
  intro operand member
  simp only [witnessOperands, List.mem_cons, List.not_mem_nil, or_false] at member
  have body : ∀ environment, SupportedOperation witnessConfig (.statements environment [.print [.text "x"] 0]) := by
    intro environment
    exact .sequence environment (.printText environment "x" 0) (.empty environment)
  have callee : SupportedOperation witnessConfig (.call witnessEnvironment 0 0) := by
    apply SupportedOperation.call witnessEnvironment 0 0 witnessContext witnessImplementation
    · rfl
    · rfl
    · rfl
    · rfl
    · intro act
      exact .activation _ 0 _ 0 body
  rcases member with rfl | rfl <;>
    exact .valueCall witnessEnvironment 0 0 witnessContext witnessImplementation rfl rfl rfl callee

theorem witness_aggregateSourceOrder : ∃ mapped visits state,
    OperandReplay (evalValue 39 witnessConfig witnessEnvironment) 0 witnessOperands [] .initial mapped visits ∧
    (∀ visit ∈ visits, SourceHistory witnessConfig 39 [visit.ordinal] (.value witnessEnvironment visit.operand)
      visit.before visit.outcome) ∧
    visits.map Invocation.operand = witnessOperands.take visits.length ∧ (visits.map Invocation.ordinal).Nodup ∧
    evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial = .ok (.fixed #[.unit, .unit]) state ∧
    state.construction.stdout.data.toList = [120, 10, 120, 10] := by
  have shape : ValueAggregate witnessExpression witnessOperands := .fixedArray (.arr .unit 2) witnessOperands 0 rfl
  obtain ⟨mapped, visits, replay, children, ordered, once, execution, history⟩ :=
    aggregate_replay 39 witnessConfig witnessEnvironment [] witnessExpression witnessOperands .initial shape witness_supported
  refine ⟨mapped, visits, witnessState (evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial),
    replay, children, ordered, once, ?_, ?_⟩ <;>
    unfold witnessState witnessConfig witnessEnvironment witnessContext witnessImplementation witnessExpression witnessOperands <;> cbv

#print axioms witness_aggregateSourceOrder

#print axioms aggregate_replay
end Goose.Proofs.ConstructionGhostSourceAggregate
