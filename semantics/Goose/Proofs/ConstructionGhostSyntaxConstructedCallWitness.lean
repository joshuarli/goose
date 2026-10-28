import Goose.Proofs.ConstructionGhostSyntaxTail
import Goose.Proofs.ConstructionGhostArrayCallEvents

namespace Goose.Proofs.ConstructionGhostSyntaxConstructedCallWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostSyntaxTail
open Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostArrayCallEvents

private def element : Ty := .varr (.int .u8)
private def bytes : Expr := .bytes element [65, 66] 0
private def operand : Expr := .call 1 [] 0
private def operands : List Expr := [operand, operand]
private def expression : Expr := .arrLit (.varr element) operands 0
private def statements : List Stmt := [.letS 0 expression 0]
private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def targetContext : Context := ⟨1, "target", [], [], []⟩
private def descriptor : LocalVar := ⟨"nested", .varr element, .immutable, 0, 0⟩
private def entryImplementation : Impl := ⟨"entry", #[], #[], #[descriptor],
  .mk 0 statements none, .unknown⟩
private def targetImplementation : Impl := ⟨"target", #[], #[⟨element, .value, none⟩], #[], .mk 1 [] (some bytes), .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[entryImplementation, targetImplementation], #[entryContext, targetContext], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem argumentsSyntax (contextId : Goose.Core.ContextId) : ∀ id actualImplementation start ready,
    getImplementation config contextId start = .ok (id, actualImplementation) ready →
    ArgumentSyntax config actualImplementation.params.toList [] := by
  intro id actualImplementation start ready lookup
  obtain ⟨actualContext, found, idEq, implemented⟩ := implementation_lookup_source config contextId start ready id actualImplementation lookup
  subst id
  cases contextId with
  | zero =>
      have contextEq : actualContext = entryContext := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = entryImplementation := by simpa [config, entryContext] using implemented.symm
      subst actualImplementation
      exact .nil
  | succ n =>
      cases n with
      | zero =>
          have contextEq : actualContext = targetContext := by simpa [config] using found.symm
          subst actualContext
          have implEq : actualImplementation = targetImplementation := by simpa [config, targetContext] using implemented.symm
          subst actualImplementation
          exact .nil
      | succ n => simp [config] at found

private theorem operandValues : ∀ value ∈ operands, ValueSyntax config value := by
  intro value member
  simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .channelCall 1 [] 0 (argumentsSyntax 1)

private theorem operandBuilders : ∀ value ∈ operands, DeclarationBuilderSyntax config value := by
  intro value member
  simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .channelCall 1 [] 0 (argumentsSyntax 1)

private theorem builder : DeclarationBuilderSyntax config expression := .array (.varr element) operands 0 operandValues operandBuilders
private theorem value : ValueSyntax config expression := .nonfixedArray (.varr element) operands 0 rfl builder

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation found implemented
  cases contextId with
  | zero =>
      have contextEq : actualContext = entryContext := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = entryImplementation := by simpa [config, entryContext] using implemented.symm
      subst actualImplementation
      refine ⟨0, statements, none, rfl, ?_, .none⟩
      intro statement member
      simp only [statements, List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .declaration 0 expression 0 value builder
  | succ n =>
      cases n with
      | zero =>
          have contextEq : actualContext = targetContext := by simpa [config] using found.symm
          subst actualContext
          have implEq : actualImplementation = targetImplementation := by simpa [config, targetContext] using implemented.symm
          subst actualImplementation
          exact ⟨1, [], some bytes, rfl, (by simp), .constructed bytes (.bytes _ _ _) (.bytes _ _ _) (.bytes _ _ _)⟩
      | succ n => simp [config] at found

theorem module_history (fuel : Nat) :
    runModule fuel config .initial = moduleChannelResult fuel config
      (channelsFor config.layout 0 entryImplementation.results.toList 0 .initial) ∧
    SourceHistory config fuel [] (.channelCall ⟨0, 0, #[], [], []⟩ 0 [] [] 0) .initial
      (invokeCall fuel config ⟨0, 0, #[], [], []⟩ 0 [] [] 0 .initial) := by
  obtain ⟨execution, history⟩ := moduleHistoryWithTails fuel config closed entryContext entryImplementation rfl rfl rfl (argumentsSyntax 0)
  exact ⟨execution, history [] .initial (by simp [channelsFor, config, entryImplementation, bind, pure])⟩

theorem module_constructedCalls :
    SourceHistory config 40 [] (.channelCall ⟨0, 0, #[], [], []⟩ 0 [] [] 0) .initial
      (invokeCall 40 config ⟨0, 0, #[], [], []⟩ 0 [] [] 0 .initial) ∧
    runModule 40 config .initial = .ok () (stepState (runModule 40 config .initial)) ∧
    (stepState (runModule 40 config .initial)).nextAct = 3 := by
  have history := (module_history 40).2
  refine ⟨history, ?_, ?_⟩
  · simp only [stepState, config, entryContext, targetContext, entryImplementation, targetImplementation,
      statements, expression, operands, operand, bytes, element]
    cbv
  · simp only [stepState, config, entryContext, targetContext, entryImplementation, targetImplementation,
      statements, expression, operands, operand, bytes, element]
    cbv

private def environment : RuntimeActivation := ⟨0, 4, #[descriptor], [(0, 1)], []⟩
private def initial : ExecutionState := stepState (newDestination config.layout 4 descriptor.ty .value 0 none
  (producerCount? ⟨config.module, environment.vars⟩ expression) .initial)
private def prepared : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 0) initial)
private def ready : ExecutionState := stepState (getDestination 0 prepared)
private def pending : PendingDestination := (prepared.construction.destinations[0]?).get (by
  simp only [prepared, initial, stepState, config, entryContext, targetContext, entryImplementation, targetImplementation,
    environment, descriptor, element, expression, operands, operand, bytes]
  cbv)
private def layout : ReceivingLayout := match receivingLayout config.layout element ready with
  | .ok value _ => value
  | _ => .packed
private def layoutReady : ExecutionState := stepState (receivingLayout config.layout element ready)
private def childReady : ExecutionState := stepState (receivingAction 0 0 (fun parent => openChild parent element layout) layoutReady)
private def callReady : ExecutionState := stepState (liftConstruction 0 (renewReceivingDestination 1) childReady)

private theorem replay_hasHead {action : Expr → EvalM Unit} {fuelOutcome : ExecutionStep (List Unit)}
    {visits : List (Invocation Expr Unit)} (replay : OperandReplay action 0 operands [] ready fuelOutcome visits) :
    ∃ visit ∈ visits, visit.ordinal = 0 ∧ visit.operand = operand ∧ visit.before = ready := by
  change OperandReplay action 0 (operand :: [operand]) [] ready fuelOutcome visits at replay
  cases replay <;> simp

theorem arrayCall_childEvents :
    SourceHistory config 36 [4, 0, 0, 0, 0, 0] (.channelCall environment 1 [] [.construct 1] 0) callReady
      (invokeCall 36 config environment 1 [] [.construct 1] 0 callReady) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (invokeCall 36 config environment 1 [] [.construct 1] 0 callReady)).construction.events
      (Goose.Proofs.Exit.stepState (execStmt 40 config environment (.letS 0 expression 0) .initial)).construction.events ∧
    (Goose.Proofs.Exit.stepState (invokeCall 36 config environment 1 [] [.construct 1] 0 callReady)).construction.events =
      callReady.construction.events ++ [.write 1 0, .write 1 1] := by
  have occurrence : DeclarationOccurrence 39 config environment 0 expression 0 .initial (some 0) initial := by
    apply DeclarationOccurrence.direct descriptor (.local 4 1 0) .initial entryImplementation .initial 0 initial
    all_goals first | exact DeclarationFallback.absent _ rfl | skip
    all_goals simp only [config, entryContext, targetContext, entryImplementation, targetImplementation,
      environment, descriptor, element, expression, operands, operand, bytes, initial, stepState]
    all_goals cbv
  have renewed : liftConstruction 0 (renewReceivingDestination 0) initial = .ok 0 prepared := by
    simp only [prepared, initial, stepState, config, entryContext, targetContext, entryImplementation, targetImplementation,
      environment, descriptor, element, expression, operands, operand, bytes]
    cbv
  have found : getDestination 0 prepared = .ok pending ready := by
    simp only [ready, pending, prepared, initial, stepState, config, entryContext, targetContext, entryImplementation, targetImplementation,
      environment, descriptor, element, expression, operands, operand, bytes]
    cbv
  have elementFound : elementType pending.capability.logicalType = some element := by
    simp only [pending, prepared, initial, stepState, config, entryContext, targetContext, entryImplementation, targetImplementation,
      environment, descriptor, element, expression, operands, operand, bytes]
    cbv
  have supported : ∀ child ∈ operands, FuelSupport config 38 (.element environment 0 element child) := by
    intro child member
    exact (syntaxFuel_existsWithTails 38 config closed).element environment 0 element child
      (operandValues child member) (operandBuilders child member)
  obtain ⟨outcome, visits, replay, ordered, once, children⟩ :=
    array_constructedCallEvents 36 config environment [4, 0] 0 0 0 (.varr element) operands 0 0
      .initial initial prepared ready pending element occurrence renewed found elementFound rfl supported
  obtain ⟨visit, member, ordinalEq, operandEq, beforeEq⟩ := replay_hasHead replay
  have layoutResult : receivingLayout config.layout element visit.before = .ok layout layoutReady := by
    rw [beforeEq]
    simp only [layout, layoutReady, ready, pending, prepared, initial, stepState, config, entryContext, targetContext,
      entryImplementation, targetImplementation, environment, descriptor, element, expression, operands, operand, bytes]
    cbv
  have opened : receivingAction (expressionOrigin visit.operand) 0 (fun parent => openChild parent element layout) layoutReady =
      .ok 1 childReady := by
    rw [operandEq]
    simp only [childReady, layout, layoutReady, ready, pending, prepared, initial, stepState, config, entryContext, targetContext,
      entryImplementation, targetImplementation, environment, descriptor, element, expression, operands, operand, bytes]
    cbv
  have callRenewed : liftConstruction 0 (renewReceivingDestination 1) childReady = .ok 1 callReady := by
    simp only [callReady, childReady, layout, layoutReady, ready, pending, prepared, initial, stepState, config, entryContext,
      targetContext, entryImplementation, targetImplementation, environment, descriptor, element, expression, operands, operand, bytes]
    cbv
  have child := children visit member 1 [] 0 layout layoutReady childReady 1 1 callReady operandEq layoutResult opened callRenewed
  rw [ordinalEq] at child
  refine ⟨child.1, child.2, ?_⟩
  simp only [callReady, childReady, layout, layoutReady, ready, pending, prepared, initial, stepState, config, entryContext,
    targetContext, entryImplementation, targetImplementation, environment, descriptor, element, expression, operands, operand, bytes]
  cbv

#print axioms arrayCall_childEvents
#print axioms module_history
#print axioms module_constructedCalls
end Goose.Proofs.ConstructionGhostSyntaxConstructedCallWitness
