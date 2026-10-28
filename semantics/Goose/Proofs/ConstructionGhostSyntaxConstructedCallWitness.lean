import Goose.Proofs.ConstructionGhostSyntaxTail

namespace Goose.Proofs.ConstructionGhostSyntaxConstructedCallWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostSyntaxTail

private def element : Ty := .varr (.int .u8)
private def bytes : Expr := .bytes element [65, 66] 0
private def operand : Expr := .call 1 [] 0
private def operands : List Expr := [operand, operand]
private def expression : Expr := .arrLit (.varr element) operands 0
private def statements : List Stmt := [.letS 0 expression 0]
private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def targetContext : Context := ⟨1, "target", [], [], []⟩
private def entryImplementation : Impl := ⟨"entry", #[], #[], #[⟨"nested", .varr element, .immutable, 0, 0⟩],
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

#print axioms module_history
#print axioms module_constructedCalls
end Goose.Proofs.ConstructionGhostSyntaxConstructedCallWitness
