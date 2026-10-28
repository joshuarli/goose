import Goose.Proofs.ConstructionGhostSyntaxTail

namespace Goose.Proofs.ConstructionGhostRecursiveArgumentWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostSyntaxTail

private def element : Ty := .varr (.int .u8)
private def bytes : Expr := .bytes element [65, 66] 0
private def argument : Expr := .call 2 [] 0
private def statements : List Stmt := [.expr (.call 1 [.construct argument] 0) 0]
private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def consumerContext : Context := ⟨1, "consumer", [], [], []⟩
private def producerContext : Context := ⟨2, "producer", [], [], []⟩
private def entry : Impl := ⟨"entry", #[], #[], #[], .mk 0 statements none, .unknown⟩
private def consumer : Impl := ⟨"consumer", #[⟨0, .byValue⟩], #[], #[⟨"value", element, .immutable, 0, 0⟩],
  .mk 1 [] none, .unknown⟩
private def producer : Impl := ⟨"producer", #[], #[⟨element, .value, none⟩], #[], .mk 2 [] (some bytes), .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[entry, consumer, producer], #[entryContext, consumerContext, producerContext], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem producerArguments : ∀ id actual start ready,
    getImplementation config 2 start = .ok (id, actual) ready → ArgumentSyntax config actual.params.toList [] := by
  intro id actual start ready lookup
  obtain ⟨context, found, idEq, implemented⟩ := implementation_lookup_source config 2 start ready id actual lookup
  have contextEq : context = producerContext := by simpa [config] using found.symm
  subst context
  subst id
  have implEq : actual = producer := by simpa [config, producerContext] using implemented.symm
  subst actual
  exact .nil

private theorem entryStatementsSyntax : ∀ statement ∈ statements, StatementSyntax config statement := by
  intro statement member
  simp only [statements, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  apply StatementSyntax.expression
  apply ValueSyntax.call 1 [.construct argument] 0 consumerContext consumer
  · rfl
  · rfl
  · rfl
  · change ArgumentSyntax config [⟨0, .byValue⟩] [.construct argument]
    exact .constructRecursive 0 [] argument [] (.channelCall 2 [] 0 producerArguments)
      (.channelCall 2 [] 0 producerArguments) .nil

private theorem closed : ClosedModuleWithTails config := by
  intro contextId context implementation found implemented
  cases contextId with
  | zero =>
      have contextEq : context = entryContext := by simpa [config] using found.symm
      subst context
      have implEq : implementation = entry := by simpa [config, entryContext] using implemented.symm
      subst implementation
      exact ⟨0, statements, none, rfl, entryStatementsSyntax, .none⟩
  | succ n =>
      cases n with
      | zero =>
          have contextEq : context = consumerContext := by simpa [config] using found.symm
          subst context
          have implEq : implementation = consumer := by simpa [config, consumerContext] using implemented.symm
          subst implementation
          exact ⟨1, [], none, rfl, (by simp), .none⟩
      | succ n =>
          cases n with
          | zero =>
              have contextEq : context = producerContext := by simpa [config] using found.symm
              subst context
              have implEq : implementation = producer := by simpa [config, producerContext] using implemented.symm
              subst implementation
              exact ⟨2, [], some bytes, rfl, (by simp), .constructed bytes (.bytes _ _ _) (.bytes _ _ _) (.bytes _ _ _)⟩
          | succ n => simp [config] at found

private theorem entryArguments : ∀ id actual start ready,
    getImplementation config 0 start = .ok (id, actual) ready → ArgumentSyntax config actual.params.toList [] := by
  intro id actual start ready lookup
  obtain ⟨context, found, idEq, implemented⟩ := implementation_lookup_source config 0 start ready id actual lookup
  have contextEq : context = entryContext := by simpa [config] using found.symm
  subst context
  subst id
  have implEq : actual = entry := by simpa [config, entryContext] using implemented.symm
  subst actual
  exact .nil

theorem recursiveConstructedArgument_history (fuel : Nat) :
    runModule fuel config .initial = moduleChannelResult fuel config
      (channelsFor config.layout 0 entry.results.toList 0 .initial) ∧
    SourceHistory config fuel [] (.channelCall ⟨0, 0, #[], [], []⟩ 0 [] [] 0) .initial
      (invokeCall fuel config ⟨0, 0, #[], [], []⟩ 0 [] [] 0 .initial) := by
  obtain ⟨execution, history⟩ := moduleHistoryWithTails fuel config closed entryContext entry rfl rfl rfl entryArguments
  exact ⟨execution, history [] .initial (by simp [channelsFor, config, entry, bind, pure])⟩

theorem recursiveConstructedArgument_witness :
    SourceHistory config 40 [] (.channelCall ⟨0, 0, #[], [], []⟩ 0 [] [] 0) .initial
      (invokeCall 40 config ⟨0, 0, #[], [], []⟩ 0 [] [] 0 .initial) ∧
    runModule 40 config .initial = .ok () (stepState (runModule 40 config .initial)) ∧
    (stepState (runModule 40 config .initial)).nextAct = 3 := by
  refine ⟨(recursiveConstructedArgument_history 40).2, ?_, ?_⟩ <;>
    simp only [stepState, config, entryContext, consumerContext, producerContext, entry, consumer, producer, statements, argument, bytes, element] <;> cbv

#print axioms recursiveConstructedArgument_history
#print axioms recursiveConstructedArgument_witness
end Goose.Proofs.ConstructionGhostRecursiveArgumentWitness
