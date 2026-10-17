import Goose.Proofs.ConstructionExecutionEventPrefixPrimitives
import Goose.Proofs.ConstructionExecutionProtocol

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol
open Goose.Proofs.ConstructionExecutionProtocol

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

def EventPrefix (before after : List Goose.Core.ConstructionEvent) : Prop :=
  ∃ suffix, after = before ++ suffix

theorem eventPrefix_refl (events : List Goose.Core.ConstructionEvent) : EventPrefix events events :=
  ⟨[], by simp⟩

theorem eventPrefix_iff_isPrefix (before after : List Goose.Core.ConstructionEvent) :
    EventPrefix before after ↔ before <+: after := by
  constructor
  · rintro ⟨suffix, equal⟩
    exact ⟨suffix, equal.symm⟩
  · rintro ⟨suffix, equal⟩
    exact ⟨suffix, equal.symm⟩

theorem eventPrefix_trans (before middle after : List Goose.Core.ConstructionEvent)
    (first : EventPrefix before middle) (second : EventPrefix middle after) :
    EventPrefix before after := by
  obtain ⟨left, rfl⟩ := first
  obtain ⟨right, rfl⟩ := second
  exact ⟨left ++ right, by simp [List.append_assoc]⟩

def KeepsEventPrefix (action : EvalM α) : Prop :=
  ∀ state, EventPrefix state.construction.events
    (Goose.Proofs.Exit.stepState (action state)).construction.events

private theorem keepsEventPrefix_from_protocol (action : EvalM α)
    (preserved : ∀ before, PreservesConstructionInvariant (PrefixInvariant before) action) :
    KeepsEventPrefix action := by
  intro state
  rw [eventPrefix_iff_isPrefix]
  exact preserved state.construction.events state List.prefix_rfl

structure EvaluationKeepsEventPrefix (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, KeepsEventPrefix (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, KeepsEventPrefix (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, KeepsEventPrefix (evalPlace fuel config environment operand)
  view : ∀ environment operand, KeepsEventPrefix (evalView fuel config environment operand)
  produce : ∀ environment channels operand, KeepsEventPrefix (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, KeepsEventPrefix (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, KeepsEventPrefix (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, KeepsEventPrefix (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, KeepsEventPrefix (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, KeepsEventPrefix (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, KeepsEventPrefix (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, KeepsEventPrefix (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, KeepsEventPrefix (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, KeepsEventPrefix (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, KeepsEventPrefix (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, KeepsEventPrefix (execStmts fuel config environment statements)
  statement : ∀ environment statement, KeepsEventPrefix (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, KeepsEventPrefix (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, KeepsEventPrefix (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, KeepsEventPrefix (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, KeepsEventPrefix (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, KeepsEventPrefix (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, KeepsEventPrefix (pushValue fuel config environment owner expression origin)

theorem evaluation_keepsEventPrefix (fuel : Nat) (config : EvalConfig) :
    EvaluationKeepsEventPrefix fuel config := by
  constructor
  · intro environment expression
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).value environment expression
  · intro environment count defaultValue operand
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).bound environment count defaultValue operand
  · intro environment operand
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).place environment operand
  · intro environment operand
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).view environment operand
  · intro environment channels operand
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).produce environment channels operand
  · intro environment channels expressions
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).operands environment channels expressions
  · intro environment destination expression
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).build environment destination expression
  · intro environment destination element expression
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).element environment destination element expression
  · intro environment vars params args
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).arguments environment vars params args
  · intro environment context args channels origin
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).call environment context args channels origin
  · intro environment pre body origin
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).activation environment pre body origin
  · intro environment pre body
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).activationBody environment pre body
  · intro environment channels body
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).resultBlock environment channels body
  · intro environment pre channels body
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).resultBlockWith environment pre channels body
  · intro environment pre channels body
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).block environment pre channels body
  · intro environment statements
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).statements environment statements
  · intro environment statement
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).statement environment statement
  · intro environment argument
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).printArgument environment argument
  · intro environment condition body
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).whileLoop environment condition body
  · intro environment var ty first last body
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).rangeLoop environment var ty first last body
  · intro environment var index byRef body view current
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).eachLoop environment var index byRef body view current
  · intro environment pre body
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).loop environment pre body
  · intro environment owner expression origin
    apply keepsEventPrefix_from_protocol
    intro before
    exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before) fuel config).push environment owner expression origin

theorem initGlobals_keepsEventPrefix (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    KeepsEventPrefix (initGlobals fuel config globals) :=
  keepsEventPrefix_from_protocol _ (fun _ => initGlobals_preservesConstructionInvariant fuel config globals)

theorem runModule_keepsEventPrefix (fuel : Nat) (config : EvalConfig) :
    KeepsEventPrefix (runModule fuel config) :=
  keepsEventPrefix_from_protocol _ (fun _ => runModule_preservesConstructionInvariant fuel config)

theorem wholeRun_terminal_skips_continuation (fuel : Nat) (config : EvalConfig)
    (initial terminal : ExecutionState) (reason : Goose.Core.Stop) (next : Unit → EvalM α)
    (stopped : runModule fuel config initial = .stop reason terminal) :
    (runModule fuel config >>= next) initial = .stop reason terminal := by
  simp only [bind, stopped]

theorem runModule_terminal_prefix (fuel : Nat) (config : EvalConfig)
    (initial terminal : ExecutionState) (reason : Goose.Core.Stop) (next : Unit → EvalM α)
    (stopped : runModule fuel config initial = .stop reason terminal) :
    EventPrefix initial.construction.events terminal.construction.events ∧
    (runModule fuel config >>= next) initial = .stop reason terminal := by
  have kept := runModule_keepsEventPrefix fuel config initial
  simp only [stopped, Goose.Proofs.Exit.stepState] at kept
  exact ⟨kept, wholeRun_terminal_skips_continuation fuel config initial terminal reason next stopped⟩

#print axioms evaluation_keepsEventPrefix
#print axioms runModule_terminal_prefix

end Goose.Proofs.ConstructionExecution
