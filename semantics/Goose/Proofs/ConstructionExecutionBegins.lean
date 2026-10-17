import Goose.Construct.Validate
import Goose.Proofs.Construct
import Goose.Proofs.ConstructionExecutionProtocolBegins

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionProtocol

attribute [local instance] destinationBeginsPrimitives destinationBeginsReservationPrimitives

def ConstructionBegins (state : ExecutionState) : Prop := DestinationBegins state.construction

def PreservesConstructionBegins (action : EvalM α) : Prop :=
  ∀ state, ConstructionBegins state → ConstructionBegins (Goose.Proofs.Exit.stepState (action state))

structure EvaluationPreservesConstructionBegins (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, PreservesConstructionBegins (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, PreservesConstructionBegins (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, PreservesConstructionBegins (evalPlace fuel config environment operand)
  view : ∀ environment operand, PreservesConstructionBegins (evalView fuel config environment operand)
  produce : ∀ environment channels operand, PreservesConstructionBegins (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, PreservesConstructionBegins (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, PreservesConstructionBegins (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, PreservesConstructionBegins (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, PreservesConstructionBegins (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, PreservesConstructionBegins (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, PreservesConstructionBegins (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, PreservesConstructionBegins (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, PreservesConstructionBegins (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, PreservesConstructionBegins (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, PreservesConstructionBegins (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, PreservesConstructionBegins (execStmts fuel config environment statements)
  statement : ∀ environment statement, PreservesConstructionBegins (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, PreservesConstructionBegins (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, PreservesConstructionBegins (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, PreservesConstructionBegins (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, PreservesConstructionBegins (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, PreservesConstructionBegins (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, PreservesConstructionBegins (pushValue fuel config environment owner expression origin)

theorem evaluation_preservesConstructionBegins (fuel : Nat) (config : EvalConfig) :
    EvaluationPreservesConstructionBegins fuel config := by
  have checked := evaluation_preservesConstructionInvariant (predicate := DestinationBegins) fuel config
  exact {
    value := checked.value
    bound := checked.bound
    place := checked.place
    view := checked.view
    produce := checked.produce
    operands := checked.operands
    build := checked.build
    element := checked.element
    arguments := checked.arguments
    call := checked.call
    activation := checked.activation
    activationBody := checked.activationBody
    resultBlock := checked.resultBlock
    resultBlockWith := checked.resultBlockWith
    block := checked.block
    statements := checked.statements
    statement := checked.statement
    printArgument := checked.printArgument
    whileLoop := checked.whileLoop
    rangeLoop := checked.rangeLoop
    eachLoop := checked.eachLoop
    loop := checked.loop
    push := checked.push
  }

theorem initGlobals_preservesConstructionBegins (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    PreservesConstructionBegins (initGlobals fuel config globals) :=
  initGlobals_preservesConstructionInvariant (predicate := DestinationBegins) fuel config globals

theorem runModule_preservesConstructionBegins (fuel : Nat) (config : EvalConfig) :
    PreservesConstructionBegins (runModule fuel config) :=
  runModule_preservesConstructionInvariant (predicate := DestinationBegins) fuel config

theorem runModule_destinationBeginIds (fuel : Nat) (config : EvalConfig) :
    destinationBeginIds (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction.events =
      List.range (Goose.Proofs.Exit.stepState
        (runModule fuel config .initial)).construction.destinations.size :=
  runModule_preservesConstructionBegins fuel config .initial initial_destination_begins

theorem runModule_distinctDestinationBegins (fuel : Nat) (config : EvalConfig) :
    (destinationBeginIds (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction.events).Nodup :=
  DestinationBegins.distinct _ (runModule_destinationBeginIds fuel config)

theorem runModule_destinationBegins_cover (fuel : Nat) (config : EvalConfig)
    (id : Goose.Core.DestinationId) :
    id ∈ destinationBeginIds (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction.events ↔
      id < (Goose.Proofs.Exit.stepState
        (runModule fuel config .initial)).construction.destinations.size :=
  DestinationBegins.covers _ (runModule_destinationBeginIds fuel config) id

theorem rejected_publication_preserves_execution (state : ExecutionState)
    (destinations : List Goose.Core.DestinationId) (kind : ConstructionFault)
    (origin : Goose.Core.OriginId)
    (rejected : preflightPublication state.construction destinations = .error kind) :
    liftConstruction origin (publishOperation destinations) state =
      .stop (match kind with
        | .capacity => .abort .capacity origin
        | .storage => .fault .danglingRoot
        | .destination => .fault .unbound
        | .ownership | .protocol => .fault .flow) state := by
  rw [liftConstruction, Goose.Proofs.Construct.publication_rejection_keeps_prefix
    state.construction destinations kind rejected]
  cases kind <;> rfl

theorem terminal_receiver_scope_activation (layout : LayoutEnv) (activation : RuntimeActivation)
    (resultTypes : List Ty) (scope scopeInst : Nat) (origin : Goose.Core.OriginId)
    (destination : Goose.Core.DestinationId) (action : EvalM (List Carrier))
    (state terminal : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : action state = .stop reason terminal) :
    finishActivation layout activation resultTypes origin
      (withScope activation scope scopeInst (protectDestination origin destination action)) state =
        .stop reason terminal := by
  simp [finishActivation, withScope, protectDestination, stopped]

#print axioms evaluation_preservesConstructionBegins
#print axioms runModule_destinationBegins_cover

end Goose.Proofs.ConstructionExecution
