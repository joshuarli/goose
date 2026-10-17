import Goose.Proofs.ExitExecutionExitChannels

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

inductive ExitInvocation : Type → Type
  | module (fuel : Nat) : ExitInvocation Unit
  | globals (fuel : Nat) (globals : List Goose.Core.GlobalId) : ExitInvocation Unit
  | value (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) : ExitInvocation Value
  | bound (fuel : Nat) (environment : RuntimeActivation) (count : Nat) (defaultValue : Int)
      (operand : Bound) : ExitInvocation Int
  | place (fuel : Nat) (environment : RuntimeActivation) (operand : Place) : ExitInvocation Goose.Core.Loc
  | view (fuel : Nat) (environment : RuntimeActivation) (operand : View) : ExitInvocation RuntimeView
  | produce (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (expression : Expr) : ExitInvocation (List Carrier)
  | operands (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (expressions : List Expr) : ExitInvocation (List Carrier)
  | build (fuel : Nat) (environment : RuntimeActivation) (destination : Nat) (expression : Expr) : ExitInvocation Unit
  | element (fuel : Nat) (environment : RuntimeActivation) (destination : Nat) (element : Ty)
      (expression : Expr) : ExitInvocation Unit
  | arguments (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar)
      (params : List Param) (arguments : List Arg) : ExitInvocation (List Value)
  | call (fuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
      (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId) : ExitInvocation (List Carrier)
  | activation (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) (origin : Goose.Core.OriginId) : ExitInvocation (List Carrier)
  | activationBody (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) : ExitInvocation (List Carrier)
  | activationScope (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) : ExitInvocation (Flow × List Carrier)
  | completionTail (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (expression : Expr) : ExitInvocation (List Carrier)
  | resultBlock (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (body : Block) : ExitInvocation (Flow × List Carrier)
  | resultBlockWith (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (body : Block) : ExitInvocation (Flow × List Carrier)
  | resultScope (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (body : Block) : ExitInvocation (Flow × List Carrier)
  | block (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (body : Block) : ExitInvocation Flow
  | statements (fuel : Nat) (environment : RuntimeActivation) (statements : List Stmt) : ExitInvocation Flow
  | statement (fuel : Nat) (environment : RuntimeActivation) (statement : Stmt) : ExitInvocation Flow
  | printArgument (fuel : Nat) (environment : RuntimeActivation) (argument : PrintArg) : ExitInvocation ByteArray
  | whileLoop (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block) : ExitInvocation Flow
  | rangeLoop (fuel : Nat) (environment : RuntimeActivation) (var : Goose.Core.VarId)
      (ty : Goose.Core.IntTy) (first last : Int) (body : Block) : ExitInvocation Flow
  | eachLoop (fuel : Nat) (environment : RuntimeActivation) (var : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat) :
      ExitInvocation Flow
  | loop (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) : ExitInvocation Flow
  | push (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) : ExitInvocation Value

def ExitInvocation.action (config : EvalConfig) : ExitInvocation α → EvalM α
  | .module fuel => runModule fuel config
  | .globals fuel globalIds => initGlobals fuel config globalIds
  | .value fuel environment expression => evalValue fuel config environment expression
  | .bound fuel environment count defaultValue operand => evalBound fuel config environment count defaultValue operand
  | .place fuel environment operand => evalPlace fuel config environment operand
  | .view fuel environment operand => evalView fuel config environment operand
  | .produce fuel environment channels expression => evalProduce fuel config environment channels expression
  | .operands fuel environment channels expressions => evalOperands fuel config environment channels expressions
  | .build fuel environment destination expression => buildExpr fuel config environment destination expression
  | .element fuel environment destination elementType expression => buildElement fuel config environment destination elementType expression
  | .arguments fuel environment vars params actualArguments => evalArguments fuel config environment vars params actualArguments
  | .call fuel environment context actualArguments channels origin => invokeCall fuel config environment context actualArguments channels origin
  | .activation fuel environment pre body origin => enterActivation fuel config environment pre body origin
  | .activationBody fuel environment pre body => execActivationBody fuel config environment pre body
  | .activationScope fuel environment pre body => execResultScope environment pre environment.channels body
      (fun environment statements => execStmts fuel config environment statements)
      (fun localEnvironment expression => withCompletionChannels environment.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config localEnvironment channels expression))
  | .completionTail fuel environment channels expression =>
      withCompletionChannels channels (expressionOrigin expression)
        (fun prepared => evalProduce fuel config environment prepared expression)
  | .resultBlock fuel environment channels body => execResultBlock fuel config environment channels body
  | .resultBlockWith fuel environment pre channels body => execResultBlockWith fuel config environment pre channels body
  | .resultScope fuel environment pre channels body => execResultScope environment pre channels body
      (fun environment statements => execStmts fuel config environment statements)
      (fun environment expression => evalProduce fuel config environment channels expression)
  | .block fuel environment pre channels body => execBlock fuel config environment pre channels body
  | .statements fuel environment statementList => execStmts fuel config environment statementList
  | .statement fuel environment oneStatement => execStmt fuel config environment oneStatement
  | .printArgument fuel environment argument => evalPrintArg fuel config environment argument
  | .whileLoop fuel environment condition body => execWhile fuel config environment condition body
  | .rangeLoop fuel environment var ty first last body => execRange fuel config environment var ty first last body
  | .eachLoop fuel environment var index byRef body runtimeView current =>
      execEach fuel config environment var index byRef body runtimeView current
  | .loop fuel environment pre body => loopBody fuel config environment pre body
  | .push fuel environment owner expression origin => pushValue fuel config environment owner expression origin

inductive CallArgumentPrefix (config : EvalConfig)
    (context : Goose.Core.ContextId) (channels : List Channel) (origin : Goose.Core.OriginId) :
    ExecutionState → Goose.Core.ImplId → Impl → List Channel → ExecutionState → Prop
  | actual (initial lookupState firstState : ExecutionState)
      (id : Goose.Core.ImplId) (implementation : Impl) (firstChannels : List Channel)
      (lookup : getImplementation config context initial = .ok (id, implementation) lookupState)
      (arity : (channels.length != implementation.results.size) = false)
      (receiving : (((channels.zip implementation.results.toList).mapM fun pair => do
        match pair.2.request, pair.1 with
        | .register, _ => pure (Channel.register pair.2.ty)
        | .value, .construct incoming | .elementRun, .construct incoming =>
            let destination ← liftConstruction origin (renewReceivingDestination incoming)
            liftConstruction origin (adaptDestinationType destination pair.2.ty)
            pure (.construct destination)
        | .value, .register _ | .elementRun, .register _ => fault .shape
        | _, .completion _ => fault .flow) : EvalM (List Channel)) lookupState = .ok firstChannels firstState) :
      CallArgumentPrefix config context channels origin initial id implementation firstChannels firstState

inductive CallActivationPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId) :
    ExecutionState → RuntimeActivation → List (Goose.Core.VarId × Value) → Block → ExecutionState → Prop
  | actual (initial firstState argumentState ready : ExecutionState)
      (id : Goose.Core.ImplId) (implementation : Impl) (firstChannels renewed : List Channel) (values : List Value)
      (receiving : CallArgumentPrefix config context channels origin initial id implementation firstChannels firstState)
      (argumentsDone : evalArguments fuel config environment implementation.vars implementation.params.toList arguments
        firstState = .ok values argumentState)
      (renewal : ((firstChannels.mapM fun channel => match channel with
        | .register ty => pure (Channel.register ty)
        | .construct destination => do
            pure (.construct (← liftConstruction origin (renewReceivingDestination destination)))
        | .completion _ => fault .flow) : EvalM (List Channel)) argumentState = .ok renewed ready)
      (depth : ready.activations.length < Goose.Core.maxCallDepth) :
      CallActivationPrefix fuel config environment context arguments channels origin initial
        ⟨id, ready.nextAct, implementation.vars, [], renewed⟩
        ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
        implementation.body { ready with
          nextAct := ready.nextAct + 1
          activations := ⟨id, ready.nextAct, implementation.vars, [], renewed⟩ :: ready.activations }

end Goose.Proofs.ExitExecution
