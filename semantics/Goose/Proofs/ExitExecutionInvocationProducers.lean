import Goose.Proofs.ExitExecutionInvocation

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

inductive ProducerReceivingPrefix (environment : RuntimeActivation) (incoming : List Channel)
    (expression : Expr) : ExecutionState → List Channel → List Channel → ExecutionState → Prop
  | actual (initial renewedState prepared : ExecutionState) (planned channels : List Channel)
      (renewed : ((incoming.mapM fun channel => match channel with
        | .register ty => pure (Channel.register ty)
        | .construct id => do pure (.construct (← liftConstruction (expressionOrigin expression) (renewReceivingDestination id)))
        | .completion token => pure (.completion token)) : EvalM (List Channel)) initial = .ok planned renewedState)
      (selected : ((match expression with
        | .values _ | .ifE .. | .blockE .. => pure planned
        | _ => planned.mapM (selectCompletionChannel environment expression)) : EvalM (List Channel))
          renewedState = .ok channels prepared) :
      ProducerReceivingPrefix environment incoming expression initial planned channels prepared

def producerSingleExpression : Expr → Bool
  | .values _ | .call .. | .ifE .. | .blockE .. => false
  | _ => true

def builderValueExpression : Expr → Bool
  | .call .. | .ifE .. | .blockE .. | .values [_] | .arrLit .. | .fill ..
  | .bytes .. | .str .. | .copy .. | .resultLocal .. => false
  | _ => true

def producerBreakState (environment : RuntimeActivation) (channels : List Channel)
    (state : ExecutionState) : ExecutionState :=
  { state with
    nextScope := state.nextScope + 1
    breaks := (⟨state.nextScope, environment.act, .block, channels⟩ : BreakTarget) :: state.breaks }

inductive ProducerBodyChild (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (planned : List Channel) : List Channel → Expr → ExecutionState →
      {β : Type} → ExitInvocation β → ExecutionState → Prop
  | value (channels : List Channel) (expression : Expr) (state : ExecutionState)
      (single : producerSingleExpression expression = true)
      (receiving : channels = [] ∨ ∃ ty, channels = [.register ty]) :
      ProducerBodyChild fuel config environment planned channels expression state (.value fuel environment expression) state
  | build (destination : Nat) (expression : Expr) (state : ExecutionState)
      (single : producerSingleExpression expression = true)
      (unnamed : ∀ localVar origin, expression ≠ .resultLocal localVar origin) :
      ProducerBodyChild fuel config environment planned [.construct destination] expression state
        (.build fuel environment destination expression) state
  | resultLocalBuild (destination localVar : Nat) (origin : Goose.Core.OriginId)
      (initial ready : ExecutionState) (stored : StoredValue)
      (prepared : ((do
        let .stored actual ← readLoc fuel config.layout ⟨← rootOf environment localVar, []⟩ | fault .shape
        let named ← match planned with
          | [.completion token] => prepareNamedCarrierAt origin token destination actual
          | _ => prepareNamedCarrier origin destination actual
        pure (actual, named)) : EvalM (StoredValue × Option Carrier)) initial = .ok (stored, none) ready) :
      ProducerBodyChild fuel config environment planned [.construct destination] (.resultLocal localVar origin) initial
        (.build fuel environment destination (.resultLocal localVar origin)) ready
  | operands (channels : List Channel) (operands : List Expr) (state : ExecutionState) :
      ProducerBodyChild fuel config environment planned channels (.values operands) state
        (.operands fuel environment channels operands) state
  | call (channels : List Channel) (context : Goose.Core.ContextId) (arguments : List Arg)
      (origin : Goose.Core.OriginId) (state : ExecutionState) :
      ProducerBodyChild fuel config environment planned channels (.call context arguments origin) state
        (.call fuel environment context arguments channels origin) state
  | condition (channels : List Channel) (condition : Expr) (yes no : Block)
      (origin : Goose.Core.OriginId) (state : ExecutionState) :
      ProducerBodyChild fuel config environment planned channels (.ifE condition yes no origin) state
        (.value fuel environment condition) state
  | conditionalResult (channels : List Channel) (condition : Expr) (yes no : Block)
      (origin : Goose.Core.OriginId) (initial ready : ExecutionState) (value : Value) (selected : Bool)
      (evaluated : evalValue fuel config environment condition initial = .ok value ready)
      (boolean : expectBool value ready = .ok selected ready) :
      ProducerBodyChild fuel config environment planned channels (.ifE condition yes no origin) initial
        (.resultBlock fuel environment channels (if selected then yes else no)) ready
  | blockResult (channels : List Channel) (body : Block) (origin : Goose.Core.OriginId)
      (state : ExecutionState) :
      ProducerBodyChild fuel config environment planned channels (.blockE body origin) state
        (.resultBlock fuel environment channels body) (producerBreakState environment channels state)

inductive BuilderBodyChild (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (destination : Nat) : Expr → ExecutionState → {β : Type} → ExitInvocation β → ExecutionState → Prop
  | call (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (state : ExecutionState) :
      BuilderBodyChild fuel config environment destination (.call context arguments origin) state
        (.call fuel environment context arguments [.construct destination] origin) state
  | condition (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId) (state : ExecutionState) :
      BuilderBodyChild fuel config environment destination (.ifE condition yes no origin) state
        (.value fuel environment condition) state
  | conditionalResult (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId)
      (initial ready : ExecutionState) (value : Value) (selected : Bool)
      (evaluated : evalValue fuel config environment condition initial = .ok value ready)
      (boolean : expectBool value ready = .ok selected ready) :
      BuilderBodyChild fuel config environment destination (.ifE condition yes no origin) initial
        (.resultBlock fuel environment [.construct destination] (if selected then yes else no)) ready
  | blockResult (body : Block) (origin : Goose.Core.OriginId) (state : ExecutionState) :
      BuilderBodyChild fuel config environment destination (.blockE body origin) state
        (.resultBlock fuel environment [.construct destination] body)
          (producerBreakState environment [.construct destination] state)
  | values (operand : Expr) (state : ExecutionState) :
      BuilderBodyChild fuel config environment destination (.values [operand]) state
        (.build fuel environment destination operand) state
  | array (ty : Ty) (before after : List Expr) (operand : Expr) (origin : Goose.Core.OriginId)
      (initial ready : ExecutionState) (pending : PendingDestination) (element : Ty)
      (lookup : getDestination destination initial = .ok pending initial)
      (elementType : Goose.Construct.elementType pending.capability.logicalType = some element)
      (preceding : ((do for previous in before do
        buildElement fuel config environment destination element previous) : EvalM Unit) initial = .ok () ready) :
      BuilderBodyChild fuel config environment destination (.arrLit ty (before ++ operand :: after) origin) initial
        (.element fuel environment destination element operand) ready
  | fillBuild (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
      (initial ready : ExecutionState) (source : Nat) (dynamic : element.nonfixed = true)
      (created : (newDestination config.layout environment.act element .value origin) initial = .ok source ready) :
      BuilderBodyChild fuel config environment destination (.fill (.arr element count) operand origin) initial
        (.build fuel environment source operand) ready
  | fillValue (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
      (state : ExecutionState) (fixed : element.nonfixed = false) :
      BuilderBodyChild fuel config environment destination (.fill (.arr element count) operand origin) state
        (.value fuel environment operand) state
  | stringArgument (ty : Ty) (before after : List PrintArg) (argument : PrintArg)
      (origin : Goose.Core.OriginId) (initial ready : ExecutionState)
      (preceding : ((do for previous in before do
        let bytes ← evalPrintArg fuel config environment previous
        for byte in bytes.data do
          receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)) : EvalM Unit)
            initial = .ok () ready) :
      BuilderBodyChild fuel config environment destination (.str ty (before ++ argument :: after) origin) initial
        (.printArgument fuel environment argument) ready
  | copy (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) (state : ExecutionState) :
      BuilderBodyChild fuel config environment destination (.copy ty source origin) state
        (.place fuel environment source) state
  | value (expression : Expr) (state : ExecutionState) (fallback : builderValueExpression expression = true) :
      BuilderBodyChild fuel config environment destination expression state (.value fuel environment expression) state

inductive ProducerInvocationChild (config : EvalConfig) :
    {α β : Type} → ExitInvocation α → ExecutionState → ExitInvocation β → ExecutionState → Prop
  | produce {fuel : Nat} {environment : RuntimeActivation} {incoming planned channels : List Channel}
      {expression : Expr} {initial prepared ready : ExecutionState} {β : Type} {child : ExitInvocation β}
      (receiving : ProducerReceivingPrefix environment incoming expression initial planned channels prepared)
      (body : ProducerBodyChild fuel config environment planned channels expression prepared child ready) :
      ProducerInvocationChild config (.produce (fuel + 1) environment incoming expression) initial child ready
  | build {fuel : Nat} {environment : RuntimeActivation} {incoming destination : Nat}
      {expression : Expr} {initial prepared ready : ExecutionState} {β : Type} {child : ExitInvocation β}
      (renewed : liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) initial = .ok destination prepared)
      (body : BuilderBodyChild fuel config environment destination expression prepared child ready) :
      ProducerInvocationChild config (.build (fuel + 1) environment incoming expression) initial child ready
  | elementBuild (fuel : Nat) (environment : RuntimeActivation) (parent : Nat) (element : Ty) (operand : Expr)
      (initial ready : ExecutionState) (child : Nat) (dynamic : element.nonfixed = true)
      (opened : ((do
        let layout ← receivingLayout config.layout element
        receivingAction (expressionOrigin operand) parent (fun parent => openChild parent element layout)) : EvalM Nat)
          initial = .ok child ready) :
      ProducerInvocationChild config (.element (fuel + 1) environment parent element operand) initial
        (.build fuel environment child operand) ready
  | elementValue (fuel : Nat) (environment : RuntimeActivation) (parent : Nat) (element : Ty) (operand : Expr)
      (state : ExecutionState) (fixed : element.nonfixed = false) :
      ProducerInvocationChild config (.element (fuel + 1) environment parent element operand) state
        (.value fuel environment operand) state

end Goose.Proofs.ExitExecution
