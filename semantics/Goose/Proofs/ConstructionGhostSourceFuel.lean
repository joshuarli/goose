import Goose.Proofs.ConstructionGhostSourceMutual

namespace Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostArguments
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostProducerChannel Goose.Proofs.ConstructionGhostRegisterProducer Goose.Proofs.ConstructionGhostScalarProducer
open Goose.Proofs.ConstructionGhostSourceTransition Goose.Proofs.ConstructionGhostBlockProducerTransition

inductive FuelSupport (config : EvalConfig) : {α : Type} → Nat → SourceOperation α → Prop
  | timeout (operation : SourceOperation α) : FuelSupport config 0 operation
  | legacy (fuel : Nat) {operation : SourceOperation α} (supported : SupportedOperation config operation) :
      FuelSupport config fuel operation
  | readValue (fuel : Nat) (environment : RuntimeActivation) (place : Place)
      (child : FuelSupport config fuel (.place environment place)) : FuelSupport config (fuel + 1) (.value environment (.read place))
  | referenceValue (fuel : Nat) (environment : RuntimeActivation) (mutability : Goose.Core.Mutability) (place : Place)
      (child : FuelSupport config fuel (.place environment place)) : FuelSupport config (fuel + 1) (.value environment (.ref mutability place))
  | lengthValue (fuel : Nat) (environment : RuntimeActivation) (view : View)
      (child : FuelSupport config fuel (.view environment view)) : FuelSupport config (fuel + 1) (.value environment (.len view))
  | printArgumentExpression (fuel : Nat) (environment : RuntimeActivation) (expression : Expr)
      (child : FuelSupport config fuel (.value environment expression)) :
      FuelSupport config (fuel + 1) (.printArgument environment (.expr expression))
  | printArgumentView (fuel : Nat) (environment : RuntimeActivation) (view : View)
      (child : FuelSupport config fuel (.view environment view)) :
      FuelSupport config (fuel + 1) (.printArgument environment (.view view))
  | printArguments (fuel : Nat) (environment : RuntimeActivation) (arguments : List PrintArg) (origin : Goose.Core.OriginId)
      (children : ∀ argument ∈ arguments, FuelSupport config fuel (.printArgument environment argument)) :
      FuelSupport config (fuel + 1) (.statement environment (.print arguments origin))
  | expressionBound (fuel : Nat) (environment : RuntimeActivation) (count : Nat) (defaultValue : Int)
      (operand : Expr) (fromEnd : Bool) (child : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.bound environment count defaultValue (if fromEnd then .fromEnd operand else .expr operand))
  | sliceValue (fuel : Nat) (environment : RuntimeActivation) (mutability : Goose.Core.Mutability)
      (view : View) (lo hi : Bound) (origin : Goose.Core.OriginId)
      (viewChild : FuelSupport config fuel (.view environment view))
      (loChild : ∀ count defaultValue, FuelSupport config fuel (.bound environment count defaultValue lo))
      (hiChild : ∀ count defaultValue, FuelSupport config fuel (.bound environment count defaultValue hi)) :
      FuelSupport config (fuel + 1) (.value environment (.slice mutability view lo hi origin))
  | popValue (fuel : Nat) (environment : RuntimeActivation) (place : Place) (origin : Goose.Core.OriginId)
      (child : FuelSupport config fuel (.place environment place)) : FuelSupport config (fuel + 1) (.value environment (.pop place origin))
  | valueView (fuel : Nat) (environment : RuntimeActivation) (operand : Expr)
      (child : FuelSupport config fuel (.value environment operand)) : FuelSupport config (fuel + 1) (.view environment (.val operand))
  | aggregate (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (operands : List Expr)
      (shape : ValueAggregate expression operands)
      (children : ∀ operand ∈ operands, FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.value environment expression)
  | unary (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.UnOp) (operand : Expr) (origin : Goose.Core.OriginId)
      (child : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.value environment (.un operation operand origin))
  | conversion (fuel : Nat) (environment : RuntimeActivation) (kind : Goose.Core.ConvKind) (target : Ty) (operand : Expr) (origin : Goose.Core.OriginId)
      (child : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.value environment (.conv kind target operand origin))
  | negation (fuel : Nat) (environment : RuntimeActivation) (operand : Expr)
      (child : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.value environment (.not operand))
  | comparison (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.CmpOp) (first second : Expr)
      (left : FuelSupport config fuel (.value environment first)) (right : FuelSupport config fuel (.value environment second)) :
      FuelSupport config (fuel + 1) (.value environment (.cmp operation first second))
  | binary (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId)
      (left : FuelSupport config fuel (.value environment first)) (right : FuelSupport config fuel (.value environment second)) :
      FuelSupport config (fuel + 1) (.value environment (.bin operation first second origin))
  | logical (fuel : Nat) (environment : RuntimeActivation) (isAnd : Bool) (first second : Expr)
      (left : FuelSupport config fuel (.value environment first)) (right : FuelSupport config fuel (.value environment second)) :
      FuelSupport config (fuel + 1) (.value environment (logicalExpression isAnd first second))
  | valueNonfixedArray (fuel : Nat) (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
      (origin : Goose.Core.OriginId) (nonfixed : ty.nonfixed = true)
      (child : ∀ destination, FuelSupport config fuel (.builder environment destination (.arrLit ty operands origin))) :
      FuelSupport config (fuel + 1) (.value environment (.arrLit ty operands origin))
  | builderArray (fuel : Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId) (ty : Ty)
      (operands : List Expr) (origin : Goose.Core.OriginId)
      (children : ∀ operand ∈ operands, ∀ parent element, FuelSupport config fuel (.element environment parent element operand)) :
      FuelSupport config (fuel + 1) (.builder environment incoming (.arrLit ty operands origin))
  | element (fuel : Nat) (environment : RuntimeActivation) (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr)
      (valueChild : FuelSupport config fuel (.value environment operand))
      (builderChild : ∀ destination, FuelSupport config fuel (.builder environment destination operand)) :
      FuelSupport config (fuel + 1) (.element environment parent element operand)
  | valueNonfixedFill (fuel : Nat) (environment : RuntimeActivation) (element : Ty) (count : Nat)
      (operand : Expr) (origin : Goose.Core.OriginId) (nonfixed : (Ty.arr element count).nonfixed = true)
      (child : ∀ destination, FuelSupport config fuel (.builder environment destination (.fill (.arr element count) operand origin))) :
      FuelSupport config (fuel + 1) (.value environment (.fill (.arr element count) operand origin))
  | builderChannelCall (fuel : Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId)
      (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (child : ∀ destination, FuelSupport config fuel (.channelCall environment context arguments [.construct destination] origin)) :
      FuelSupport config (fuel + 1) (.builder environment incoming (.call context arguments origin))
  | builderSingleValue (fuel : Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId)
      (operand : Expr) (child : ∀ destination, FuelSupport config fuel (.builder environment destination operand)) :
      FuelSupport config (fuel + 1) (.builder environment incoming (.values [operand]))
  | builderBlock (fuel : Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId)
      (block : Block) (origin : Goose.Core.OriginId)
      (child : ∀ destination, FuelSupport config fuel (.resultBlock environment [.construct destination] block)) :
      FuelSupport config (fuel + 1) (.builder environment incoming (.blockE block origin))
  | builderConditional (fuel : Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId)
      (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId)
      (conditionChild : FuelSupport config fuel (.value environment condition))
      (yesChild : ∀ destination, FuelSupport config fuel (.resultBlock environment [.construct destination] yes))
      (noChild : ∀ destination, FuelSupport config fuel (.resultBlock environment [.construct destination] no)) :
      FuelSupport config (fuel + 1) (.builder environment incoming (.ifE condition yes no origin))
  | fillBuilder (fuel : Nat) (environment : RuntimeActivation) (destination : Goose.Core.DestinationId)
      (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
      (valueChild : FuelSupport config fuel (.value environment operand))
      (builderChild : ∀ source, FuelSupport config fuel (.builder environment source operand)) :
      FuelSupport config (fuel + 1) (.builder environment destination (.fill (.arr element count) operand origin))
  | fill (fuel : Nat) (environment : RuntimeActivation) (element : Ty) (count : Nat) (origin : Goose.Core.OriginId)
      (operand : Expr) (fixed : (Ty.arr element count).nonfixed = false)
      (child : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.value environment (.fill (.arr element count) operand origin))
  | valueBlockProducer (fuel : Nat) (environment : RuntimeActivation) (block : Block) (origin : Goose.Core.OriginId)
      (child : ∀ channels, FuelSupport config fuel (.producerWith environment channels (.blockE block origin))) :
      FuelSupport config (fuel + 1) (.value environment (.blockE block origin))
  | producerValues (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel) (operands : List Expr)
      (child : ∀ planned, FuelSupport config fuel (.producerOperands environment planned operands)) :
      FuelSupport config (fuel + 1) (.producerWith environment channels (.values operands))
  | producerOperandsEmpty (fuel : Nat) (environment : RuntimeActivation) :
      FuelSupport config (fuel + 1) (.producerOperands environment [] [])
  | producerOperandsNoChannels (fuel : Nat) (environment : RuntimeActivation) (operand : Expr) (operands : List Expr) :
      FuelSupport config (fuel + 1) (.producerOperands environment [] (operand :: operands))
  | producerOperandsNoValues (fuel : Nat) (environment : RuntimeActivation) (channel : Channel) (channels : List Channel) :
      FuelSupport config (fuel + 1) (.producerOperands environment (channel :: channels) [])
  | producerOperandsCons (fuel : Nat) (environment : RuntimeActivation) (channel : Channel) (channels : List Channel)
      (operand : Expr) (operands : List Expr)
      (head : FuelSupport config fuel (.producerWith environment [channel] operand))
      (tail : FuelSupport config fuel (.producerOperands environment channels operands)) :
      FuelSupport config (fuel + 1) (.producerOperands environment (channel :: channels) (operand :: operands))
  | producerConditional (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId)
      (conditionChild : FuelSupport config fuel (.value environment condition))
      (yesChild : ∀ planned, FuelSupport config fuel (.resultBlock environment planned yes))
      (noChild : ∀ planned, FuelSupport config fuel (.resultBlock environment planned no)) :
      FuelSupport config (fuel + 1) (.producerWith environment channels (.ifE condition yes no origin))
  | producerBlock (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel) (block : Block) (origin : Goose.Core.OriginId)
      (child : ∀ planned, FuelSupport config fuel (.resultBlock environment planned block)) :
      FuelSupport config (fuel + 1) (.producerWith environment channels (.blockE block origin))
  | resultBlock (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel) (block : Block)
      (child : FuelSupport config fuel (.resultBlockWith environment [] channels block)) :
      FuelSupport config (fuel + 1) (.resultBlock environment channels block)
  | resultBlockWith (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
      (body : ∀ scopedEnvironment, FuelSupport config fuel (.statements scopedEnvironment statements))
      (tailChild : ∀ scopedEnvironment expression, tail = some expression → FuelSupport config fuel (.producerWith scopedEnvironment channels expression)) :
      FuelSupport config (fuel + 1) (.resultBlockWith environment pre channels (.mk scope statements tail))
  | conditional (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId)
      (conditionChild : FuelSupport config fuel (.value environment condition))
      (yesChild : FuelSupport config fuel (.block environment yes)) (noChild : FuelSupport config fuel (.block environment no)) :
      FuelSupport config (fuel + 1) (.value environment (.ifE condition yes no origin))
  | blockTail (fuel : Nat) (environment : RuntimeActivation) (scope : Nat) (statements : List Stmt) (expression : Expr)
      (body : ∀ scopedEnvironment, FuelSupport config fuel (.statements scopedEnvironment statements))
      (tail : ∀ scopedEnvironment, FuelSupport config fuel (.value scopedEnvironment expression)) :
      FuelSupport config (fuel + 1) (.block environment (.mk scope statements (some expression)))
  | valueFirstStatement (fuel : Nat) (environment : RuntimeActivation) (statement : Stmt) (expression : Expr)
      (shape : ValueFirstStatement statement expression) (child : FuelSupport config fuel (.value environment expression)) :
      FuelSupport config (fuel + 1) (.statement environment statement)
  | leafStatement (fuel : Nat) (environment : RuntimeActivation) (statement : Stmt) (shape : LeafStatement statement) :
      FuelSupport config (fuel + 1) (.statement environment statement)
  | assignment (fuel : Nat) (environment : RuntimeActivation) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId)
      (placeChild : FuelSupport config fuel (.place environment place))
      (valueChild : FuelSupport config fuel (.value environment expression)) :
      FuelSupport config (fuel + 1) (.statement environment (.assign place expression origin))
  | declaration (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId)
      (value : FuelSupport config fuel (.value environment expression))
      (builder : ∀ destination, FuelSupport config fuel (.builder environment destination expression)) :
      FuelSupport config (fuel + 1) (.statement environment (.letS localVar expression origin))
  | expression (fuel : Nat) (environment : RuntimeActivation) (operand : Expr) (origin : Goose.Core.OriginId)
      (child : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.statement environment (.expr operand origin))
  | sequence (fuel : Nat) (environment : RuntimeActivation) (statement : Stmt) (rest : List Stmt)
      (head : FuelSupport config fuel (.statement environment statement))
      (tail : FuelSupport config fuel (.statements environment rest)) :
      FuelSupport config (fuel + 1) (.statements environment (statement :: rest))
  | activationBody (fuel : Nat) (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (body : ∀ environment, FuelSupport config fuel (.statements environment statements)) :
      FuelSupport config (fuel + 1) (.activationBody activation (.mk scope statements none))
  | activation (fuel : Nat) (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (origin : Goose.Core.OriginId)
      (body : FuelSupport config fuel (.activationBody activation (.mk scope statements none))) :
      FuelSupport config (fuel + 1) (.activation activation (.mk scope statements none) origin)
  | dereferencePlace (fuel : Nat) (environment : RuntimeActivation) (operand : Expr)
      (child : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.place environment (.deref operand))
  | fieldPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (index : Nat)
      (child : FuelSupport config fuel (.place environment owner)) :
      FuelSupport config (fuel + 1) (.place environment (.field owner index))
  | elementPlace (fuel : Nat) (environment : RuntimeActivation) (view : View) (operand : Expr) (origin : Goose.Core.OriginId)
      (viewChild : FuelSupport config fuel (.view environment view))
      (indexChild : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.place environment (.elem view operand origin))
  | block (fuel : Nat) (environment : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (body : ∀ scopedEnvironment, FuelSupport config fuel (.statements scopedEnvironment statements)) :
      FuelSupport config (fuel + 1) (.block environment (.mk scope statements none))
  | placeView (fuel : Nat) (environment : RuntimeActivation) (place : Place)
      (child : FuelSupport config fuel (.place environment place)) :
      FuelSupport config (fuel + 1) (.view environment (.of place))
  | boundBlock (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt)
      (body : ∀ scopedEnvironment, FuelSupport config fuel (.statements scopedEnvironment statements)) :
      FuelSupport config (fuel + 1) (.blockWith environment pre (.mk scope statements none))
  | boundLoopBody (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
      (child : FuelSupport config fuel (.blockWith environment pre body)) :
      FuelSupport config (fuel + 1) (.loopBodyWith environment pre body)
  | eachLoop (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId)
      (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat)
      (bodyChild : ∀ pre, FuelSupport config fuel (.loopBodyWith environment pre body))
      (next : FuelSupport config fuel (.eachLoop environment localVar index byRef body view (current + 1))) :
      FuelSupport config (fuel + 1) (.eachLoop environment localVar index byRef body view current)
  | rangeLoop (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (ty : Goose.Core.IntTy)
      (first last : Int) (body : Block)
      (bodyChild : ∀ pre, FuelSupport config fuel (.loopBodyWith environment pre body))
      (next : FuelSupport config fuel (.rangeLoop environment localVar ty (first + 1) last body)) :
      FuelSupport config (fuel + 1) (.rangeLoop environment localVar ty first last body)
  | rangeStatement (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (first last : Expr) (body : Block) (origin : Goose.Core.OriginId)
      (firstChild : FuelSupport config fuel (.value environment first))
      (lastChild : FuelSupport config fuel (.value environment last))
      (loopChild : ∀ ty low high, FuelSupport config fuel (.rangeLoop environment localVar ty low high body)) :
      FuelSupport config (fuel + 1) (.statement environment (.forRange localVar first last body origin))
  | eachStatement (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId)
      (view : View) (byRef : Bool) (body : Block) (origin : Goose.Core.OriginId)
      (viewChild : FuelSupport config fuel (.view environment view))
      (loopChild : ∀ runtime, FuelSupport config fuel (.eachLoop environment localVar index byRef body runtime 0)) :
      FuelSupport config (fuel + 1) (.statement environment (.forEach localVar index view byRef body origin))
  | loopBody (fuel : Nat) (environment : RuntimeActivation) (body : Block)
      (child : FuelSupport config fuel (.block environment body)) :
      FuelSupport config (fuel + 1) (.loopBody environment body)
  | whileLoop (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (conditionChild : FuelSupport config fuel (.value environment condition))
      (bodyChild : FuelSupport config fuel (.loopBody environment body))
      (next : FuelSupport config fuel (.whileLoop environment condition body)) :
      FuelSupport config (fuel + 1) (.whileLoop environment condition body)
  | whileStatement (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block) (origin : Goose.Core.OriginId)
      (child : FuelSupport config fuel (.whileLoop environment condition body)) :
      FuelSupport config (fuel + 1) (.statement environment (.while condition body origin))
  | ifStatement (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes : Block) (no : Option Block)
      (origin : Goose.Core.OriginId) (child : FuelSupport config fuel (.value environment condition))
      (yesChild : FuelSupport config fuel (.block environment yes))
      (noChild : ∀ block, no = some block → FuelSupport config fuel (.block environment block)) :
      FuelSupport config (fuel + 1) (.statement environment (.ifS condition yes no origin))
  | boundActivationBody (fuel : Nat) (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt)
      (body : ∀ environment, FuelSupport config fuel (.statements environment statements)) :
      FuelSupport config (fuel + 1) (.boundActivationBody activation pre (.mk scope statements none))
  | boundActivationTail (fuel : Nat) (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt) (tail : Expr)
      (body : ∀ environment, FuelSupport config fuel (.statements environment statements))
      (tailChild : ∀ environment channels, FuelSupport config fuel (.producerWith environment channels tail)) :
      FuelSupport config (fuel + 1) (.boundActivationBody activation pre (.mk scope statements (some tail)))
  | boundActivationWithTail (fuel : Nat) (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt) (tail : Expr) (origin : Goose.Core.OriginId)
      (body : FuelSupport config fuel (.boundActivationBody activation pre (.mk scope statements (some tail)))) :
      FuelSupport config (fuel + 1) (.boundActivation activation pre (.mk scope statements (some tail)) origin)
  | boundActivation (fuel : Nat) (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt) (origin : Goose.Core.OriginId)
      (body : FuelSupport config fuel (.boundActivationBody activation pre (.mk scope statements none))) :
      FuelSupport config (fuel + 1) (.boundActivation activation pre (.mk scope statements none) origin)
  | argumentValue (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param)
      (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (child : FuelSupport config fuel (.value environment operand))
      (tail : FuelSupport config fuel (.arguments environment vars parameters arguments)) :
      FuelSupport config (fuel + 1) (.arguments environment vars (parameter :: parameters) (.byVal operand :: arguments))
  | argumentReference (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param)
      (parameters : List Param) (mutability : Goose.Core.Mutability) (place : Place) (arguments : List Arg)
      (child : FuelSupport config fuel (.place environment place))
      (tail : FuelSupport config fuel (.arguments environment vars parameters arguments)) :
      FuelSupport config (fuel + 1) (.arguments environment vars (parameter :: parameters) (.byRef mutability place :: arguments))
  | argumentConstruct (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param)
      (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (materialized : FuelSupport config fuel (.value environment operand))
      (direct : ∀ destination, FuelSupport config fuel (.builder environment destination operand))
      (tail : FuelSupport config fuel (.arguments environment vars parameters arguments)) :
      FuelSupport config (fuel + 1) (.arguments environment vars (parameter :: parameters) (.construct operand :: arguments))
  | callWith (fuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (arguments : List Arg)
      (origin : Goose.Core.OriginId) (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (argumentsSupported : FuelSupport config fuel (.arguments environment implementation.vars implementation.params.toList arguments))
      (body : ∀ act pre, FuelSupport config fuel
        (.boundActivation ⟨context.impl, act, implementation.vars, [], []⟩ pre implementation.body origin)) :
      FuelSupport config (fuel + 1) (.callWith environment contextId arguments origin)
  | defaultBuilder (fuel : Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId)
      (expression : Expr) (shape : DefaultBuilderExpression expression) (child : FuelSupport config fuel (.value environment expression)) :
      FuelSupport config (fuel + 1) (.builder environment incoming expression)
  | scalarBuilder (fuel : Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId)
      (expression : Expr) (scalar : ScalarExpression expression) (child : FuelSupport config fuel (.value environment expression)) :
      FuelSupport config (fuel + 1) (.builder environment incoming expression)
  | supportedBuilder (fuel : Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId)
      (expression : Expr) (supported : SupportedValue expression)
      (valueChild : FuelSupport config fuel (.value environment (supportedBuilderOperand expression)))
      (builderChild : ∀ source, FuelSupport config fuel (.builder environment source (supportedBuilderOperand expression))) :
      FuelSupport config (fuel + 1) (.builder environment incoming expression)
  | valueProducer (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (expression : Expr) (shape : ValueProducerExpression expression)
      (valueChild : FuelSupport config fuel (.value environment expression))
      (builderChild : ∀ destination, FuelSupport config fuel (.builder environment destination expression)) :
      FuelSupport config (fuel + 1) (.producerWith environment channels expression)
  | producerChannelCall (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (callee : ∀ selected, FuelSupport config fuel (.channelCall environment context arguments selected origin)) :
      FuelSupport config (fuel + 1) (.producerWith environment channels (.call context arguments origin))
  | valueChannelCall (fuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
      (arguments : List Arg) (origin : Goose.Core.OriginId)
      (callee : ∀ channels, FuelSupport config fuel (.channelCall environment context arguments channels origin)) :
      FuelSupport config (fuel + 1) (.value environment (.call context arguments origin))
  | channelCall (fuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
      (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
      (argumentChild : ∀ id implementation start lookupReady,
        getImplementation config context start = .ok (id, implementation) lookupReady →
        FuelSupport config fuel (.arguments environment implementation.vars implementation.params.toList arguments))
      (activationChild : ∀ id implementation start lookupReady act pre callableChannels,
        getImplementation config context start = .ok (id, implementation) lookupReady →
        FuelSupport config fuel (.boundActivation ⟨id, act, implementation.vars, [], callableChannels⟩ pre implementation.body origin)) :
      FuelSupport config (fuel + 1) (.channelCall environment context arguments channels origin)
  | valueCallWith (fuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (arguments : List Arg)
      (origin : Goose.Core.OriginId) (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (callee : FuelSupport config fuel (.callWith environment contextId arguments origin)) :
      FuelSupport config (fuel + 1) (.value environment (.call contextId arguments origin))
  | producerCallWith (fuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (arguments : List Arg)
      (origin : Goose.Core.OriginId) (callee : FuelSupport config fuel (.callWith environment contextId arguments origin)) :
      FuelSupport config (fuel + 1) (.producer environment (.call contextId arguments origin))
  | callOne (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[]) :
      FuelSupport config 1 (.call environment contextId origin)
  | call (fuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
      (body : ∀ act, FuelSupport config (fuel + 1)
        (.activation ⟨context.impl, act, implementation.vars, [], []⟩ implementation.body origin)) :
      FuelSupport config (fuel + 2) (.call environment contextId origin)
  | valueCall (fuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (callee : FuelSupport config fuel (.call environment contextId origin)) :
      FuelSupport config (fuel + 1) (.value environment (.call contextId [] origin))

theorem fuelHistory_exists (fuel : Nat) (config : EvalConfig) {α : Type} (operation : SourceOperation α)
    (path : List Nat) (before : ExecutionState) (supported : FuelSupport config fuel operation) :
    SourceHistory config fuel path operation before (execute fuel config operation before) := by
  induction fuel generalizing α operation path before with
  | zero =>
      cases operation <;> simpa [execute, evalValue, execStmt, execStmts, execBlock, execResultBlock, execResultBlockWith, execActivationBody,
        enterActivation, invokeCall, evalArguments, evalBound, evalPlace, evalView, execWhile, execRange, execEach, Goose.Construct.loopBody, evalPrintArg, buildExpr, buildElement, evalProduce, evalOperands, Goose.Construct.timeout, EvalM.stop] using
        (SourceHistory.timeout path _ before)
  | succ fuel ih =>
      cases supported with
      | legacy fuel supported => exact history_exists (fuel + 1) config _ path before supported
      | readValue _ environment place child =>
          exact .readValue (ih (.place environment place) (path ++ [0]) before child)
      | referenceValue _ environment mutability place child =>
          exact .referenceValue (ih (.place environment place) (path ++ [0]) before child)
      | lengthValue _ environment view child =>
          exact .lengthValue (ih (.view environment view) (path ++ [0]) before child)
      | printArgumentExpression _ environment expression child =>
          exact .printArgumentExpression (ih (.value environment expression) (path ++ [0]) before child)
      | printArgumentView _ environment view child =>
          exact .printArgumentView (ih (.view environment view) (path ++ [0]) before child)
      | printArguments _ environment arguments origin childrenSupported =>
          refine .printArguments fuel path environment arguments origin before ?_
          intro outcome visits replay visit member
          have inMapped : visit.operand ∈ visits.map Goose.Proofs.ConstructionInvocationReplay.Invocation.operand := List.mem_map_of_mem member
          rw [replay.sourceOrder] at inMapped
          have inArguments : visit.operand ∈ arguments := List.mem_of_mem_take inMapped
          have child := ih (.printArgument environment visit.operand) (path ++ [visit.ordinal]) visit.before
            (childrenSupported visit.operand inArguments)
          simp only [execute] at child
          rw [← Goose.Proofs.ConstructionGhostInvocation.visit_executes replay visit member]
          exact child
      | expressionBound _ environment count defaultValue operand fromEnd child =>
          exact .expressionBound (ih (.value environment operand) (path ++ [0]) before child)
      | sliceValue _ environment mutability view lo hi origin viewSupported loSupported hiSupported =>
          refine .sliceValue (ih (.view environment view) (path ++ [0]) before viewSupported) ?_ ?_
          · intro value middle viewed
            exact ih (.bound environment value.count 0 lo) (path ++ [1]) middle (loSupported _ _)
          · intro value middle low ready viewed lowResult
            exact ih (.bound environment value.count value.count hi) (path ++ [2]) ready (hiSupported _ _)
      | popValue _ environment place origin child =>
          exact .popValue (ih (.place environment place) (path ++ [0]) before child)
      | valueView _ environment operand child =>
          exact .valueView (ih (.value environment operand) (path ++ [0]) before child)
      | aggregate _ environment expression operands shape childrenSupported =>
          refine .aggregate fuel path environment expression operands before shape ?_
          intro outcome visits replay visit member
          have inMapped : visit.operand ∈ visits.map Goose.Proofs.ConstructionInvocationReplay.Invocation.operand := List.mem_map_of_mem member
          rw [replay.sourceOrder] at inMapped
          have inOperands : visit.operand ∈ operands := List.mem_of_mem_take inMapped
          have child := ih (.value environment visit.operand) (path ++ [visit.ordinal]) visit.before
            (childrenSupported visit.operand inOperands)
          simp only [execute] at child
          rw [← Goose.Proofs.ConstructionGhostInvocation.visit_executes replay visit member]
          exact child
      | unary _ environment operation operand origin childSupported =>
          exact .unary (ih (.value environment operand) (path ++ [0]) before childSupported)
      | conversion _ environment kind target operand origin childSupported =>
          exact .conversion (ih (.value environment operand) (path ++ [0]) before childSupported)
      | negation _ environment operand childSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          have actual : evalValue (fuel + 1) config environment (.not operand) before =
              negationResult (evalValue fuel config environment operand before) := by
            simp only [evalValue, bind, negationResult]
            cases evalValue fuel config environment operand before <;> rfl
          simp only [execute] at child ⊢
          rw [actual]
          exact .negation child
      | comparison _ environment operation first second leftSupported rightSupported =>
          refine .comparison (ih (.value environment first) (path ++ [0]) before leftSupported) ?_
          intro value middle result
          exact ih (.value environment second) (path ++ [1]) middle rightSupported
      | binary _ environment operation first second origin leftSupported rightSupported =>
          refine .binary (ih (.value environment first) (path ++ [0]) before leftSupported) ?_
          intro value middle ty number ready result checked
          exact ih (.value environment second) (path ++ [1]) ready rightSupported
      | logical _ environment isAnd first second leftSupported rightSupported =>
          refine .logical (ih (.value environment first) (path ++ [0]) before leftSupported) ?_
          intro value middle ready result checked
          exact ih (.value environment second) (path ++ [1]) ready rightSupported
      | valueNonfixedArray _ environment ty operands origin nonfixed childSupported =>
          refine .valueNonfixedArray fuel path environment ty operands origin before nonfixed ?_
          intro destination ready allocated
          exact ih (.builder environment destination (.arrLit ty operands origin)) (path ++ [0]) ready (childSupported destination)
      | builderArray _ environment incoming ty operands origin childrenSupported =>
          refine .builderArray fuel path environment incoming ty operands origin before ?_
          intro current prepared ready pending element outcome visits renewed found elementFound replay visit member
          have inMapped : visit.operand ∈ visits.map Goose.Proofs.ConstructionInvocationReplay.Invocation.operand := List.mem_map_of_mem member
          rw [replay.sourceOrder] at inMapped
          have inOperands := List.mem_of_mem_take inMapped
          have child := ih (.element environment current element visit.operand) (path ++ [visit.ordinal]) visit.before
            (childrenSupported visit.operand inOperands current element)
          simp only [execute] at child
          rw [← Goose.Proofs.ConstructionGhostInvocation.visit_executes replay visit member]
          exact child
      | element _ environment parent element operand valueSupported builderSupported =>
          cases fixed : element.nonfixed with
          | false =>
              have child := ih (.value environment operand) (path ++ [0]) before valueSupported
              simp only [execute] at child ⊢
              rw [Goose.Proofs.ConstructionGhostElements.fixedElement_execution fuel config environment parent element operand before fixed]
              exact .fixedElement fixed child
          | true =>
              refine .nonfixedElement fixed ?_
              intro layout layoutReady destination ready layoutResult opened
              exact ih (.builder environment destination operand) (path ++ [0]) ready (builderSupported destination)
      | valueNonfixedFill _ environment element count operand origin nonfixed childSupported =>
          refine .valueNonfixedFill fuel path environment element count operand origin before nonfixed ?_
          intro destination ready allocated
          exact ih (.builder environment destination (.fill (.arr element count) operand origin)) (path ++ [0]) ready (childSupported destination)
      | builderChannelCall _ environment incoming context arguments origin childSupported =>
          refine .builderChannelCall fuel path environment incoming context arguments origin before ?_
          intro destination ready renewed
          exact ih (.channelCall environment context arguments [.construct destination] origin) (path ++ [0]) ready (childSupported destination)
      | builderSingleValue _ environment incoming operand childSupported =>
          refine .builderSingleValue fuel path environment incoming operand before ?_
          intro destination ready renewed
          exact ih (.builder environment destination operand) (path ++ [0]) ready (childSupported destination)
      | builderBlock _ environment incoming block origin childSupported =>
          refine .builderBlock fuel path environment incoming block origin before ?_
          intro destination ready renewed
          exact ih (.resultBlock environment [.construct destination] block) (path ++ [0])
            (blockProducerStart environment [.construct destination] ready) (childSupported destination)
      | builderConditional _ environment incoming condition yes no origin conditionSupported yesSupported noSupported =>
          refine .builderConditional fuel path environment incoming condition yes no origin before ?_ ?_
          · intro destination ready renewed
            exact ih (.value environment condition) (path ++ [0]) ready conditionSupported
          · intro destination ready value middle selected selectedState renewed evaluated boolean
            cases selected with
            | false => exact ih (.resultBlock environment [.construct destination] no) (path ++ [1]) selectedState (noSupported destination)
            | true => exact ih (.resultBlock environment [.construct destination] yes) (path ++ [1]) selectedState (yesSupported destination)
      | fillBuilder _ environment destination element count operand origin valueSupported builderSupported =>
          refine .fillBuilder fuel path environment destination element count operand origin before ?_ ?_
          · intro current ready renewed fixed
            exact ih (.value environment operand) (path ++ [0]) ready valueSupported
          · intro current ready source allocated renewed nonfixed made
            exact ih (.builder environment source operand) (path ++ [0]) allocated (builderSupported source)
      | fill _ environment element count origin operand fixed childSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          have actual : evalValue (fuel + 1) config environment (.fill (.arr element count) operand origin) before =
              Goose.Proofs.ConstructionGhostSourceTransition.fillResult count
                (evalValue fuel config environment operand before) := by
            simp only [evalValue, fixed, Bool.false_eq_true, ↓reduceIte, bind,
              Goose.Proofs.ConstructionGhostSourceTransition.fillResult]
            cases evalValue fuel config environment operand before <;> rfl
          simp only [execute] at child ⊢
          rw [actual]
          exact .fill fixed child
      | valueBlockProducer _ environment block origin childSupported =>
          refine .valueBlockProducer fuel path environment block origin before ?_
          intro types channels ready typesFound prepared
          exact ih (.producerWith environment channels (.blockE block origin)) (path ++ [0]) ready (childSupported channels)
      | producerValues _ environment channels operands childSupported =>
          refine .producerValues fuel path environment channels operands before ?_
          intro planned ready prepared
          exact ih (.producerOperands environment planned operands) (path ++ [0]) ready (childSupported planned)
      | producerOperandsEmpty _ environment => exact .producerOperandsEmpty fuel path environment before
      | producerOperandsNoChannels _ environment operand operands => exact .producerOperandsNoChannels fuel path environment operand operands before
      | producerOperandsNoValues _ environment channel channels => exact .producerOperandsNoValues fuel path environment channel channels before
      | producerOperandsCons _ environment channel channels operand operands headSupported tailSupported =>
          refine .producerOperandsCons fuel path environment channel channels operand operands before
            (ih (.producerWith environment [channel] operand) (path ++ [0]) before headSupported) ?_
          intro carriers middle carrier ready produced selected
          exact ih (.producerOperands environment channels operands) (path ++ [1]) ready tailSupported
      | producerConditional _ environment channels condition yes no origin conditionSupported yesSupported noSupported =>
          refine .producerConditional fuel path environment channels condition yes no origin before ?_ ?_
          · intro planned ready prepared
            exact ih (.value environment condition) (path ++ [0]) ready conditionSupported
          · intro planned ready value middle selected selectedState prepared evaluated boolean
            cases selected with
            | false => exact ih (.resultBlock environment planned no) (path ++ [1]) selectedState (noSupported planned)
            | true => exact ih (.resultBlock environment planned yes) (path ++ [1]) selectedState (yesSupported planned)
      | producerBlock _ environment channels block origin childSupported =>
          refine .producerBlock fuel path environment channels block origin before ?_
          intro planned ready prepared
          exact ih (.resultBlock environment planned block) (path ++ [0]) (blockProducerStart environment planned ready) (childSupported planned)
      | resultBlock _ environment channels block childSupported =>
          exact .resultBlock fuel path environment channels block before
            (ih (.resultBlockWith environment [] channels block) (path ++ [0]) before childSupported)
      | resultBlockWith _ environment pre channels scope statements tail bodySupported tailSupported =>
          refine .resultBlockWith fuel path environment pre channels scope statements tail before ?_ ?_
          · intro ready bound
            exact ih (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements)
              (path ++ [0]) ready (bodySupported _)
          · intro expression ready value after tailEq bound bodyResult
            exact ih (.producerWith { environment with scopes := (scope, before.nextScope) :: environment.scopes } channels expression)
              (path ++ [1]) after (tailSupported _ expression tailEq)
      | conditional _ environment condition yes no origin conditionSupported yesSupported noSupported =>
          have child := ih (.value environment condition) (path ++ [0]) before conditionSupported
          have branch : ∀ value middle selected ready,
              evalValue fuel config environment condition before = .ok value middle → expectBool value middle = .ok selected ready →
              SourceHistory config fuel (path ++ [if selected then 1 else 2])
                (.block environment (if selected then yes else no)) ready
                (execBlock fuel config environment [] [] (if selected then yes else no) ready) := by
            intro value middle selected ready _ _
            cases selected with
            | false => exact ih (.block environment no) (path ++ [2]) ready noSupported
            | true => exact ih (.block environment yes) (path ++ [1]) ready yesSupported
          have actual : evalValue (fuel + 1) config environment (.ifE condition yes no origin) before =
              conditionalResult fuel config environment yes no (evalValue fuel config environment condition before) := by
            simp only [evalValue, bind, conditionalResult]
            cases result : evalValue fuel config environment condition before with
            | ok value state =>
                simp only
                cases check : expectBool value state with
                | ok selected ready => simp only [check]; cases selected <;> rfl
                | stop | escape | jump => simp only [check]
            | stop | escape | jump => rfl
          simp only [execute]
          rw [actual]
          exact .conditional child branch
      | blockTail _ environment scope statements expression bodySupported tailSupported =>
          refine .blockTail fuel path environment scope statements expression before ?_ ?_
          · exact ih (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements)
              (path ++ [0]) { before with nextScope := before.nextScope + 1 } (bodySupported _)
          · intro value ready result
            exact ih (.value { environment with scopes := (scope, before.nextScope) :: environment.scopes } expression)
              (path ++ [1]) ready (tailSupported _)
      | valueFirstStatement _ environment statement expression shape child =>
          exact .valueFirstStatement fuel path environment statement expression before shape
            (ih (.value environment expression) (path ++ [0]) before child)
      | leafStatement _ environment statement shape =>
          exact .leafStatement fuel path environment statement before shape
      | assignment _ environment place expression origin placeSupported valueSupported =>
          refine .assignment fuel path environment place expression origin before
            (ih (.place environment place) (path ++ [0]) before placeSupported) ?_
          intro location ready placed
          exact ih (.value environment expression) (path ++ [1]) ready valueSupported
      | declaration _ environment localVar expression origin valueSupported builderSupported =>
          refine .declaration fuel path environment localVar expression origin before ?_ ?_ ?_ ?_
          · intro descriptor root ready found fixed rootResult
            exact ih (.value environment expression) (path ++ [0]) ready valueSupported
          · intro descriptor root rootReady implementation ready count found nonfixed rootResult implementationFound fallback materialized
            exact ih (.value environment expression) (path ++ [0]) ready valueSupported
          · intro descriptor root rootReady implementation ready destination buildReady found nonfixed rootResult implementationFound fallback direct allocated
            exact ih (.builder environment destination expression) (path ++ [0]) buildReady (builderSupported destination)
          · intro descriptor root rootReady implementation result index incoming selected selectedReady pending ready destination renewedReady buildReady
                found nonfixed rootResult implementationFound named channel renewed queried valueRequest renewedAgain prepared
            exact ih (.builder environment destination expression) (path ++ [0]) buildReady (builderSupported destination)
      | expression _ environment operand origin childSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          have actual : execStmt (fuel + 1) config environment (.expr operand origin) before =
              Goose.Proofs.ConstructionGhostSourceTransition.expressionStatementResult
                (evalValue fuel config environment operand before) := by
            simp only [execStmt, bind, Goose.Proofs.ConstructionGhostSourceTransition.expressionStatementResult]
            cases evalValue fuel config environment operand before <;> rfl
          simp only [execute] at child ⊢
          rw [actual]
          exact .expression child
      | sequence _ environment statement rest headSupported tailSupported =>
          have head := ih (.statement environment statement) (path ++ [0]) before headSupported
          have tail : ∀ value middle, execStmt fuel config environment statement before = .ok (.normal value) middle →
              SourceHistory config fuel (path ++ [1]) (.statements environment rest) middle
                (execStmts fuel config environment rest middle) := by
            intro value middle _
            exact ih (.statements environment rest) (path ++ [1]) middle tailSupported
          have actual : execStmts (fuel + 1) config environment (statement :: rest) before =
              Goose.Proofs.ConstructionGhostSourceTransition.sequenceResult fuel config environment rest
                (execStmt fuel config environment statement before) := by
            simp only [execStmts, bind, Goose.Proofs.ConstructionGhostSourceTransition.sequenceResult]
            cases execStmt fuel config environment statement before with
            | ok flow state => cases flow <;> rfl
            | stop | escape | jump => rfl
          simp only [execute] at head ⊢
          rw [actual]
          exact .next head tail
      | activationBody _ activation scope statements bodySupported =>
          let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
          let ready := Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation scope before
          have child := ih (.statements environment statements) (path ++ [0]) ready (bodySupported environment)
          simp only [execute] at child ⊢
          rw [activationBody_source]
          exact .activationBody child
      | activation _ activation scope statements origin bodySupported =>
          have body : ∀ implementation, config.module.impls[activation.implementation]? = some implementation →
              SourceHistory config fuel (path ++ [0]) (.activationBody activation (.mk scope statements none)) before
                (execActivationBody fuel config activation [] (.mk scope statements none) before) := by
            intro implementation _
            exact ih (.activationBody activation (.mk scope statements none)) (path ++ [0]) before bodySupported
          simp only [execute]
          rw [activationEnter_source]
          exact .activation body
      | dereferencePlace _ environment operand childSupported =>
          exact .dereferencePlace (ih (.value environment operand) (path ++ [0]) before childSupported)
      | fieldPlace _ environment owner index childSupported =>
          exact .fieldPlace (ih (.place environment owner) (path ++ [0]) before childSupported)
      | elementPlace _ environment view operand origin viewSupported indexSupported =>
          refine .elementPlace (ih (.view environment view) (path ++ [0]) before viewSupported) ?_
          intro value ready viewed
          exact ih (.value environment operand) (path ++ [1]) ready indexSupported
      | block _ environment scope statements bodySupported =>
          let scopedEnvironment := { environment with scopes := (scope, before.nextScope) :: environment.scopes }
          let ready := { before with nextScope := before.nextScope + 1 }
          have child := ih (.statements scopedEnvironment statements) (path ++ [0]) ready (bodySupported scopedEnvironment)
          have bound : bindAll environment.act before.nextScope [] ready = .ok () ready := by simp [ready, bindAll, bind, pure]
          obtain ⟨outcome, visits, replay, execution⟩ :=
            Goose.Proofs.ConstructionGhostBlock.execBlock_statementReplay fuel config environment [] [] scope statements none before ready bound
          simp only [execute]
          rw [execution, ← replay.sound]
          exact .block child
      | placeView _ environment place childSupported =>
          exact .placeView (ih (.place environment place) (path ++ [0]) before childSupported)
      | boundBlock _ environment pre scope statements bodySupported =>
          refine .boundBlock ?_
          intro ready bound
          exact ih (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements)
            (path ++ [0]) ready (bodySupported _)
      | boundLoopBody _ environment pre body childSupported =>
          exact .boundLoopBody (ih (.blockWith environment pre body) (path ++ [0]) (loopStart environment before) childSupported)
      | eachLoop _ environment localVar index byRef body view current bodySupported nextSupported =>
          simp only [execute]
          rw [Goose.Proofs.ConstructionGhostEachCore.eachCount_source]
          refine .eachLoop ?_ ?_
          · intro count countReady pre ready counted inside selected
            exact ih (.loopBodyWith environment pre body) (path ++ [0]) ready (bodySupported pre)
          · intro count countReady pre ready flow after counted inside selected result continuing
            exact ih (.eachLoop environment localVar index byRef body view (current + 1)) (path ++ [1]) after nextSupported
      | rangeLoop _ environment localVar ty first last body bodySupported nextSupported =>
          refine .rangeLoop ?_ ?_
          · intro inside
            exact ih (.loopBodyWith environment [(localVar, .int ty first)] body) (path ++ [0]) before (bodySupported _)
          · intro flow after inside result continuing
            exact ih (.rangeLoop environment localVar ty (first + 1) last body) (path ++ [1]) after nextSupported
      | rangeStatement _ environment localVar first last body origin firstSupported lastSupported loopSupported =>
          refine .rangeStatement (ih (.value environment first) (path ++ [0]) before firstSupported) ?_ ?_
          · intro firstValue middle ty low ready firstResult checked
            exact ih (.value environment last) (path ++ [1]) ready lastSupported
          · intro firstValue middle ty low ready lastValue lastState otherTy high checked final firstResult checkedFirst lastResult checkedLast same
            exact ih (.rangeLoop environment localVar ty low high body) (path ++ [2]) final (loopSupported ty low high)
      | eachStatement _ environment localVar index view byRef body origin viewSupported loopSupported =>
          refine .eachStatement (ih (.view environment view) (path ++ [0]) before viewSupported) ?_
          intro runtime ready result
          exact ih (.eachLoop environment localVar index byRef body runtime 0) (path ++ [1]) ready (loopSupported runtime)
      | loopBody _ environment body childSupported =>
          exact .loopBody (ih (.block environment body) (path ++ [0]) (loopStart environment before) childSupported)
      | whileLoop _ environment condition body conditionSupported bodySupported nextSupported =>
          refine .whileLoop (ih (.value environment condition) (path ++ [0]) before conditionSupported) ?_ ?_
          · intro value middle ready result checked
            exact ih (.loopBody environment body) (path ++ [1]) ready bodySupported
          · intro value middle ready flow after result checked loopResult continuing
            exact ih (.whileLoop environment condition body) (path ++ [2]) after nextSupported
      | whileStatement _ environment condition body origin childSupported =>
          exact .whileStatement (ih (.whileLoop environment condition body) (path ++ [0]) before childSupported)
      | ifStatement _ environment condition yes no origin childSupported yesSupported noSupported =>
          refine .ifStatement (ih (.value environment condition) (path ++ [0]) before childSupported) ?_ ?_
          · intro value middle ready result checked
            exact ih (.block environment yes) (path ++ [1]) ready yesSupported
          · intro value middle ready block result checked selected
            exact ih (.block environment block) (path ++ [2]) ready (noSupported block selected)
      | boundActivationBody _ activation pre scope statements bodySupported =>
          simp only [execute]
          rw [boundActivationBody_source]
          refine .boundActivationBody ?_
          intro ready bound
          exact ih (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements)
            (path ++ [0]) ready (bodySupported _)
      | boundActivationTail _ activation pre scope statements tail bodySupported tailSupported =>
          refine .boundActivationTail fuel path activation pre scope statements tail before ?_ ?_
          · intro ready bound
            exact ih (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements)
              (path ++ [0]) ready (bodySupported _)
          · intro ready value after planned tokens prepared bound body setup
            exact ih (.producerWith { activation with scopes := (scope, before.nextScope) :: activation.scopes } planned tail)
              (path ++ [1]) prepared (tailSupported _ planned)
      | boundActivationWithTail _ activation pre scope statements tail origin bodySupported =>
          refine .boundActivation ?_
          intro implementation found
          exact ih (.boundActivationBody activation pre (.mk scope statements (some tail))) (path ++ [0]) before bodySupported
      | boundActivation _ activation pre scope statements origin bodySupported =>
          refine .boundActivation ?_
          intro implementation found
          exact ih (.boundActivationBody activation pre (.mk scope statements none)) (path ++ [0]) before bodySupported
      | argumentValue _ environment vars parameter parameters operand arguments childSupported tailSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          have tail : ∀ value middle, evalValue fuel config environment operand before = .ok value middle →
              SourceHistory config fuel (path ++ [1]) (.arguments environment vars parameters arguments) middle
                (evalArguments fuel config environment vars parameters arguments middle) := by
            intro value middle _
            exact ih (.arguments environment vars parameters arguments) (path ++ [1]) middle tailSupported
          simp only [execute]
          rw [valueArgument_source]
          exact .argumentValue child tail
      | argumentReference _ environment vars parameter parameters mutability place arguments childSupported tailSupported =>
          refine .argumentReference (ih (.place environment place) (path ++ [0]) before childSupported) ?_
          intro location middle result
          exact ih (.arguments environment vars parameters arguments) (path ++ [1]) middle tailSupported
      | argumentConstruct _ environment vars parameter parameters operand arguments materializedSupported directSupported tailSupported =>
          refine .argumentConstruct ?_ ?_ ?_
          · intro localVar count found query
            exact ih (.value environment operand) (path ++ [0]) before materializedSupported
          · intro localVar destination ready found query allocated
            exact ih (.builder environment destination operand) (path ++ [0]) ready (directSupported destination)
          · intro value middle result
            exact ih (.arguments environment vars parameters arguments) (path ++ [1]) middle tailSupported
      | callWith _ environment contextId arguments origin context implementation contextFound implementationFound resultsEmpty argumentsSupported bodySupported =>
          have argumentsHistory := ih (.arguments environment implementation.vars implementation.params.toList arguments)
            (path ++ [0]) before argumentsSupported
          have activationHistory : ∀ values ready,
              evalArguments fuel config environment implementation.vars implementation.params.toList arguments before = .ok values ready →
              ready.activations.length < Goose.Core.maxCallDepth →
              let activation : RuntimeActivation := ⟨context.impl, ready.nextAct, implementation.vars, [], []⟩
              let activated := { ready with nextAct := ready.nextAct + 1, activations := activation :: ready.activations }
              let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
              SourceHistory config fuel (path ++ [1]) (.boundActivation activation pre implementation.body origin) activated
                (enterActivation fuel config activation pre implementation.body origin activated) := by
            intro values ready result depth
            exact ih _ _ _ (bodySupported ready.nextAct _)
          simp only [execute] at argumentsHistory ⊢
          rw [callWith_source fuel config environment contextId arguments origin context implementation before
            contextFound implementationFound resultsEmpty]
          exact .callWith contextFound implementationFound resultsEmpty argumentsHistory activationHistory
      | defaultBuilder _ environment incoming expression shape childSupported =>
          refine .defaultBuilder fuel path environment incoming expression before shape ?_
          intro destination ready renewed
          exact ih (.value environment expression) (path ++ [0]) ready childSupported
      | scalarBuilder _ environment incoming expression scalar childSupported =>
          refine .scalarBuilder fuel path environment incoming expression before scalar ?_
          intro destination ready renewed
          exact ih (.value environment expression) (path ++ [0]) ready childSupported
      | supportedBuilder _ environment incoming expression supported valueSupported builderSupported =>
          refine .supportedBuilder fuel path environment incoming expression before supported ?_ ?_
          · intro destination ready renewed needsValue
            exact ih (.value environment (supportedBuilderOperand expression)) (path ++ [0]) ready valueSupported
          · intro destination ready element count operand origin source allocated renewed shape nonfixed made
            subst expression
            exact ih (.builder environment source operand) (path ++ [0]) allocated (by simpa [supportedBuilderOperand] using builderSupported source)
      | valueProducer _ environment channels expression shape valueSupported builderSupported =>
          refine .valueProducer fuel path environment channels expression before shape ?_ ?_
          · intro selected ready prepared valueShape
            exact ih (.value environment expression) (path ++ [0]) ready valueSupported
          · intro destination ready prepared
            exact ih (.builder environment destination expression) (path ++ [0]) ready (builderSupported destination)
      | producerChannelCall _ environment channels context arguments origin calleeSupported =>
          refine .producerChannelCall fuel path environment channels context arguments origin before ?_
          intro selected ready prepared
          exact ih (.channelCall environment context arguments selected origin) (path ++ [0]) ready (calleeSupported selected)
      | valueChannelCall _ environment context arguments origin calleeSupported =>
          refine .valueChannelCall fuel path environment context arguments origin before ?_
          intro id implementation lookupReady channels ready lookup prepared
          exact ih (.channelCall environment context arguments channels origin) (path ++ [0]) ready (calleeSupported channels)
      | channelCall _ environment context arguments channels origin argumentSupported activationSupported =>
          refine .channelCall fuel path environment context arguments channels origin before ?_ ?_
          · intro id implementation lookupReady callableChannels ready lookup arity prepared
            exact ih (.arguments environment implementation.vars implementation.params.toList arguments) (path ++ [0]) ready
              (argumentSupported id implementation before lookupReady lookup)
          · intro id implementation lookupReady callableChannels argumentsReady values valuesReady refreshed activationReady
              lookup arity prepared argumentsResult refresh depth
            exact ih (.boundActivation ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
                ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)) implementation.body origin)
              (path ++ [1]) _ (activationSupported id implementation before lookupReady activationReady.nextAct _ refreshed lookup)
      | valueCallWith _ environment contextId arguments origin context implementation contextFound implementationFound resultsEmpty callee =>
          have child := ih (.callWith environment contextId arguments origin) (path ++ [0]) before callee
          simp only [execute] at child ⊢
          rw [valueCallWith_source fuel config environment contextId arguments context implementation origin before
            contextFound implementationFound resultsEmpty]
          exact .valueCallWith contextFound implementationFound resultsEmpty child
      | producerCallWith _ environment contextId arguments origin callee =>
          have child := ih (.callWith environment contextId arguments origin) (path ++ [0]) before callee
          simp only [execute] at child ⊢
          rw [producerCallWith_source]
          exact .producerCallWith child
      | callOne environment contextId origin context implementation contextFound implementationFound resultsEmpty =>
          simpa only [execute, emptyCall_one config environment contextId context implementation origin before
            contextFound implementationFound resultsEmpty] using
            (SourceHistory.callOne contextFound implementationFound resultsEmpty :
              SourceHistory config 1 path (.call environment contextId origin) before _)
      | call fuel environment contextId origin context implementation contextFound implementationFound parametersEmpty resultsEmpty body =>
          by_cases depth : before.activations.length < Goose.Core.maxCallDepth
          · let activation : RuntimeActivation := ⟨context.impl, before.nextAct, implementation.vars, [], []⟩
            let activated := { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
            have child := ih (.activation activation implementation.body origin) (path ++ [0]) activated (body before.nextAct)
            have actual := emptyCall_enter fuel config environment contextId context implementation origin before
              contextFound implementationFound parametersEmpty resultsEmpty depth
            simp only [execute] at child ⊢
            rw [actual]
            have delivered : (enterActivation (fuel + 1) config activation [] implementation.body origin >>= fun carriers =>
                deliverCarriers (fuel + 1) config.layout [] carriers origin) activated =
                callDeliveryResult (fuel + 1) config origin
                  (enterActivation (fuel + 1) config activation [] implementation.body origin activated) := by
              simp only [bind, callDeliveryResult]
              cases enterActivation (fuel + 1) config activation [] implementation.body origin activated <;> rfl
            rw [delivered]
            exact SourceHistory.callEnter contextFound implementationFound parametersEmpty resultsEmpty depth child
          · have full : Goose.Core.maxCallDepth ≤ before.activations.length := Nat.le_of_not_gt depth
            simpa only [execute, emptyCall_depth fuel config environment contextId context implementation origin before
              contextFound implementationFound parametersEmpty resultsEmpty full] using
              (SourceHistory.callDepth contextFound implementationFound parametersEmpty resultsEmpty full :
                SourceHistory config (fuel + 2) path (.call environment contextId origin) before _)
      | valueCall _ environment contextId origin context implementation contextFound implementationFound resultsEmpty callee =>
          have child := ih (.call environment contextId origin) (path ++ [0]) before callee
          simp only [execute] at child ⊢
          rw [valueCall_source fuel config environment contextId context implementation origin before
            contextFound implementationFound resultsEmpty]
          exact .valueCall contextFound implementationFound resultsEmpty child

private def recursiveContext : Context := ⟨0, "recursive", [], [], []⟩
private def recursiveImplementation : Impl := ⟨"recursive", #[], #[], #[],
  .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0, .expr (.fill (.arr .unit 3) (.call 0 [] 0) 0) 0] none, .unknown⟩
private def recursiveConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[recursiveImplementation], #[recursiveContext], 0, #[], #[], #[]⟩⟩

theorem recursiveCall_supported (fuel : Nat) : ∀ environment,
    FuelSupport recursiveConfig fuel (.call environment 0 0) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro environment
    cases fuel with
    | zero => exact .timeout _
    | succ fuel =>
      cases fuel with
      | zero => exact .callOne environment 0 0 recursiveContext recursiveImplementation rfl rfl rfl
      | succ fuel =>
        apply FuelSupport.call fuel environment 0 0 recursiveContext recursiveImplementation rfl rfl rfl rfl
        intro act
        let activation : RuntimeActivation := ⟨0, act, #[], [], []⟩
        change FuelSupport recursiveConfig (fuel + 1)
          (.activation activation (.mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0, .expr (.fill (.arr .unit 3) (.call 0 [] 0) 0) 0] none) 0)
        cases fuel with
        | zero => exact .activation 0 activation 0 _ 0 (.timeout _)
        | succ fuel =>
          apply FuelSupport.activation (fuel + 1)
          apply FuelSupport.activationBody fuel
          intro scopedEnvironment
          cases fuel with
          | zero => exact .timeout _
          | succ fuel =>
            apply FuelSupport.sequence fuel
            · exact .legacy fuel (.expression scopedEnvironment 0 (.value scopedEnvironment
                (.fill (.int .i64) 3 0 rfl (.integer .i64 7))))
            · cases fuel with
              | zero => exact .timeout _
              | succ fuel =>
                apply FuelSupport.sequence fuel
                · cases fuel with
                  | zero => exact .timeout _
                  | succ fuel =>
                    apply FuelSupport.expression fuel
                    cases fuel with
                    | zero => exact .timeout _
                    | succ fuel =>
                      apply FuelSupport.fill fuel scopedEnvironment .unit 3 0 (.call 0 [] 0) rfl
                      cases fuel with
                      | zero => exact .timeout _
                      | succ fuel =>
                        apply FuelSupport.valueCall fuel scopedEnvironment 0 0 recursiveContext recursiveImplementation rfl rfl rfl
                        exact ih fuel (by omega) scopedEnvironment
                · exact .legacy fuel (.empty scopedEnvironment)

private def recursiveEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def recursiveState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem recursiveCall_history (fuel : Nat) :
    SourceHistory recursiveConfig fuel [] (.call recursiveEnvironment 0 0) .initial
      (invokeCall fuel recursiveConfig recursiveEnvironment 0 [] [] 0 .initial) :=
  fuelHistory_exists fuel recursiveConfig (.call recursiveEnvironment 0 0) [] .initial
    (recursiveCall_supported fuel recursiveEnvironment)

theorem recursiveCall_terminal : ∃ state,
    invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial = .stop .timeout state ∧
    1 < state.nextAct ∧
    SourceHistory recursiveConfig 15 [] (.call recursiveEnvironment 0 0) .initial (.stop .timeout state) := by
  refine ⟨recursiveState (invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial), ?_, ?_, ?_⟩
  · unfold recursiveState recursiveConfig recursiveContext recursiveImplementation recursiveEnvironment
    cbv
  · unfold recursiveState recursiveConfig recursiveContext recursiveImplementation recursiveEnvironment
    cbv
  · have actual : invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial =
        .stop .timeout (recursiveState (invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial)) := by
      unfold recursiveState recursiveConfig recursiveContext recursiveImplementation recursiveEnvironment
      cbv
    have history := recursiveCall_history 15
    rw [actual] at history
    exact history

def moduleCallResult : ExecutionStep (List Carrier) → ExecutionStep Unit
  | .ok carriers state => publishCarriers 0 carriers state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem recursiveModule_history (fuel : Nat) :
    ∃ outcome, SourceHistory recursiveConfig fuel [] (.call recursiveEnvironment 0 0) .initial outcome ∧
      runModule fuel recursiveConfig .initial = moduleCallResult outcome := by
  have history := recursiveCall_history fuel
  refine ⟨_, history, ?_⟩
  simp only [runModule, recursiveConfig, recursiveContext, recursiveImplementation, Array.size_empty, List.range_zero,
    initGlobals, getImplementation, Array.getElem?_singleton, channelsFor, Array.toList_empty, List.mapM_nil, bind, pure]
  change (invokeCall fuel recursiveConfig recursiveEnvironment 0 [] [] 0 >>= fun carriers =>
    publishCarriers 0 carriers) .initial = moduleCallResult
      (invokeCall fuel recursiveConfig recursiveEnvironment 0 [] [] 0 .initial)
  simp only [bind, moduleCallResult]
  cases invokeCall fuel recursiveConfig recursiveEnvironment 0 [] [] 0 .initial <;> rfl

theorem recursiveModule_terminal : ∃ state,
    runModule 15 recursiveConfig .initial = .stop .timeout state ∧ 1 < state.nextAct ∧
    SourceHistory recursiveConfig 15 [] (.call recursiveEnvironment 0 0) .initial (.stop .timeout state) := by
  obtain ⟨state, call, allocated, history⟩ := recursiveCall_terminal
  obtain ⟨outcome, moduleHistory, execution⟩ := recursiveModule_history 15
  have actual := moduleHistory.sound
  change invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial = outcome at actual
  rw [call] at actual
  subst outcome
  exact ⟨state, execution, allocated, history⟩

theorem recursiveParameter_supported (fuel : Nat) (config : EvalConfig) (contextId : Goose.Core.ContextId)
    (context : Context) (implementation : Impl) (parameter : Goose.Core.VarId) (ty : Goose.Core.IntTy) (number : Int)
    (scope : Nat) (callOrigin statementOrigin : Goose.Core.OriginId)
    (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (resultsEmpty : implementation.results = #[]) (parameters : implementation.params = #[⟨parameter, .byValue⟩])
    (body : implementation.body = .mk scope [.expr (.call contextId [.byVal (.lit ty number)] callOrigin) statementOrigin] none) :
    ∀ environment, FuelSupport config fuel (.callWith environment contextId [.byVal (.lit ty number)] callOrigin) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro environment
    cases fuel with
    | zero => exact .timeout _
    | succ fuel =>
      apply FuelSupport.callWith fuel environment contextId [.byVal (.lit ty number)] callOrigin context implementation
        contextFound implementationFound resultsEmpty
      · cases fuel with
        | zero => exact .timeout _
        | succ fuel =>
          have arguments : FuelSupport config (fuel + 1)
              (.arguments environment implementation.vars [⟨parameter, .byValue⟩] [.byVal (.lit ty number)]) :=
            .argumentValue fuel environment implementation.vars ⟨parameter, .byValue⟩ [] (.lit ty number) []
              (.legacy fuel (.value environment (.integer ty number))) (.legacy fuel (.argumentsDone environment _))
          simpa [parameters] using arguments
      · intro act pre
        let activation : RuntimeActivation := ⟨context.impl, act, implementation.vars, [], []⟩
        change FuelSupport config fuel (.boundActivation activation pre implementation.body callOrigin)
        rw [body]
        cases fuel with
        | zero => exact .timeout _
        | succ fuel =>
          apply FuelSupport.boundActivation fuel activation pre scope _ callOrigin
          cases fuel with
          | zero => exact .timeout _
          | succ fuel =>
            apply FuelSupport.boundActivationBody fuel
            intro scopedEnvironment
            cases fuel with
            | zero => exact .timeout _
            | succ fuel =>
              apply FuelSupport.sequence fuel
              · cases fuel with
                | zero => exact .timeout _
                | succ fuel =>
                  apply FuelSupport.expression fuel
                  cases fuel with
                  | zero => exact .timeout _
                  | succ fuel =>
                    apply FuelSupport.valueCallWith fuel scopedEnvironment contextId [.byVal (.lit ty number)] callOrigin
                      context implementation contextFound implementationFound resultsEmpty
                    exact ih fuel (by omega) scopedEnvironment
              · exact .legacy fuel (.empty scopedEnvironment)

theorem recursiveParameter_history (fuel : Nat) (config : EvalConfig) (contextId : Goose.Core.ContextId)
    (context : Context) (implementation : Impl) (parameter : Goose.Core.VarId) (ty : Goose.Core.IntTy) (number : Int)
    (scope : Nat) (callOrigin statementOrigin : Goose.Core.OriginId) (environment : RuntimeActivation)
    (path : List Nat) (before : ExecutionState)
    (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (resultsEmpty : implementation.results = #[]) (parameters : implementation.params = #[⟨parameter, .byValue⟩])
    (body : implementation.body = .mk scope [.expr (.call contextId [.byVal (.lit ty number)] callOrigin) statementOrigin] none) :
    SourceHistory config fuel path (.callWith environment contextId [.byVal (.lit ty number)] callOrigin) before
      (invokeCall fuel config environment contextId [.byVal (.lit ty number)] [] callOrigin before) :=
  fuelHistory_exists fuel config _ path before
    (recursiveParameter_supported fuel config contextId context implementation parameter ty number scope callOrigin statementOrigin
      contextFound implementationFound resultsEmpty parameters body environment)


private def parameterContext : Context := ⟨0, "recursive", [], [], []⟩
private def parameterArguments : List Arg := [.byVal (.lit .i64 1)]
private def parameterImplementation : Impl := ⟨"recursive", #[⟨0, .byValue⟩], #[],
  #[⟨"n", .int .i64, .immutable, 0, 0⟩], .mk 0 [.expr (.call 0 parameterArguments 0) 0] none, .unknown⟩
private def parameterConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[parameterImplementation], #[parameterContext], 0, #[], #[], #[]⟩⟩

theorem recursiveParameterCall_supported (fuel : Nat) : ∀ environment,
    FuelSupport parameterConfig fuel (.callWith environment 0 parameterArguments 0) :=
  recursiveParameter_supported fuel parameterConfig 0 parameterContext parameterImplementation 0 .i64 1 0 0 0
    rfl rfl rfl rfl rfl

theorem recursiveParameterCall_history (fuel : Nat) (environment : RuntimeActivation) :
    SourceHistory parameterConfig fuel [] (.callWith environment 0 parameterArguments 0) .initial
      (invokeCall fuel parameterConfig environment 0 parameterArguments [] 0 .initial) :=
  fuelHistory_exists fuel parameterConfig (.callWith environment 0 parameterArguments 0) [] .initial
    (recursiveParameterCall_supported fuel environment)

theorem recursiveParameterCall_terminal : ∃ state,
    invokeCall 20 parameterConfig recursiveEnvironment 0 parameterArguments [] 0 .initial = .stop .timeout state ∧
    1 < state.nextAct ∧
    SourceHistory parameterConfig 20 [] (.callWith recursiveEnvironment 0 parameterArguments 0) .initial (.stop .timeout state) := by
  refine ⟨recursiveState (invokeCall 20 parameterConfig recursiveEnvironment 0 parameterArguments [] 0 .initial), ?_, ?_, ?_⟩
  · unfold recursiveState parameterConfig parameterContext parameterImplementation parameterArguments recursiveEnvironment
    cbv
  · unfold recursiveState parameterConfig parameterContext parameterImplementation parameterArguments recursiveEnvironment
    cbv
  · have actual : invokeCall 20 parameterConfig recursiveEnvironment 0 parameterArguments [] 0 .initial =
        .stop .timeout (recursiveState (invokeCall 20 parameterConfig recursiveEnvironment 0 parameterArguments [] 0 .initial)) := by
      unfold recursiveState parameterConfig parameterContext parameterImplementation parameterArguments recursiveEnvironment
      cbv
    have history := recursiveParameterCall_history 20 recursiveEnvironment
    rw [actual] at history
    exact history

#print axioms recursiveParameter_supported
#print axioms recursiveParameter_history
#print axioms recursiveParameterCall_supported
#print axioms recursiveParameterCall_history
#print axioms recursiveParameterCall_terminal

#print axioms recursiveModule_history
#print axioms recursiveModule_terminal

#print axioms recursiveCall_supported
#print axioms recursiveCall_history
#print axioms recursiveCall_terminal

#print axioms fuelHistory_exists
end Goose.Proofs.ConstructionGhostSourceFuel
