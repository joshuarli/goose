import Goose.Proofs.ConstructionGhostSourceFuel

namespace Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSourceTransition Goose.Proofs.ConstructionGhostRegisterProducer Goose.Proofs.ConstructionGhostScalarProducer

mutual
inductive ValueSyntax (config : EvalConfig) : Expr → Prop
  | base {expression : Expr} (supported : Goose.Proofs.ConstructionGhostSourceTransition.SupportedValue expression) :
      ValueSyntax config expression
  | read (place : Place) (child : PlaceSyntax config place) : ValueSyntax config (.read place)
  | reference (mutability : Goose.Core.Mutability) (place : Place) (child : PlaceSyntax config place) : ValueSyntax config (.ref mutability place)
  | length (view : View) (child : ViewSyntax config view) : ValueSyntax config (.len view)
  | pop (place : Place) (origin : Goose.Core.OriginId) (child : PlaceSyntax config place) : ValueSyntax config (.pop place origin)
  | aggregate (expression : Expr) (operands : List Expr) (shape : ValueAggregate expression operands)
      (children : ∀ operand ∈ operands, ValueSyntax config operand) : ValueSyntax config expression
  | unary (operation : Goose.Core.UnOp) (operand : Expr) (origin : Goose.Core.OriginId) (child : ValueSyntax config operand) :
      ValueSyntax config (.un operation operand origin)
  | conversion (kind : Goose.Core.ConvKind) (target : Ty) (operand : Expr) (origin : Goose.Core.OriginId) (child : ValueSyntax config operand) :
      ValueSyntax config (.conv kind target operand origin)
  | negation (operand : Expr) (child : ValueSyntax config operand) : ValueSyntax config (.not operand)
  | comparison (operation : Goose.Core.CmpOp) (first second : Expr) (left : ValueSyntax config first) (right : ValueSyntax config second) :
      ValueSyntax config (.cmp operation first second)
  | binary (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId)
      (left : ValueSyntax config first) (right : ValueSyntax config second) : ValueSyntax config (.bin operation first second origin)
  | logical (isAnd : Bool) (first second : Expr) (left : ValueSyntax config first) (right : ValueSyntax config second) :
      ValueSyntax config (logicalExpression isAnd first second)
  | bytes (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
      ValueSyntax config (.bytes ty bytes origin)
  | nonfixedArray (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) (nonfixed : ty.nonfixed = true)
      (builder : DeclarationBuilderSyntax config (.arrLit ty operands origin)) :
      ValueSyntax config (.arrLit ty operands origin)
  | nonfixedFill (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
      (nonfixed : (Ty.arr element count).nonfixed = true)
      (builder : DeclarationBuilderSyntax config (.fill (.arr element count) operand origin)) :
      ValueSyntax config (.fill (.arr element count) operand origin)
  | fill (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
      (fixed : (Ty.arr element count).nonfixed = false) (child : ValueSyntax config operand) :
      ValueSyntax config (.fill (.arr element count) operand origin)
  | channelCall (contextId : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (argumentsSyntax : ∀ id implementation start lookupReady,
        getImplementation config contextId start = .ok (id, implementation) lookupReady →
        ArgumentSyntax config implementation.params.toList arguments) :
      ValueSyntax config (.call contextId arguments origin)
  | call (contextId : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (argumentsSyntax : ArgumentSyntax config implementation.params.toList arguments) :
      ValueSyntax config (.call contextId arguments origin)

inductive DeclarationBuilderSyntax (config : EvalConfig) : Expr → Prop
  | bytes (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
      DeclarationBuilderSyntax config (.bytes ty bytes origin)
  | scalar (expression : Expr) (shape : ScalarExpression expression) (source : ValueSyntax config expression) :
      DeclarationBuilderSyntax config expression
  | supported (expression : Expr) (source : SupportedValue expression) : DeclarationBuilderSyntax config expression
  | static (expression : Expr) (source : ∀ environment destination, SupportedOperation config (.builder environment destination expression)) :
      DeclarationBuilderSyntax config expression
  | channelCall (contextId : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (argumentsSyntax : ∀ id implementation start lookupReady,
        getImplementation config contextId start = .ok (id, implementation) lookupReady →
        ArgumentSyntax config implementation.params.toList arguments) :
      DeclarationBuilderSyntax config (.call contextId arguments origin)
  | array (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId)
      (values : ∀ operand ∈ operands, ValueSyntax config operand)
      (builders : ∀ operand ∈ operands, DeclarationBuilderSyntax config operand) :
      DeclarationBuilderSyntax config (.arrLit ty operands origin)
  | fill (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
      (value : ValueSyntax config operand) (builder : DeclarationBuilderSyntax config operand) :
      DeclarationBuilderSyntax config (.fill (.arr element count) operand origin)

inductive ArgumentSyntax (config : EvalConfig) : List Param → List Arg → Prop
  | nil : ArgumentSyntax config [] []
  | value (parameter : Goose.Core.VarId) (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (child : ValueSyntax config operand) (tail : ArgumentSyntax config parameters arguments) :
      ArgumentSyntax config (⟨parameter, .byValue⟩ :: parameters) (.byVal operand :: arguments)
  | reference (parameter : Goose.Core.VarId) (parameters : List Param) (mutability : Goose.Core.Mutability)
      (place : Place) (arguments : List Arg) (child : PlaceSyntax config place) (tail : ArgumentSyntax config parameters arguments) :
      ArgumentSyntax config (⟨parameter, .byRef⟩ :: parameters) (.byRef mutability place :: arguments)
  | construct (parameter : Goose.Core.VarId) (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (child : ValueSyntax config operand)
      (direct : ∀ environment destination, SupportedOperation config (.builder environment destination operand))
      (tail : ArgumentSyntax config parameters arguments) :
      ArgumentSyntax config (⟨parameter, .byValue⟩ :: parameters) (.construct operand :: arguments)
  | constructRecursive (parameter : Goose.Core.VarId) (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (child : ValueSyntax config operand) (builder : DeclarationBuilderSyntax config operand)
      (tail : ArgumentSyntax config parameters arguments) :
      ArgumentSyntax config (⟨parameter, .byValue⟩ :: parameters) (.construct operand :: arguments)

inductive ViewSyntax (config : EvalConfig) : View → Prop
  | place (place : Place) (child : PlaceSyntax config place) : ViewSyntax config (.of place)
  | value (operand : Expr) (child : ValueSyntax config operand) : ViewSyntax config (.val operand)

inductive PlaceSyntax (config : EvalConfig) : Place → Prop
  | localPlace (localVar : Goose.Core.VarId) : PlaceSyntax config (.var localVar)
  | globalPlace (global : Goose.Core.GlobalId) : PlaceSyntax config (.global global)
  | dereference (operand : Expr) (child : ValueSyntax config operand) : PlaceSyntax config (.deref operand)
  | field (owner : Place) (index : Nat) (child : PlaceSyntax config owner) : PlaceSyntax config (.field owner index)
  | element (view : View) (operand : Expr) (origin : Goose.Core.OriginId)
      (viewChild : ViewSyntax config view) (indexChild : ValueSyntax config operand) : PlaceSyntax config (.elem view operand origin)

end


inductive StatementSyntax (config : EvalConfig) : Stmt → Prop
  | declaration (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
      (value : ValueSyntax config expression) (builder : DeclarationBuilderSyntax config expression) :
      StatementSyntax config (.letS localVar expression origin)
  | expression (operand : Expr) (origin : Goose.Core.OriginId) (child : ValueSyntax config operand) :
      StatementSyntax config (.expr operand origin)
  | printText (text : String) (origin : Goose.Core.OriginId) : StatementSyntax config (.print [.text text] origin)
  | whileLoop (condition : Expr) (scope : Nat) (statements : List Stmt) (origin : Goose.Core.OriginId)
      (conditionSyntax : ValueSyntax config condition)
      (body : ∀ statement ∈ statements, StatementSyntax config statement) :
      StatementSyntax config (.while condition (.mk scope statements none) origin)
  | eachStatement (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (place : Place) (byRef : Bool)
      (scope : Nat) (statements : List Stmt) (origin : Goose.Core.OriginId)
      (placeSyntax : PlaceSyntax config place)
      (body : ∀ statement ∈ statements, StatementSyntax config statement) :
      StatementSyntax config (.forEach localVar index (.of place) byRef (.mk scope statements none) origin)
  | eachValueStatement (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (operand : Expr) (byRef : Bool)
      (scope : Nat) (statements : List Stmt) (origin : Goose.Core.OriginId)
      (operandSyntax : ValueSyntax config operand)
      (body : ∀ statement ∈ statements, StatementSyntax config statement) :
      StatementSyntax config (.forEach localVar index (.val operand) byRef (.mk scope statements none) origin)
  | rangeStatement (localVar : Goose.Core.VarId) (first last : Expr) (scope : Nat) (statements : List Stmt)
      (origin : Goose.Core.OriginId) (firstSyntax : ValueSyntax config first) (lastSyntax : ValueSyntax config last)
      (body : ∀ statement ∈ statements, StatementSyntax config statement) :
      StatementSyntax config (.forRange localVar first last (.mk scope statements none) origin)
  | ifStatement (condition : Expr) (scope : Nat) (statements : List Stmt) (origin : Goose.Core.OriginId)
      (conditionSyntax : ValueSyntax config condition)
      (body : ∀ statement ∈ statements, StatementSyntax config statement) :
      StatementSyntax config (.ifS condition (.mk scope statements none) none origin)

  | ifElseStatement (condition : Expr) (yesScope : Nat) (yesStatements : List Stmt)
      (noScope : Nat) (noStatements : List Stmt) (origin : Goose.Core.OriginId)
      (conditionSyntax : ValueSyntax config condition)
      (yesBody : ∀ statement ∈ yesStatements, StatementSyntax config statement)
      (noBody : ∀ statement ∈ noStatements, StatementSyntax config statement) :
      StatementSyntax config (.ifS condition (.mk yesScope yesStatements none) (some (.mk noScope noStatements none)) origin)

def ClosedModule (config : EvalConfig) : Prop :=
  ∀ (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl),
    config.module.contexts[contextId]? = some context → config.module.impls[context.impl]? = some implementation →
    ∃ scope statements, implementation.body = .mk scope statements none ∧
      ∀ statement ∈ statements, StatementSyntax config statement

inductive TailSyntax (config : EvalConfig) : Option Expr → Prop
  | none : TailSyntax config none
  | value (expression : Expr) (supported : SupportedValue expression) : TailSyntax config (some expression)
  | scalar (expression : Expr) (shape : ScalarExpression expression) (derivation : ValueSyntax config expression) :
      TailSyntax config (some expression)
  | constructed (expression : Expr) (shape : ValueProducerExpression expression)
      (value : ValueSyntax config expression) (builder : DeclarationBuilderSyntax config expression) :
      TailSyntax config (some expression)
  | call (contextId : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (argumentsSyntax : ∀ id implementation start lookupReady,
        getImplementation config contextId start = .ok (id, implementation) lookupReady →
        ArgumentSyntax config implementation.params.toList arguments) :
      TailSyntax config (some (.call contextId arguments origin))

def ClosedModuleWithTails (config : EvalConfig) : Prop :=
  ∀ (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl),
    config.module.contexts[contextId]? = some context → config.module.impls[context.impl]? = some implementation →
    ∃ scope statements tail, implementation.body = .mk scope statements tail ∧
      (∀ statement ∈ statements, StatementSyntax config statement) ∧ TailSyntax config tail

theorem closedModule_withTails (config : EvalConfig) (closed : ClosedModule config) : ClosedModuleWithTails config := by
  intro contextId context implementation found implemented
  obtain ⟨scope, statements, body, derivation⟩ := closed contextId context implementation found implemented
  exact ⟨scope, statements, none, body, derivation, .none⟩

theorem implementation_lookup_source (config : EvalConfig) (contextId : Goose.Core.ContextId)
    (before ready : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (lookup : getImplementation config contextId before = .ok (id, implementation) ready) :
    ∃ context, config.module.contexts[contextId]? = some context ∧ context.impl = id ∧
      config.module.impls[id]? = some implementation := by
  cases found : config.module.contexts[contextId]? with
  | none => simp [getImplementation, found, bind, fault, EvalM.stop] at lookup
  | some context =>
      cases implemented : config.module.impls[context.impl]? with
      | none => simp [getImplementation, found, implemented, bind, fault, EvalM.stop] at lookup
      | some target =>
          simp [getImplementation, found, implemented, bind, pure] at lookup
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := lookup
          exact ⟨context, rfl, rfl, implemented⟩

structure SyntaxFuel (config : EvalConfig) (fuel : Nat) : Prop where
  value : ∀ environment expression, ValueSyntax config expression → FuelSupport config fuel (.value environment expression)
  builder : ∀ environment destination expression, DeclarationBuilderSyntax config expression →
    FuelSupport config fuel (.builder environment destination expression)
  element : ∀ environment parent element operand, ValueSyntax config operand → DeclarationBuilderSyntax config operand →
    FuelSupport config fuel (.element environment parent element operand)
  place : ∀ environment place, PlaceSyntax config place → FuelSupport config fuel (.place environment place)
  view : ∀ environment view, ViewSyntax config view → FuelSupport config fuel (.view environment view)
  placeView : ∀ environment place, PlaceSyntax config place → FuelSupport config fuel (.view environment (.of place))
  arguments : ∀ environment vars parameters arguments, ArgumentSyntax config parameters arguments →
    FuelSupport config fuel (.arguments environment vars parameters arguments)
  statement : ∀ environment statement, StatementSyntax config statement → FuelSupport config fuel (.statement environment statement)
  statements : ∀ environment statements, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.statements environment statements)
  block : ∀ environment scope statements, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.block environment (.mk scope statements none))
  loopBody : ∀ environment scope statements, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.loopBody environment (.mk scope statements none))
  whileLoop : ∀ environment condition scope statements, ValueSyntax config condition →
    (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.whileLoop environment condition (.mk scope statements none))
  boundBlock : ∀ environment pre scope statements, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.blockWith environment pre (.mk scope statements none))
  boundLoopBody : ∀ environment pre scope statements, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.loopBodyWith environment pre (.mk scope statements none))
  eachLoop : ∀ environment localVar index byRef scope statements view current,
    (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.eachLoop environment localVar index byRef (.mk scope statements none) view current)
  rangeLoop : ∀ environment localVar ty first last scope statements,
    (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.rangeLoop environment localVar ty first last (.mk scope statements none))
  activationBody : ∀ activation pre scope statements, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.boundActivationBody activation pre (.mk scope statements none))
  activation : ∀ activation pre scope statements origin, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.boundActivation activation pre (.mk scope statements none) origin)
  activationBodyTail : ∀ activation pre scope statements contextId arguments origin,
    (∀ statement ∈ statements, StatementSyntax config statement) →
    (∀ id implementation start lookupReady,
      getImplementation config contextId start = .ok (id, implementation) lookupReady →
      ArgumentSyntax config implementation.params.toList arguments) →
    FuelSupport config fuel (.boundActivationBody activation pre (.mk scope statements (some (.call contextId arguments origin))))
  activationTail : ∀ activation pre scope statements contextId arguments tailOrigin origin,
    (∀ statement ∈ statements, StatementSyntax config statement) →
    (∀ id implementation start lookupReady,
      getImplementation config contextId start = .ok (id, implementation) lookupReady →
      ArgumentSyntax config implementation.params.toList arguments) →
    FuelSupport config fuel (.boundActivation activation pre (.mk scope statements (some (.call contextId arguments tailOrigin))) origin)
  scalarBuilder : ∀ environment destination expression, ScalarExpression expression → ValueSyntax config expression →
    FuelSupport config fuel (.builder environment destination expression)
  scalarProducer : ∀ environment channels expression, ScalarExpression expression → ValueSyntax config expression →
    FuelSupport config fuel (.producerWith environment channels expression)
  activationBodyScalarTail : ∀ activation pre scope statements expression,
    (∀ statement ∈ statements, StatementSyntax config statement) → ScalarExpression expression → ValueSyntax config expression →
    FuelSupport config fuel (.boundActivationBody activation pre (.mk scope statements (some expression)))
  activationScalarTail : ∀ activation pre scope statements expression origin,
    (∀ statement ∈ statements, StatementSyntax config statement) → ScalarExpression expression → ValueSyntax config expression →
    FuelSupport config fuel (.boundActivation activation pre (.mk scope statements (some expression)) origin)
  supportedBuilder : ∀ environment destination expression, SupportedValue expression →
    FuelSupport config fuel (.builder environment destination expression)
  supportedProducer : ∀ environment channels expression, SupportedValue expression →
    FuelSupport config fuel (.producerWith environment channels expression)
  activationBodyValueTail : ∀ activation pre scope statements expression,
    (∀ statement ∈ statements, StatementSyntax config statement) → SupportedValue expression →
    FuelSupport config fuel (.boundActivationBody activation pre (.mk scope statements (some expression)))
  activationValueTail : ∀ activation pre scope statements expression origin,
    (∀ statement ∈ statements, StatementSyntax config statement) → SupportedValue expression →
    FuelSupport config fuel (.boundActivation activation pre (.mk scope statements (some expression)) origin)
  constructedProducer : ∀ environment channels expression, ValueProducerExpression expression → ValueSyntax config expression →
    DeclarationBuilderSyntax config expression → FuelSupport config fuel (.producerWith environment channels expression)
  activationBodyConstructedTail : ∀ activation pre scope statements expression,
    (∀ statement ∈ statements, StatementSyntax config statement) → ValueProducerExpression expression → ValueSyntax config expression →
    DeclarationBuilderSyntax config expression → FuelSupport config fuel (.boundActivationBody activation pre (.mk scope statements (some expression)))
  activationConstructedTail : ∀ activation pre scope statements expression origin,
    (∀ statement ∈ statements, StatementSyntax config statement) → ValueProducerExpression expression → ValueSyntax config expression →
    DeclarationBuilderSyntax config expression → FuelSupport config fuel (.boundActivation activation pre (.mk scope statements (some expression)) origin)
  producerCall : ∀ environment channels contextId arguments origin,
    (∀ id implementation start lookupReady,
      getImplementation config contextId start = .ok (id, implementation) lookupReady →
      ArgumentSyntax config implementation.params.toList arguments) →
    FuelSupport config fuel (.producerWith environment channels (.call contextId arguments origin))
  channelCall : ∀ environment contextId arguments channels origin,
    (∀ id implementation start lookupReady,
      getImplementation config contextId start = .ok (id, implementation) lookupReady →
      ArgumentSyntax config implementation.params.toList arguments) →
    FuelSupport config fuel (.channelCall environment contextId arguments channels origin)
  call : ∀ environment contextId arguments origin context implementation,
    config.module.contexts[contextId]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.results = #[] → ArgumentSyntax config implementation.params.toList arguments →
    FuelSupport config fuel (.callWith environment contextId arguments origin)

theorem syntaxFuel_existsWithTails (fuel : Nat) (config : EvalConfig) (closed : ClosedModuleWithTails config) : SyntaxFuel config fuel := by
  induction fuel with
  | zero =>
      constructor <;> intros <;> exact .timeout _
  | succ fuel previous =>
      constructor
      · intro environment expression derivation
        cases derivation with
        | base supported => exact .legacy (fuel + 1) (.value environment supported)
        | read place child => exact .readValue fuel environment place (previous.place environment place child)
        | reference mutability place child => exact .referenceValue fuel environment mutability place (previous.place environment place child)
        | length view child => exact .lengthValue fuel environment view (previous.view environment view child)
        | pop place origin child => exact .popValue fuel environment place origin (previous.place environment place child)
        | aggregate expression operands shape children =>
            exact .aggregate fuel environment expression operands shape
              (fun operand member => previous.value environment operand (children operand member))
        | unary operation operand origin child => exact .unary fuel environment operation operand origin (previous.value environment operand child)
        | conversion kind target operand origin child => exact .conversion fuel environment kind target operand origin (previous.value environment operand child)
        | negation operand child => exact .negation fuel environment operand (previous.value environment operand child)
        | comparison operation first second left right =>
            exact .comparison fuel environment operation first second (previous.value environment first left) (previous.value environment second right)
        | binary operation first second origin left right =>
            exact .binary fuel environment operation first second origin (previous.value environment first left) (previous.value environment second right)
        | logical isAnd first second left right =>
            exact .logical fuel environment isAnd first second (previous.value environment first left) (previous.value environment second right)
        | bytes ty bytes origin => exact .legacy (fuel + 1) (.valueBytes environment ty bytes origin)
        | nonfixedArray ty operands origin nonfixed builder =>
            exact .valueNonfixedArray fuel environment ty operands origin nonfixed
              (fun destination => previous.builder environment destination (.arrLit ty operands origin) builder)
        | nonfixedFill element count operand origin nonfixed builder =>
            exact .valueNonfixedFill fuel environment element count operand origin nonfixed
              (fun destination => previous.builder environment destination (.fill (.arr element count) operand origin) builder)
        | fill element count operand origin fixed child =>
            exact .fill fuel environment element count origin operand fixed (previous.value environment operand child)
        | channelCall contextId arguments origin argumentsSyntax =>
            exact .valueChannelCall fuel environment contextId arguments origin
              (fun channels => previous.channelCall environment contextId arguments channels origin argumentsSyntax)
        | call contextId arguments origin context implementation contextFound implementationFound resultsEmpty argumentsSyntax =>
            exact .valueCallWith fuel environment contextId arguments origin context implementation contextFound implementationFound
              resultsEmpty (previous.call environment contextId arguments origin context implementation contextFound implementationFound
                resultsEmpty argumentsSyntax)
      · intro environment destination expression derivation
        cases derivation with
        | bytes ty bytes origin => exact .legacy (fuel + 1) (.builderBytes environment destination ty bytes origin)
        | scalar expression shape source => exact .scalarBuilder fuel environment destination expression shape (previous.value environment expression source)
        | supported expression source =>
            have operandSupported := supportedBuilderOperand_supported expression source
            exact .supportedBuilder fuel environment destination expression source
              (previous.value environment (supportedBuilderOperand expression) (.base operandSupported))
              (fun child => previous.supportedBuilder environment child (supportedBuilderOperand expression) operandSupported)
        | static expression source => exact .legacy (fuel + 1) (source environment destination)
        | channelCall contextId arguments origin argumentsSyntax =>
            exact .builderChannelCall fuel environment destination contextId arguments origin
              (fun child => previous.channelCall environment contextId arguments [.construct child] origin argumentsSyntax)
        | array ty operands origin values builders =>
            exact .builderArray fuel environment destination ty operands origin
              (fun operand member parent element => previous.element environment parent element operand
                (values operand member) (builders operand member))
        | fill element count operand origin value builder =>
            exact .fillBuilder fuel environment destination element count operand origin (previous.value environment operand value)
              (fun child => previous.builder environment child operand builder)
      · intro environment parent element operand value builder
        exact .element fuel environment parent element operand (previous.value environment operand value)
          (fun destination => previous.builder environment destination operand builder)
      · intro environment place derivation
        cases derivation with
        | localPlace localVar => exact .legacy (fuel + 1) (.localPlace environment localVar)
        | globalPlace global => exact .legacy (fuel + 1) (.globalPlace environment global)
        | dereference operand child => exact .dereferencePlace fuel environment operand (previous.value environment operand child)
        | field owner index child => exact .fieldPlace fuel environment owner index (previous.place environment owner child)
        | element view operand origin viewChild indexChild =>
            exact .elementPlace fuel environment view operand origin (previous.view environment view viewChild) (previous.value environment operand indexChild)
      · intro environment view derivation
        cases derivation with
        | place place child => exact .placeView fuel environment place (previous.place environment place child)
        | value operand child => exact .valueView fuel environment operand (previous.value environment operand child)
      · intro environment place derivation
        exact .placeView fuel environment place (previous.place environment place derivation)
      · intro environment vars parameters arguments derivation
        cases derivation with
        | nil => exact .legacy (fuel + 1) (.argumentsDone environment vars)
        | value parameter parameters operand arguments child tail =>
            exact .argumentValue fuel environment vars ⟨parameter, .byValue⟩ parameters operand arguments
              (previous.value environment operand child) (previous.arguments environment vars parameters arguments tail)
        | reference parameter parameters mutability place arguments child tail =>
            exact .argumentReference fuel environment vars ⟨parameter, .byRef⟩ parameters mutability place arguments
              (previous.place environment place child) (previous.arguments environment vars parameters arguments tail)
        | construct parameter parameters operand arguments child direct tail =>
            exact .argumentConstruct fuel environment vars ⟨parameter, .byValue⟩ parameters operand arguments
              (previous.value environment operand child) (fun destination => .legacy fuel (direct environment destination))
              (previous.arguments environment vars parameters arguments tail)
        | constructRecursive parameter parameters operand arguments child builder tail =>
            exact .argumentConstruct fuel environment vars ⟨parameter, .byValue⟩ parameters operand arguments
              (previous.value environment operand child) (fun destination => previous.builder environment destination operand builder)
              (previous.arguments environment vars parameters arguments tail)
      · intro environment statement derivation
        cases derivation with
        | declaration localVar expression origin value builder =>
            exact .declaration fuel environment localVar expression origin (previous.value environment expression value)
              (fun destination => previous.builder environment destination expression builder)
        | expression operand origin child =>
            exact .expression fuel environment operand origin (previous.value environment operand child)
        | printText text origin => exact .legacy (fuel + 1) (.printText environment text origin)
        | whileLoop condition scope statements origin conditionSyntax body =>
            exact .whileStatement fuel environment condition (.mk scope statements none) origin
              (previous.whileLoop environment condition scope statements conditionSyntax body)
        | eachStatement localVar index place byRef scope statements origin placeSyntax body =>
            exact .eachStatement fuel environment localVar index (.of place) byRef (.mk scope statements none) origin
              (previous.placeView environment place placeSyntax)
              (fun runtime => previous.eachLoop environment localVar index byRef scope statements runtime 0 body)
        | eachValueStatement localVar index operand byRef scope statements origin operandSyntax body =>
            exact .eachStatement fuel environment localVar index (.val operand) byRef (.mk scope statements none) origin
              (previous.view environment (.val operand) (.value operand operandSyntax))
              (fun runtime => previous.eachLoop environment localVar index byRef scope statements runtime 0 body)
        | rangeStatement localVar first last scope statements origin firstSyntax lastSyntax body =>
            exact .rangeStatement fuel environment localVar first last (.mk scope statements none) origin
              (previous.value environment first firstSyntax) (previous.value environment last lastSyntax)
              (fun ty low high => previous.rangeLoop environment localVar ty low high scope statements body)
        | ifStatement condition scope statements origin conditionSyntax body =>
            exact .ifStatement fuel environment condition (.mk scope statements none) none origin
              (previous.value environment condition conditionSyntax) (previous.block environment scope statements body)
              (fun block impossible => by cases impossible)
        | ifElseStatement condition yesScope yesStatements noScope noStatements origin conditionSyntax yesBody noBody =>
            exact .ifStatement fuel environment condition (.mk yesScope yesStatements none) (some (.mk noScope noStatements none)) origin
              (previous.value environment condition conditionSyntax) (previous.block environment yesScope yesStatements yesBody)
              (fun block same => by cases same; exact previous.block environment noScope noStatements noBody)
      · intro environment statements derivation
        cases statements with
        | nil => exact .legacy (fuel + 1) (.empty environment)
        | cons statement rest =>
            have head : StatementSyntax config statement := derivation statement (by simp)
            have tail : ∀ statement ∈ rest, StatementSyntax config statement := by
              intro statement member
              exact derivation statement (by simp [member])
            have headSupported := previous.statement environment statement head
            exact .sequence fuel environment statement rest headSupported (previous.statements environment rest tail)
      · intro environment scope statements derivation
        exact .block fuel environment scope statements (fun scopedEnvironment => previous.statements scopedEnvironment statements derivation)
      · intro environment scope statements derivation
        exact .loopBody fuel environment (.mk scope statements none) (previous.block environment scope statements derivation)
      · intro environment condition scope statements conditionSyntax body
        exact .whileLoop fuel environment condition (.mk scope statements none) (previous.value environment condition conditionSyntax)
          (previous.loopBody environment scope statements body) (previous.whileLoop environment condition scope statements conditionSyntax body)
      · intro environment pre scope statements derivation
        exact .boundBlock fuel environment pre scope statements (fun scopedEnvironment => previous.statements scopedEnvironment statements derivation)
      · intro environment pre scope statements derivation
        exact .boundLoopBody fuel environment pre (.mk scope statements none) (previous.boundBlock environment pre scope statements derivation)
      · intro environment localVar index byRef scope statements view current derivation
        exact .eachLoop fuel environment localVar index byRef (.mk scope statements none) view current
          (fun pre => previous.boundLoopBody environment pre scope statements derivation)
          (previous.eachLoop environment localVar index byRef scope statements view (current + 1) derivation)
      · intro environment localVar ty first last scope statements derivation
        exact .rangeLoop fuel environment localVar ty first last (.mk scope statements none)
          (fun pre => previous.boundLoopBody environment pre scope statements derivation)
          (previous.rangeLoop environment localVar ty (first + 1) last scope statements derivation)
      · intro activation pre scope statements derivation
        exact .boundActivationBody fuel activation pre scope statements (fun environment => previous.statements environment statements derivation)
      · intro activation pre scope statements origin derivation
        exact .boundActivation fuel activation pre scope statements origin (previous.activationBody activation pre scope statements derivation)
      · intro activation pre scope statements contextId arguments origin derivation argumentSyntax
        exact .boundActivationTail fuel activation pre scope statements (.call contextId arguments origin)
          (fun environment => previous.statements environment statements derivation)
          (fun environment channels => previous.producerCall environment channels contextId arguments origin argumentSyntax)
      · intro activation pre scope statements contextId arguments tailOrigin origin derivation argumentSyntax
        exact .boundActivationWithTail fuel activation pre scope statements (.call contextId arguments tailOrigin) origin
          (previous.activationBodyTail activation pre scope statements contextId arguments tailOrigin derivation argumentSyntax)
      · intro environment destination expression scalar derivation
        exact .scalarBuilder fuel environment destination expression scalar (previous.value environment expression derivation)
      · intro environment channels expression scalar derivation
        exact .valueProducer fuel environment channels expression (.scalar scalar) (previous.value environment expression derivation)
          (fun destination => previous.scalarBuilder environment destination expression scalar derivation)
      · intro activation pre scope statements expression derivation scalar valueSyntax
        exact .boundActivationTail fuel activation pre scope statements expression
          (fun environment => previous.statements environment statements derivation)
          (fun environment channels => previous.scalarProducer environment channels expression scalar valueSyntax)
      · intro activation pre scope statements expression origin derivation scalar valueSyntax
        exact .boundActivationWithTail fuel activation pre scope statements expression origin
          (previous.activationBodyScalarTail activation pre scope statements expression derivation scalar valueSyntax)
      · intro environment destination expression supported
        have operandSupported := supportedBuilderOperand_supported expression supported
        exact .supportedBuilder fuel environment destination expression supported
          (previous.value environment (supportedBuilderOperand expression) (.base operandSupported))
          (fun source => previous.supportedBuilder environment source (supportedBuilderOperand expression) operandSupported)
      · intro environment channels expression supported
        exact .valueProducer fuel environment channels expression (.supported supported) (previous.value environment expression (.base supported))
          (fun destination => previous.supportedBuilder environment destination expression supported)
      · intro activation pre scope statements expression derivation supported
        exact .boundActivationTail fuel activation pre scope statements expression
          (fun environment => previous.statements environment statements derivation)
          (fun environment channels => previous.supportedProducer environment channels expression supported)
      · intro activation pre scope statements expression origin derivation supported
        exact .boundActivationWithTail fuel activation pre scope statements expression origin
          (previous.activationBodyValueTail activation pre scope statements expression derivation supported)
      · intro environment channels expression shape value builder
        exact .valueProducer fuel environment channels expression shape (previous.value environment expression value)
          (fun destination => previous.builder environment destination expression builder)
      · intro activation pre scope statements expression derivation shape value builder
        exact .boundActivationTail fuel activation pre scope statements expression
          (fun environment => previous.statements environment statements derivation)
          (fun environment channels => previous.constructedProducer environment channels expression shape value builder)
      · intro activation pre scope statements expression origin derivation shape value builder
        exact .boundActivationWithTail fuel activation pre scope statements expression origin
          (previous.activationBodyConstructedTail activation pre scope statements expression derivation shape value builder)
      · intro environment channels contextId arguments origin argumentSyntax
        exact .producerChannelCall fuel environment channels contextId arguments origin
          (fun selected => previous.channelCall environment contextId arguments selected origin argumentSyntax)
      · intro environment contextId arguments channels origin argumentSyntax
        apply FuelSupport.channelCall fuel environment contextId arguments channels origin
        · intro id implementation start lookupReady lookup
          exact previous.arguments environment implementation.vars implementation.params.toList arguments
            (argumentSyntax id implementation start lookupReady lookup)
        · intro id implementation start lookupReady act pre callableChannels lookup
          obtain ⟨context, contextFound, idEqual, implementationFound⟩ :=
            implementation_lookup_source config contextId start lookupReady id implementation lookup
          subst id
          obtain ⟨scope, statements, tail, body, derivation, tailDerivation⟩ := closed contextId context implementation contextFound implementationFound
          rw [body]
          cases tailDerivation with
          | none => exact previous.activation ⟨context.impl, act, implementation.vars, [], callableChannels⟩ pre scope statements origin derivation
          | scalar expression scalar valueSyntax =>
              exact previous.activationScalarTail ⟨context.impl, act, implementation.vars, [], callableChannels⟩ pre scope statements expression origin derivation scalar valueSyntax
          | value expression supported =>
              exact previous.activationValueTail ⟨context.impl, act, implementation.vars, [], callableChannels⟩ pre scope statements expression origin derivation supported
          | constructed expression shape value builder =>
              exact previous.activationConstructedTail ⟨context.impl, act, implementation.vars, [], callableChannels⟩ pre scope statements expression origin derivation shape value builder
          | call tailContext tailArguments tailOrigin tailArgumentsSyntax =>
              exact previous.activationTail ⟨context.impl, act, implementation.vars, [], callableChannels⟩ pre scope statements
                tailContext tailArguments tailOrigin origin derivation tailArgumentsSyntax
      · intro environment contextId arguments origin context implementation contextFound implementationFound resultsEmpty argumentsSyntax
        obtain ⟨scope, statements, tail, body, derivation, tailDerivation⟩ := closed contextId context implementation contextFound implementationFound
        apply FuelSupport.callWith fuel environment contextId arguments origin context implementation contextFound implementationFound
          resultsEmpty (previous.arguments environment implementation.vars implementation.params.toList arguments argumentsSyntax)
        intro act pre
        rw [body]
        cases tailDerivation with
        | none => exact previous.activation ⟨context.impl, act, implementation.vars, [], []⟩ pre scope statements origin derivation
        | scalar expression scalar valueSyntax =>
            exact previous.activationScalarTail ⟨context.impl, act, implementation.vars, [], []⟩ pre scope statements expression origin derivation scalar valueSyntax
        | value expression supported =>
            exact previous.activationValueTail ⟨context.impl, act, implementation.vars, [], []⟩ pre scope statements expression origin derivation supported
        | constructed expression shape value builder =>
            exact previous.activationConstructedTail ⟨context.impl, act, implementation.vars, [], []⟩ pre scope statements expression origin derivation shape value builder
        | call tailContext tailArguments tailOrigin tailArgumentsSyntax =>
            exact previous.activationTail ⟨context.impl, act, implementation.vars, [], []⟩ pre scope statements
              tailContext tailArguments tailOrigin origin derivation tailArgumentsSyntax

theorem syntaxFuel_exists (fuel : Nat) (config : EvalConfig) (closed : ClosedModule config) : SyntaxFuel config fuel :=
  syntaxFuel_existsWithTails fuel config (closedModule_withTails config closed)

theorem syntaxModule_history (fuel : Nat) (config : EvalConfig) (closed : ClosedModule config)
    (entryContext : Context) (entryImplementation : Impl) (noGlobals : config.module.globals.size = 0)
    (entryFound : config.module.contexts[config.module.entry]? = some entryContext)
    (entryImplementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (entryResults : entryImplementation.results = #[]) (entryParameters : entryImplementation.params = #[]) :
    ∃ outcome, SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ config.module.entry [] 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome := by
  have args : ArgumentSyntax config entryImplementation.params.toList [] := by
    simpa [entryParameters] using (ArgumentSyntax.nil : ArgumentSyntax config [] [])
  have support := (syntaxFuel_exists fuel config closed).call ⟨0, 0, #[], [], []⟩ config.module.entry [] 0
    entryContext entryImplementation entryFound entryImplementationFound entryResults args
  have history := fuelHistory_exists fuel config _ [] .initial support
  change SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ config.module.entry [] 0) .initial
    (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 .initial) at history
  refine ⟨_, history, ?_⟩
  simp only [runModule, noGlobals, List.range_zero, initGlobals, getImplementation, entryFound,
    entryImplementationFound, entryResults, Array.toList_empty, channelsFor, List.mapM_nil, bind, pure, moduleCallResult]
  cases invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 .initial <;> rfl

private def firstContext : Context := ⟨0, "first", [], [], []⟩
private def secondContext : Context := ⟨1, "second", [], [], []⟩
private def firstStatements : List Stmt := [.print [.text "a"] 0,
  .ifS (.bool true) (.mk 2 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none) none 0,
  .while (.bool false) (.mk 3 [.expr (.call 0 [] 0) 0] none) 0,
  .expr (.call 1 [.byVal (.lit .i64 1)] 0) 0]
private def secondStatements : List Stmt := [.print [.text "b"] 0, .expr (.call 0 [] 0) 0]
private def firstImplementation : Impl := ⟨"first", #[], #[], #[], .mk 0 firstStatements none, .unknown⟩
private def secondImplementation : Impl := ⟨"second", #[⟨0, .byValue⟩], #[],
  #[⟨"n", .int .i64, .immutable, 0, 0⟩], .mk 1 secondStatements none, .unknown⟩
private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[firstImplementation, secondImplementation], #[firstContext, secondContext], 0, #[], #[], #[]⟩⟩
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem firstStatements_syntax : ∀ statement ∈ firstStatements, StatementSyntax witnessConfig statement := by
  intro statement member
  simp only [firstStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .printText "a" 0
  · apply StatementSyntax.ifStatement
    · exact .base (.boolean true)
    · intro child childMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMember
      subst child
      exact .expression _ 0 (.base (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))
  · apply StatementSyntax.whileLoop
    · exact .base (.boolean false)
    · intro child childMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at childMember
      subst child
      exact .expression _ 0 (.call 0 [] 0 firstContext firstImplementation rfl rfl rfl .nil)
  · exact .expression _ 0 (.call 1 _ 0 secondContext secondImplementation rfl rfl rfl
      (.value 0 [] (.lit .i64 1) [] (.base (.integer .i64 1)) .nil))

private theorem secondStatements_syntax : ∀ statement ∈ secondStatements, StatementSyntax witnessConfig statement := by
  intro statement member
  simp only [secondStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .printText "b" 0
  · exact .expression _ 0 (.call 0 [] 0 firstContext firstImplementation rfl rfl rfl .nil)

private theorem witness_closed : ClosedModule witnessConfig := by
  intro contextId context implementation contextFound implementationFound
  cases contextId with
  | zero =>
      have contextEq : context = firstContext := by simpa [witnessConfig] using contextFound.symm
      subst context
      have implementationEq : implementation = firstImplementation := by
        simpa [witnessConfig, firstContext] using implementationFound.symm
      subst implementation
      exact ⟨0, firstStatements, rfl, firstStatements_syntax⟩
  | succ contextId =>
      cases contextId with
      | zero =>
          have contextEq : context = secondContext := by simpa [witnessConfig] using contextFound.symm
          subst context
          have implementationEq : implementation = secondImplementation := by
            simpa [witnessConfig, secondContext] using implementationFound.symm
          subst implementation
          exact ⟨1, secondStatements, rfl, secondStatements_syntax⟩
      | succ contextId => simp [witnessConfig] at contextFound

theorem mutualModule_history (fuel : Nat) : ∃ outcome,
    SourceHistory witnessConfig fuel [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule fuel witnessConfig .initial = moduleCallResult outcome :=
  syntaxModule_history fuel witnessConfig witness_closed firstContext firstImplementation rfl rfl rfl rfl rfl

theorem mutualModule_terminal : ∃ state,
    runModule 20 witnessConfig .initial = .stop .timeout state ∧ 1 < state.nextAct ∧
    0 < state.construction.stdout.data.size ∧
    ∃ outcome, SourceHistory witnessConfig 20 [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule 20 witnessConfig .initial = moduleCallResult outcome := by
  obtain ⟨outcome, history, execution⟩ := mutualModule_history 20
  refine ⟨witnessState (runModule 20 witnessConfig .initial), ?_, ?_, ?_, outcome, history, execution⟩ <;>
    unfold witnessState witnessConfig firstContext secondContext firstImplementation secondImplementation firstStatements secondStatements <;> cbv

#print axioms mutualModule_history
#print axioms mutualModule_terminal

#print axioms syntaxModule_history

#print axioms syntaxFuel_exists
end Goose.Proofs.ConstructionGhostSyntaxFuel
