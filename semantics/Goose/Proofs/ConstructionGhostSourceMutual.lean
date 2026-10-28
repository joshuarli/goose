import Goose.Proofs.ConstructionGhostScalarProducer
import Goose.Proofs.ConstructionGhostRegisterProducer
import Goose.Proofs.ConstructionGhostProducerChannel
import Goose.Proofs.ConstructionGhostChannelTransition
import Goose.Proofs.ConstructionGhostCallActivation
import Goose.Proofs.ConstructionGhostSourceTransition
import Goose.Proofs.ConstructionGhostBlock
import Goose.Proofs.ConstructionGhostResultScopeCore
import Goose.Proofs.ConstructionGhostElementCore
import Goose.Proofs.ConstructionGhostInvocationCore
import Goose.Proofs.ConstructionGhostArgumentCore
import Goose.Proofs.ConstructionGhostEachCore
import Goose.Proofs.ConstructionInitializerLoopReplay

namespace Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Construct Goose.Proofs.ConstructionGhostSourceTransition
open Goose.Proofs.ConstructionGhostBlock Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostElements
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionInitializerLoopReplay
open Goose.Proofs.ConstructionGhostArguments Goose.Proofs.ConstructionGhostEachCore
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostProducerChannel Goose.Proofs.ConstructionGhostRegisterProducer Goose.Proofs.ConstructionGhostScalarProducer

inductive SourceOperation : Type → Type
  | value (environment : RuntimeActivation) (expression : Expr) : SourceOperation Value
  | statement (environment : RuntimeActivation) (statement : Stmt) : SourceOperation Flow
  | statements (environment : RuntimeActivation) (statements : List Stmt) : SourceOperation Flow
  | block (environment : RuntimeActivation) (block : Block) : SourceOperation Flow
  | activationBody (activation : RuntimeActivation) (block : Block) : SourceOperation (List Carrier)
  | activation (activation : RuntimeActivation) (block : Block) (origin : Goose.Core.OriginId) : SourceOperation (List Carrier)
  | boundActivationBody (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (block : Block) : SourceOperation (List Carrier)
  | boundActivation (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (block : Block) (origin : Goose.Core.OriginId) : SourceOperation (List Carrier)
  | call (environment : RuntimeActivation) (context : Goose.Core.ContextId) (origin : Goose.Core.OriginId) : SourceOperation (List Carrier)
  | callWith (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
      (origin : Goose.Core.OriginId) : SourceOperation (List Carrier)
  | channelCall (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
      (channels : List Channel) (origin : Goose.Core.OriginId) : SourceOperation (List Carrier)
  | builder (environment : RuntimeActivation) (destination : Goose.Core.DestinationId) (expression : Expr) : SourceOperation Unit
  | bound (environment : RuntimeActivation) (count : Nat) (defaultValue : Int) (bound : Bound) : SourceOperation Int
  | place (environment : RuntimeActivation) (place : Place) : SourceOperation Goose.Core.Loc
  | view (environment : RuntimeActivation) (view : View) : SourceOperation RuntimeView
  | blockWith (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block) : SourceOperation Flow
  | loopBodyWith (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block) : SourceOperation Flow
  | whileLoop (environment : RuntimeActivation) (condition : Expr) (body : Block) : SourceOperation Flow
  | eachLoop (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId)
      (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat) : SourceOperation Flow
  | rangeLoop (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (ty : Goose.Core.IntTy)
      (first last : Int) (body : Block) : SourceOperation Flow
  | loopBody (environment : RuntimeActivation) (body : Block) : SourceOperation Flow
  | printArgument (environment : RuntimeActivation) (argument : PrintArg) : SourceOperation ByteArray
  | element (environment : RuntimeActivation) (parent : Goose.Core.DestinationId) (element : Ty) (operand : Expr) : SourceOperation Unit
  | arguments (environment : RuntimeActivation) (vars : Array LocalVar) (parameters : List Param)
      (arguments : List Arg) : SourceOperation (List Value)
  | producerWith (environment : RuntimeActivation) (channels : List Channel) (expression : Expr) : SourceOperation (List Carrier)
  | producer (environment : RuntimeActivation) (expression : Expr) : SourceOperation (List Carrier)

def execute (fuel : Nat) (config : EvalConfig) : SourceOperation α → EvalM α
  | .value environment expression => evalValue fuel config environment expression
  | .statement environment statement => execStmt fuel config environment statement
  | .statements environment statements => execStmts fuel config environment statements
  | .block environment block => execBlock fuel config environment [] [] block
  | .activationBody activation block => execActivationBody fuel config activation [] block
  | .activation activation block origin => enterActivation fuel config activation [] block origin
  | .boundActivationBody activation pre block => execActivationBody fuel config activation pre block
  | .boundActivation activation pre block origin => enterActivation fuel config activation pre block origin
  | .call environment context origin => invokeCall fuel config environment context [] [] origin
  | .callWith environment context arguments origin => invokeCall fuel config environment context arguments [] origin
  | .channelCall environment context arguments channels origin => invokeCall fuel config environment context arguments channels origin
  | .builder environment destination expression => buildExpr fuel config environment destination expression
  | .bound environment count defaultValue bound => evalBound fuel config environment count defaultValue bound
  | .place environment place => evalPlace fuel config environment place
  | .view environment view => evalView fuel config environment view
  | .blockWith environment pre body => execBlock fuel config environment pre [] body
  | .loopBodyWith environment pre body => Goose.Construct.loopBody fuel config environment pre body
  | .whileLoop environment condition body => execWhile fuel config environment condition body
  | .eachLoop environment localVar index byRef body view current => execEach fuel config environment localVar index byRef body view current
  | .rangeLoop environment localVar ty first last body => execRange fuel config environment localVar ty first last body
  | .loopBody environment body => Goose.Construct.loopBody fuel config environment [] body
  | .printArgument environment argument => evalPrintArg fuel config environment argument
  | .element environment parent element operand => buildElement fuel config environment parent element operand
  | .arguments environment vars parameters arguments => evalArguments fuel config environment vars parameters arguments
  | .producerWith environment channels expression => evalProduce fuel config environment channels expression
  | .producer environment expression => evalProduce fuel config environment [] expression

def conditionalResult (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (yes no : Block) : ExecutionStep Value → ExecutionStep Value
  | .ok value state => (do
      let selected ← expectBool value
      let flow ← execBlock fuel config environment [] [] (if selected then yes else no)
      match flow with
      | .normal value => pure value
      | _ => fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def activationBodyResult (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (scope : Nat) (before : ExecutionState) (outcome : ExecutionStep Flow) : ExecutionStep (List Carrier) :=
  match withScope activation scope before.nextScope (fun _ => resultScopeContinuation activation.channels none
      (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config
          { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression)) outcome)
      (resultScopeStart activation scope before) with
  | .ok (.normal _, carriers) state => .ok carriers state
  | .ok _ state => .stop (.fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem activationBody_source (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (before : ExecutionState) :
    execActivationBody (fuel + 1) config activation [] (.mk scope statements none) before =
      activationBodyResult fuel config activation scope before
        (execStmts fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
          statements (resultScopeStart activation scope before)) := by
  obtain ⟨outcome, visits, replay, execution⟩ := execResultScope_statementReplay fuel config activation
    activation.channels scope statements
    (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
      (fun channels => evalProduce fuel config environment channels expression)) before
  simp only [execActivationBody, bind]
  rw [execution, replay.sound]
  simp only [activationBodyResult]
  cases result : withScope activation scope before.nextScope (fun _ =>
    resultScopeContinuation activation.channels none
      (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config
          { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression)) outcome)
    (resultScopeStart activation scope before) with
  | ok pair state => cases pair with | mk flow carriers => cases flow <;> simp [result, bind, pure, fault, EvalM.stop]
  | stop | escape | jump => simp [result]

def boundActivationBodyResult (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (scope : Nat) (statements : List Stmt) (before : ExecutionState) :
    ExecutionStep (List Carrier) :=
  match withScope activation scope before.nextScope (fun _ =>
      resultScopeAfterBind fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
        activation.channels statements none
        (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
          (fun channels => evalProduce fuel config environment channels expression))
        (bindAll activation.act before.nextScope pre (resultScopeStart activation scope before)))
      (resultScopeStart activation scope before) with
  | .ok (.normal _, carriers) state => .ok carriers state
  | .ok _ state => .stop (.fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem boundActivationBody_source (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (scope : Nat) (statements : List Stmt) (before : ExecutionState) :
    execActivationBody (fuel + 1) config activation pre (.mk scope statements none) before =
      boundActivationBodyResult fuel config activation pre scope statements before := by
  have source := execResultScope_bind fuel config activation pre activation.channels scope statements none
    (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
      (fun channels => evalProduce fuel config environment channels expression)) before
  simp only [execActivationBody, bind, source, boundActivationBodyResult]
  cases result : withScope activation scope before.nextScope (fun _ =>
      resultScopeAfterBind fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
        activation.channels statements none
        (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
          (fun channels => evalProduce fuel config environment channels expression))
        (bindAll activation.act before.nextScope pre (resultScopeStart activation scope before)))
      (resultScopeStart activation scope before) with
  | ok pair state => cases pair with | mk flow carriers => cases flow <;> simp [result, bind, pure, fault, EvalM.stop]
  | stop | escape | jump => simp [result]

#print axioms boundActivationBody_source

def activationEnterResult (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before : ExecutionState) : ExecutionStep (List Carrier) :=
  match config.module.impls[activation.implementation]? with
  | none => fault .unbound before
  | some implementation => finishActivation config.layout activation (implementation.results.toList.map (·.ty)) origin
      (execActivationBody fuel config activation [] block) before

theorem activationEnter_source (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    enterActivation (fuel + 1) config activation [] block origin before =
      activationEnterResult fuel config activation block origin before := by
  simp only [enterActivation, activationEnterResult]
  cases config.module.impls[activation.implementation]? <;> rfl

theorem emptyCall_enter (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (depth : before.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, before.nextAct, implementation.vars, [], []⟩
    let activated := { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
    invokeCall (fuel + 2) config environment contextId [] [] origin before =
      (enterActivation (fuel + 1) config activation [] implementation.body origin >>= fun carriers =>
        deliverCarriers (fuel + 1) config.layout [] carriers origin) activated := by
  simp only [invokeCall, getImplementation, contextFound, implementationFound, resultsEmpty, parametersEmpty,
    Array.size_empty, Array.toList_empty, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.mapM_nil, evalArguments, freshAct, EvalM.get, EvalM.set, bind, pure,
    List.map_nil, List.zip_nil_left, Nat.not_le.mpr depth]

theorem emptyCall_depth (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (depth : Goose.Core.maxCallDepth ≤ before.activations.length) :
    invokeCall (fuel + 2) config environment contextId [] [] origin before = .stop .timeout before := by
  simp only [invokeCall, getImplementation, contextFound, implementationFound, resultsEmpty, parametersEmpty,
    Array.size_empty, Array.toList_empty, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.mapM_nil, evalArguments, EvalM.get, bind, pure, depth, if_true,
    Goose.Construct.timeout, EvalM.stop]

theorem emptyCall_one (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (resultsEmpty : implementation.results = #[]) :
    invokeCall 1 config environment contextId [] [] origin before = .stop .timeout before := by
  simp only [invokeCall, getImplementation, contextFound, implementationFound, resultsEmpty,
    Array.size_empty, Array.toList_empty, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.mapM_nil, evalArguments, bind, pure, Goose.Construct.timeout, EvalM.stop]

def callDeliveryResult (fuel : Nat) (config : EvalConfig) (origin : Goose.Core.OriginId) :
    ExecutionStep (List Carrier) → ExecutionStep (List Carrier)
  | .ok carriers state => deliverCarriers fuel config.layout [] carriers origin state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def callValueResult (origin : Goose.Core.OriginId) : ExecutionStep (List Carrier) → ExecutionStep Value
  | .ok carriers state => (do
      publishCarriers origin carriers
      carrierValue (← singleCarrier carriers)) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem valueCallWith_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (arguments : List Arg) (context : Context) (implementation : Impl) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (resultsEmpty : implementation.results = #[]) :
    evalValue (fuel + 1) config environment (.call contextId arguments origin) before =
      callValueResult origin (invokeCall fuel config environment contextId arguments [] origin before) := by
  simp only [evalValue, getImplementation, contextFound, implementationFound, resultsEmpty,
    Array.toList_empty, channelsFor, List.mapM_nil, bind, pure, callValueResult]
  cases invokeCall fuel config environment contextId arguments [] origin before <;> rfl

def argumentResult (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (vars : Array LocalVar)
    (parameters : List Param) (arguments : List Arg) : ExecutionStep Value → ExecutionStep (List Value)
  | .ok value state => (do pure (value :: (← evalArguments fuel config environment vars parameters arguments))) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem valueArgument_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg)
    (before : ExecutionState) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.byVal operand :: arguments) before =
      argumentResult fuel config environment vars parameters arguments (evalValue fuel config environment operand before) := by
  simp only [evalArguments, bind, argumentResult]
  cases evalValue fuel config environment operand before <;> rfl

theorem valueCall_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (resultsEmpty : implementation.results = #[]) :
    evalValue (fuel + 1) config environment (.call contextId [] origin) before =
      callValueResult origin (invokeCall fuel config environment contextId [] [] origin before) :=
  valueCallWith_source fuel config environment contextId [] context implementation origin before contextFound implementationFound resultsEmpty

theorem producerCallWith_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    evalProduce (fuel + 1) config environment [] (.call context arguments origin) before =
      invokeCall fuel config environment context arguments [] origin before := by
  simp only [evalProduce, List.mapM, List.mapM.loop, List.reverse_nil, bind, pure]

def callWithResult (fuel : Nat) (config : EvalConfig) (context : Context) (implementation : Impl)
    (origin : Goose.Core.OriginId) : ExecutionStep (List Value) → ExecutionStep (List Carrier)
  | .ok values state =>
      if state.activations.length ≥ Goose.Core.maxCallDepth then .stop .timeout state
      else
        let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], []⟩
        let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
        let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
        (enterActivation fuel config activation pre implementation.body origin >>= fun carriers =>
          deliverCarriers fuel config.layout [] carriers origin) activated
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem callWith_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
    (context : Context) (implementation : Impl) (before : ExecutionState)
    (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (resultsEmpty : implementation.results = #[]) :
    invokeCall (fuel + 1) config environment contextId arguments [] origin before =
      callWithResult fuel config context implementation origin
        (evalArguments fuel config environment implementation.vars implementation.params.toList arguments before) := by
  simp only [invokeCall, getImplementation, contextFound, implementationFound, resultsEmpty,
    Array.size_empty, Array.toList_empty, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.mapM_nil, bind, pure, callWithResult]
  cases result : evalArguments fuel config environment implementation.vars implementation.params.toList arguments before with
  | ok values ready =>
      simp only [result, bind, pure, EvalM.get, EvalM.set, freshAct]
      split <;> simp_all [bind, pure, Goose.Construct.timeout, EvalM.stop]
  | stop | escape | jump => simp_all [bind]

#print axioms callWith_source

theorem producerCall_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    evalProduce (fuel + 1) config environment [] (.call context [] origin) before =
      invokeCall fuel config environment context [] [] origin before :=
  producerCallWith_source fuel config environment context [] origin before

inductive ValueAggregate : Expr → List Expr → Prop
  | fixedArray (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId)
      (fixed : ty.nonfixed = false) : ValueAggregate (.arrLit ty operands origin) operands
  | record (id : Goose.Core.StructId) (fields : TyList) (operands : List Expr) :
      ValueAggregate (.structLit (.structT id fields) operands) operands

def logicalExpression (isAnd : Bool) (first second : Expr) : Expr :=
  if isAnd then .and first second else .or first second

theorem constructedArgument_direct_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (operand : Expr) (localVar : LocalVar) (before : ExecutionState)
    (found : vars[parameter.var]? = some localVar)
    (direct : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none) :
    argumentValue fuel config environment vars parameter (.construct operand) before =
      (do
        let destination ← newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
          (producerCount? ⟨config.module, environment.vars⟩ operand)
        buildExpr fuel config environment destination operand
        let destination ← completedReceivingDestination destination
        publishCarriers (expressionOrigin operand) [.completed destination]
        carrierValue (.completed destination)) before := by
  simp only [argumentValue, found, bind, materializeProducer, direct, pure, constructLocal, EvalConfig.layout]
  cases result : newDestination (LayoutEnv.ofModule config.module) environment.act localVar.ty .value (expressionOrigin operand) none
    (producerCount? ⟨config.module, environment.vars⟩ operand) before with
  | ok destination ready =>
      simp only [result, bind, pure]
      cases built : buildExpr fuel config environment destination operand ready with
      | ok unit after =>
          cases unit
          simp only [built, bind, pure]
          cases completed : completedReceivingDestination destination after with
          | ok current finished =>
              simp only [completed, bind, pure]
              cases published : publishCarriers (expressionOrigin operand) [.completed current] finished <;>
                simp [published, bind, pure]
          | stop | escape | jump => simp_all [bind, pure]
      | stop | escape | jump => simp_all [bind, pure]
  | stop | escape | jump => simp_all [bind, pure]

#print axioms constructedArgument_direct_source

def loopStart (environment : RuntimeActivation) (before : ExecutionState) : ExecutionState :=
  let target : BreakTarget := ⟨before.nextScope, environment.act, .loop, []⟩
  { before with nextScope := before.nextScope + 1, breaks := target :: before.breaks }

inductive DeclarationFallback (environment : RuntimeActivation) (implementation : Impl)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) : ExecutionState → ExecutionState → Prop
  | absent (state : ExecutionState)
      (notNamed : (implementation.results.toList.zipIdx.find? fun (result, _) =>
        result.namedLocal == some localVar) = none) : DeclarationFallback environment implementation localVar origin state state
  | selected (before selectedReady ready : ExecutionState) (result : ResultDescriptor) (index : Nat)
      (incoming selected : Goose.Core.DestinationId) (pending : PendingDestination)
      (named : (implementation.results.toList.zipIdx.find? fun (result, _) =>
        result.namedLocal == some localVar) = some (result, index))
      (channel : environment.channels[index]? = some (.construct incoming))
      (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok selected selectedReady)
      (queried : getDestination selected selectedReady = .ok pending ready)
      (nonvalue : pending.capability.request ≠ .value) :
      DeclarationFallback environment implementation localVar origin before ready

theorem DeclarationFallback.unique {environment : RuntimeActivation} {implementation : Impl}
    {localVar : Goose.Core.VarId} {origin : Goose.Core.OriginId} {before first second : ExecutionState}
    (left : DeclarationFallback environment implementation localVar origin before first)
    (right : DeclarationFallback environment implementation localVar origin before second) : first = second := by
  cases left <;> cases right <;> simp_all

inductive SourceHistory (config : EvalConfig) :
    {α : Type} → Nat → List Nat → SourceOperation α → ExecutionState → ExecutionStep α → Prop
  | timeout (path : List Nat) (operation : SourceOperation α) (before : ExecutionState) :
      SourceHistory config 0 path operation before (.stop .timeout before)
  | integer (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (ty : Goose.Core.IntTy) (value : Int) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.value environment (.lit ty value)) before (.ok (.int ty value) before)
  | boolean (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (value : Bool) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.value environment (.bool value)) before (.ok (.bool value) before)
  | valueBytes (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (ty : Ty)
      (bytes : List UInt8) (origin : Goose.Core.OriginId) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.value environment (.bytes ty bytes origin)) before
        (evalValue (fuel + 1) config environment (.bytes ty bytes origin) before)
  | valueNonfixedArray (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) (before : ExecutionState)
      (nonfixed : ty.nonfixed = true)
      (child : ∀ destination ready,
        newDestination config.layout environment.act ty .value origin none
          (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) before = .ok destination ready →
        SourceHistory config fuel (path ++ [0]) (.builder environment destination (.arrLit ty operands origin)) ready
          (buildExpr fuel config environment destination (.arrLit ty operands origin) ready)) :
      SourceHistory config (fuel + 1) path (.value environment (.arrLit ty operands origin)) before
        (evalValue (fuel + 1) config environment (.arrLit ty operands origin) before)
  | valueNonfixedFill (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState)
      (nonfixed : (Ty.arr element count).nonfixed = true)
      (child : ∀ destination ready,
        newDestination config.layout environment.act (.arr element count) .value origin none
          (producerCount? ⟨config.module, environment.vars⟩ (.fill (.arr element count) operand origin)) before = .ok destination ready →
        SourceHistory config fuel (path ++ [0]) (.builder environment destination (.fill (.arr element count) operand origin)) ready
          (buildExpr fuel config environment destination (.fill (.arr element count) operand origin) ready)) :
      SourceHistory config (fuel + 1) path (.value environment (.fill (.arr element count) operand origin)) before
        (evalValue (fuel + 1) config environment (.fill (.arr element count) operand origin) before)
  | negation {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operand : Expr}
      {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome) :
      SourceHistory config (fuel + 1) path (.value environment (.not operand)) before (negationResult outcome)
  | fill {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {element : Ty} {count : Nat}
      {operand : Expr} {origin : Goose.Core.OriginId} {before : ExecutionState} {outcome : ExecutionStep Value}
      (fixed : (Ty.arr element count).nonfixed = false)
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome) :
      SourceHistory config (fuel + 1) path (.value environment (.fill (.arr element count) operand origin)) before
        (fillResult count outcome)
  | aggregate (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (expression : Expr)
      (operands : List Expr) (before : ExecutionState) (shape : ValueAggregate expression operands)
      (children : ∀ outcome visits,
        OperandReplay (evalValue fuel config environment) 0 operands [] before outcome visits →
        ∀ visit ∈ visits, SourceHistory config fuel (path ++ [visit.ordinal]) (.value environment visit.operand)
          visit.before visit.outcome) :
      SourceHistory config (fuel + 1) path (.value environment expression) before
        (evalValue (fuel + 1) config environment expression before)
  | unary {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operation : Goose.Core.UnOp}
      {operand : Expr} {origin : Goose.Core.OriginId} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before
        (evalValue fuel config environment operand before)) :
      SourceHistory config (fuel + 1) path (.value environment (.un operation operand origin)) before
        (evalValue (fuel + 1) config environment (.un operation operand origin) before)
  | conversion {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {kind : Goose.Core.ConvKind}
      {target : Ty} {operand : Expr} {origin : Goose.Core.OriginId} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before
        (evalValue fuel config environment operand before)) :
      SourceHistory config (fuel + 1) path (.value environment (.conv kind target operand origin)) before
        (evalValue (fuel + 1) config environment (.conv kind target operand origin) before)
  | comparison {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operation : Goose.Core.CmpOp}
      {first second : Expr} {before : ExecutionState}
      (left : SourceHistory config fuel (path ++ [0]) (.value environment first) before
        (evalValue fuel config environment first before))
      (right : ∀ value middle, evalValue fuel config environment first before = .ok value middle →
        SourceHistory config fuel (path ++ [1]) (.value environment second) middle
          (evalValue fuel config environment second middle)) :
      SourceHistory config (fuel + 1) path (.value environment (.cmp operation first second)) before
        (evalValue (fuel + 1) config environment (.cmp operation first second) before)
  | binary {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operation : Goose.Core.BinOp}
      {first second : Expr} {origin : Goose.Core.OriginId} {before : ExecutionState}
      (left : SourceHistory config fuel (path ++ [0]) (.value environment first) before
        (evalValue fuel config environment first before))
      (right : ∀ value middle ty number ready, evalValue fuel config environment first before = .ok value middle →
        expectInt value middle = .ok (ty, number) ready →
        SourceHistory config fuel (path ++ [1]) (.value environment second) ready
          (evalValue fuel config environment second ready)) :
      SourceHistory config (fuel + 1) path (.value environment (.bin operation first second origin)) before
        (evalValue (fuel + 1) config environment (.bin operation first second origin) before)
  | logical {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {isAnd : Bool}
      {first second : Expr} {before : ExecutionState}
      (left : SourceHistory config fuel (path ++ [0]) (.value environment first) before
        (evalValue fuel config environment first before))
      (right : ∀ value middle ready, evalValue fuel config environment first before = .ok value middle →
        expectBool value middle = .ok isAnd ready →
        SourceHistory config fuel (path ++ [1]) (.value environment second) ready
          (evalValue fuel config environment second ready)) :
      SourceHistory config (fuel + 1) path (.value environment (logicalExpression isAnd first second)) before
        (evalValue (fuel + 1) config environment (logicalExpression isAnd first second) before)
  | singleton {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operand : Expr}
      {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome) :
      SourceHistory config (fuel + 1) path (.value environment (.values [operand])) before outcome
  | conditional {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {condition : Expr}
      {yes no : Block} {origin : Goose.Core.OriginId} {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment condition) before outcome)
      (branch : ∀ value middle selected ready, outcome = .ok value middle →
        expectBool value middle = .ok selected ready →
        SourceHistory config fuel (path ++ [if selected then 1 else 2])
          (.block environment (if selected then yes else no)) ready
          (execBlock fuel config environment [] [] (if selected then yes else no) ready)) :
      SourceHistory config (fuel + 1) path (.value environment (.ifE condition yes no origin)) before
        (conditionalResult fuel config environment yes no outcome)
  | block {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {scope : Nat}
      {statements : List Stmt} {before : ExecutionState} {outcome : ExecutionStep Flow}
      (body : SourceHistory config fuel (path ++ [0])
        (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements)
        { before with nextScope := before.nextScope + 1 } outcome) :
      SourceHistory config (fuel + 1) path (.block environment (.mk scope statements none)) before
        (withScope environment scope before.nextScope (fun _ => blockContinuation fuel config
          { environment with scopes := (scope, before.nextScope) :: environment.scopes } [] none outcome)
          { before with nextScope := before.nextScope + 1 })
  | activationBody {fuel : Nat} {path : List Nat} {activation : RuntimeActivation} {scope : Nat}
      {statements : List Stmt} {before : ExecutionState} {outcome : ExecutionStep Flow}
      (body : SourceHistory config fuel (path ++ [0])
        (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements)
        (resultScopeStart activation scope before) outcome) :
      SourceHistory config (fuel + 1) path (.activationBody activation (.mk scope statements none)) before
        (activationBodyResult fuel config activation scope before outcome)
  | activation {fuel : Nat} {path : List Nat} {activation : RuntimeActivation} {block : Block}
      {origin : Goose.Core.OriginId} {before : ExecutionState}
      (body : ∀ implementation, config.module.impls[activation.implementation]? = some implementation →
        SourceHistory config fuel (path ++ [0]) (.activationBody activation block) before
          (execActivationBody fuel config activation [] block before)) :
      SourceHistory config (fuel + 1) path (.activation activation block origin) before
        (activationEnterResult fuel config activation block origin before)
  | valueCall {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      {outcome : ExecutionStep (List Carrier)}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (child : SourceHistory config fuel (path ++ [0]) (.call environment contextId origin) before outcome) :
      SourceHistory config (fuel + 1) path (.value environment (.call contextId [] origin)) before
        (callValueResult origin outcome)
  | valueCallWith {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {arguments : List Arg} {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      {outcome : ExecutionStep (List Carrier)}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (child : SourceHistory config fuel (path ++ [0]) (.callWith environment contextId arguments origin) before outcome) :
      SourceHistory config (fuel + 1) path (.value environment (.call contextId arguments origin)) before
        (callValueResult origin outcome)
  | producerCallWith {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {arguments : List Arg} {origin : Goose.Core.OriginId} {before : ExecutionState} {outcome : ExecutionStep (List Carrier)}
      (child : SourceHistory config fuel (path ++ [0]) (.callWith environment contextId arguments origin) before outcome) :
      SourceHistory config (fuel + 1) path (.producer environment (.call contextId arguments origin)) before outcome
  | producerCall {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {outcome : ExecutionStep (List Carrier)}
      (child : SourceHistory config fuel (path ++ [0]) (.call environment contextId origin) before outcome) :
      SourceHistory config (fuel + 1) path (.producer environment (.call contextId [] origin)) before outcome
  | boundActivationBody {fuel : Nat} {path : List Nat} {activation : RuntimeActivation}
      {pre : List (Goose.Core.VarId × Value)} {scope : Nat} {statements : List Stmt} {before : ExecutionState}
      (body : ∀ ready, bindAll activation.act before.nextScope pre (resultScopeStart activation scope before) = .ok () ready →
        SourceHistory config fuel (path ++ [0])
          (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements) ready
          (execStmts fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements ready)) :
      SourceHistory config (fuel + 1) path (.boundActivationBody activation pre (.mk scope statements none)) before
        (boundActivationBodyResult fuel config activation pre scope statements before)
  | boundActivationTail (fuel : Nat) (path : List Nat) (activation : RuntimeActivation)
      (pre : List (Goose.Core.VarId × Value)) (scope : Nat) (statements : List Stmt) (tail : Expr) (before : ExecutionState)
      (body : ∀ ready, bindAll activation.act before.nextScope pre (resultScopeStart activation scope before) = .ok () ready →
        SourceHistory config fuel (path ++ [0])
          (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements) ready
          (execStmts fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements ready))
      (tailChild : ∀ ready value after planned tokens prepared,
        bindAll activation.act before.nextScope pre (resultScopeStart activation scope before) = .ok () ready →
        execStmts fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements ready =
          .ok (.normal value) after →
        completionChannelSetup activation.channels (expressionOrigin tail) after = .ok (planned, tokens) prepared →
        SourceHistory config fuel (path ++ [1])
          (.producerWith { activation with scopes := (scope, before.nextScope) :: activation.scopes } planned tail) prepared
          (evalProduce fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } planned tail prepared)) :
      SourceHistory config (fuel + 1) path (.boundActivationBody activation pre (.mk scope statements (some tail))) before
        (execActivationBody (fuel + 1) config activation pre (.mk scope statements (some tail)) before)
  | boundActivation {fuel : Nat} {path : List Nat} {activation : RuntimeActivation}
      {pre : List (Goose.Core.VarId × Value)} {block : Block} {origin : Goose.Core.OriginId} {before : ExecutionState}
      (body : ∀ implementation, config.module.impls[activation.implementation]? = some implementation →
        SourceHistory config fuel (path ++ [0]) (.boundActivationBody activation pre block) before
          (execActivationBody fuel config activation pre block before)) :
      SourceHistory config (fuel + 1) path (.boundActivation activation pre block origin) before
        (enterActivation (fuel + 1) config activation pre block origin before)
  | callWith {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {arguments : List Arg} {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      {outcome : ExecutionStep (List Value)}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (argumentsHistory : SourceHistory config fuel (path ++ [0])
        (.arguments environment implementation.vars implementation.params.toList arguments) before outcome)
      (activationHistory : ∀ values ready, outcome = .ok values ready → ready.activations.length < Goose.Core.maxCallDepth →
        let activation : RuntimeActivation := ⟨context.impl, ready.nextAct, implementation.vars, [], []⟩
        let activated := { ready with nextAct := ready.nextAct + 1, activations := activation :: ready.activations }
        let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
        SourceHistory config fuel (path ++ [1]) (.boundActivation activation pre implementation.body origin) activated
          (enterActivation fuel config activation pre implementation.body origin activated)) :
      SourceHistory config (fuel + 1) path (.callWith environment contextId arguments origin) before
        (callWithResult fuel config context implementation origin outcome)
  | callOne {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[]) :
      SourceHistory config 1 path (.call environment contextId origin) before (.stop .timeout before)
  | callDepth {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
      (depth : Goose.Core.maxCallDepth ≤ before.activations.length) :
      SourceHistory config (fuel + 2) path (.call environment contextId origin) before (.stop .timeout before)
  | callEnter {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      {outcome : ExecutionStep (List Carrier)}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
      (depth : before.activations.length < Goose.Core.maxCallDepth)
      (child : SourceHistory config (fuel + 1) (path ++ [0])
        (.activation ⟨context.impl, before.nextAct, implementation.vars, [], []⟩ implementation.body origin)
        { before with nextAct := before.nextAct + 1, activations := (⟨context.impl, before.nextAct, implementation.vars, [], []⟩ : RuntimeActivation) :: before.activations } outcome) :
      SourceHistory config (fuel + 2) path (.call environment contextId origin) before
        (callDeliveryResult (fuel + 1) config origin outcome)
  | boundBlock {fuel : Nat} {path : List Nat} {environment : RuntimeActivation}
      {pre : List (Goose.Core.VarId × Value)} {scope : Nat} {statements : List Stmt} {before : ExecutionState}
      (body : ∀ ready, bindAll environment.act before.nextScope pre { before with nextScope := before.nextScope + 1 } = .ok () ready →
        SourceHistory config fuel (path ++ [0])
          (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements) ready
          (execStmts fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements ready)) :
      SourceHistory config (fuel + 1) path (.blockWith environment pre (.mk scope statements none)) before
        (execBlock (fuel + 1) config environment pre [] (.mk scope statements none) before)
  | boundLoopBody {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)}
      {body : Block} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.blockWith environment pre body) (loopStart environment before)
        (execBlock fuel config environment pre [] body (loopStart environment before))) :
      SourceHistory config (fuel + 1) path (.loopBodyWith environment pre body) before
        (Goose.Construct.loopBody (fuel + 1) config environment pre body before)
  | whileLoop {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {condition : Expr} {body : Block}
      {before : ExecutionState}
      (conditionChild : SourceHistory config fuel (path ++ [0]) (.value environment condition) before
        (evalValue fuel config environment condition before))
      (bodyChild : ∀ value middle ready, evalValue fuel config environment condition before = .ok value middle →
        expectBool value middle = .ok true ready →
        SourceHistory config fuel (path ++ [1]) (.loopBody environment body) ready
          (Goose.Construct.loopBody fuel config environment [] body ready))
      (nextChild : ∀ value middle ready flow after, evalValue fuel config environment condition before = .ok value middle →
        expectBool value middle = .ok true ready → Goose.Construct.loopBody fuel config environment [] body ready = .ok flow after →
        (flow = .continuing ∨ ∃ value, flow = .normal value) →
        SourceHistory config fuel (path ++ [2]) (.whileLoop environment condition body) after
          (execWhile fuel config environment condition body after)) :
      SourceHistory config (fuel + 1) path (.whileLoop environment condition body) before
        (execWhile (fuel + 1) config environment condition body before)
  | loopBody {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {body : Block} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.block environment body)
        (loopStart environment before)
        (execBlock fuel config environment [] [] body
          (loopStart environment before))) :
      SourceHistory config (fuel + 1) path (.loopBody environment body) before
        (Goose.Construct.loopBody (fuel + 1) config environment [] body before)
  | eachLoop {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {localVar : Goose.Core.VarId}
      {index : Option Goose.Core.VarId} {byRef : Bool} {body : Block} {view : RuntimeView} {current : Nat} {before : ExecutionState}
      (bodyChild : ∀ count countReady pre ready, eachCount fuel config view before = .ok count countReady →
        current < count → eachElement fuel config localVar index byRef view current countReady = .ok pre ready →
        SourceHistory config fuel (path ++ [0]) (.loopBodyWith environment pre body) ready
          (Goose.Construct.loopBody fuel config environment pre body ready))
      (nextChild : ∀ count countReady pre ready flow after, eachCount fuel config view before = .ok count countReady →
        current < count → eachElement fuel config localVar index byRef view current countReady = .ok pre ready →
        Goose.Construct.loopBody fuel config environment pre body ready = .ok flow after →
        (flow = .continuing ∨ ∃ value, flow = .normal value) →
        SourceHistory config fuel (path ++ [1]) (.eachLoop environment localVar index byRef body view (current + 1)) after
          (execEach fuel config environment localVar index byRef body view (current + 1) after)) :
      SourceHistory config (fuel + 1) path (.eachLoop environment localVar index byRef body view current) before
        (eachCountResult fuel config environment localVar index byRef body view current (eachCount fuel config view before))
  | eachStatement {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {localVar : Goose.Core.VarId}
      {index : Option Goose.Core.VarId} {view : View} {byRef : Bool} {body : Block} {origin : Goose.Core.OriginId} {before : ExecutionState}
      (viewChild : SourceHistory config fuel (path ++ [0]) (.view environment view) before
        (evalView fuel config environment view before))
      (loopChild : ∀ runtime ready, evalView fuel config environment view before = .ok runtime ready →
        SourceHistory config fuel (path ++ [1]) (.eachLoop environment localVar index byRef body runtime 0) ready
          (execEach fuel config environment localVar index byRef body runtime 0 ready)) :
      SourceHistory config (fuel + 1) path (.statement environment (.forEach localVar index view byRef body origin)) before
        (execStmt (fuel + 1) config environment (.forEach localVar index view byRef body origin) before)
  | rangeLoop {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {localVar : Goose.Core.VarId}
      {ty : Goose.Core.IntTy} {first last : Int} {body : Block} {before : ExecutionState}
      (bodyChild : first < last → SourceHistory config fuel (path ++ [0])
        (.loopBodyWith environment [(localVar, .int ty first)] body) before
        (Goose.Construct.loopBody fuel config environment [(localVar, .int ty first)] body before))
      (nextChild : ∀ flow after, first < last →
        Goose.Construct.loopBody fuel config environment [(localVar, .int ty first)] body before = .ok flow after →
        (flow = .continuing ∨ ∃ value, flow = .normal value) →
        SourceHistory config fuel (path ++ [1]) (.rangeLoop environment localVar ty (first + 1) last body) after
          (execRange fuel config environment localVar ty (first + 1) last body after)) :
      SourceHistory config (fuel + 1) path (.rangeLoop environment localVar ty first last body) before
        (execRange (fuel + 1) config environment localVar ty first last body before)
  | rangeStatement {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {localVar : Goose.Core.VarId}
      {first last : Expr} {body : Block} {origin : Goose.Core.OriginId} {before : ExecutionState}
      (firstChild : SourceHistory config fuel (path ++ [0]) (.value environment first) before
        (evalValue fuel config environment first before))
      (lastChild : ∀ firstValue middle ty low ready, evalValue fuel config environment first before = .ok firstValue middle →
        expectInt firstValue middle = .ok (ty, low) ready →
        SourceHistory config fuel (path ++ [1]) (.value environment last) ready
          (evalValue fuel config environment last ready))
      (loopChild : ∀ firstValue middle ty low ready lastValue lastState otherTy high checked final,
        evalValue fuel config environment first before = .ok firstValue middle →
        expectInt firstValue middle = .ok (ty, low) ready →
        evalValue fuel config environment last ready = .ok lastValue lastState →
        expectInt lastValue lastState = .ok (otherTy, high) checked → sameIntType ty otherTy checked = .ok () final →
        SourceHistory config fuel (path ++ [2]) (.rangeLoop environment localVar ty low high body) final
          (execRange fuel config environment localVar ty low high body final)) :
      SourceHistory config (fuel + 1) path (.statement environment (.forRange localVar first last body origin)) before
        (execStmt (fuel + 1) config environment (.forRange localVar first last body origin) before)
  | whileStatement {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {condition : Expr} {body : Block}
      {origin : Goose.Core.OriginId} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.whileLoop environment condition body) before
        (execWhile fuel config environment condition body before)) :
      SourceHistory config (fuel + 1) path (.statement environment (.while condition body origin)) before
        (execStmt (fuel + 1) config environment (.while condition body origin) before)
  | omittedBound (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (count : Nat)
      (defaultValue : Int) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.bound environment count defaultValue .omitted) before (.ok defaultValue before)
  | expressionBound {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {count : Nat}
      {defaultValue : Int} {operand : Expr} {fromEnd : Bool} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before
        (evalValue fuel config environment operand before)) :
      SourceHistory config (fuel + 1) path (.bound environment count defaultValue
        (if fromEnd then .fromEnd operand else .expr operand)) before
        (evalBound (fuel + 1) config environment count defaultValue
          (if fromEnd then .fromEnd operand else .expr operand) before)
  | localPlace (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.place environment (.var localVar)) before
        (evalPlace (fuel + 1) config environment (.var localVar) before)
  | globalPlace (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (global : Goose.Core.GlobalId)
      (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.place environment (.global global)) before
        (evalPlace (fuel + 1) config environment (.global global) before)
  | dereferencePlace {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operand : Expr} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before
        (evalValue fuel config environment operand before)) :
      SourceHistory config (fuel + 1) path (.place environment (.deref operand)) before
        (evalPlace (fuel + 1) config environment (.deref operand) before)
  | fieldPlace {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {owner : Place} {index : Nat} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.place environment owner) before
        (evalPlace fuel config environment owner before)) :
      SourceHistory config (fuel + 1) path (.place environment (.field owner index)) before
        (evalPlace (fuel + 1) config environment (.field owner index) before)
  | elementPlace {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {view : View} {operand : Expr}
      {origin : Goose.Core.OriginId} {before : ExecutionState}
      (viewChild : SourceHistory config fuel (path ++ [0]) (.view environment view) before
        (evalView fuel config environment view before))
      (indexChild : ∀ value ready, evalView fuel config environment view before = .ok value ready →
        SourceHistory config fuel (path ++ [1]) (.value environment operand) ready
          (evalValue fuel config environment operand ready)) :
      SourceHistory config (fuel + 1) path (.place environment (.elem view operand origin)) before
        (evalPlace (fuel + 1) config environment (.elem view operand origin) before)
  | placeView {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {place : Place} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.place environment place) before
        (evalPlace fuel config environment place before)) :
      SourceHistory config (fuel + 1) path (.view environment (.of place)) before
        (evalView (fuel + 1) config environment (.of place) before)
  | valueView {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operand : Expr} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before
        (evalValue fuel config environment operand before)) :
      SourceHistory config (fuel + 1) path (.view environment (.val operand)) before
        (evalView (fuel + 1) config environment (.val operand) before)
  | readValue {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {place : Place} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.place environment place) before
        (evalPlace fuel config environment place before)) :
      SourceHistory config (fuel + 1) path (.value environment (.read place)) before
        (evalValue (fuel + 1) config environment (.read place) before)
  | referenceValue {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {mutability : Goose.Core.Mutability}
      {place : Place} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.place environment place) before
        (evalPlace fuel config environment place before)) :
      SourceHistory config (fuel + 1) path (.value environment (.ref mutability place)) before
        (evalValue (fuel + 1) config environment (.ref mutability place) before)
  | lengthValue {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {view : View} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.view environment view) before
        (evalView fuel config environment view before)) :
      SourceHistory config (fuel + 1) path (.value environment (.len view)) before
        (evalValue (fuel + 1) config environment (.len view) before)
  | popValue {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {owner : Place}
      {origin : Goose.Core.OriginId} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.place environment owner) before
        (evalPlace fuel config environment owner before)) :
      SourceHistory config (fuel + 1) path (.value environment (.pop owner origin)) before
        (evalValue (fuel + 1) config environment (.pop owner origin) before)
  | sliceValue {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {mutability : Goose.Core.Mutability}
      {view : View} {lo hi : Bound} {origin : Goose.Core.OriginId} {before : ExecutionState}
      (viewChild : SourceHistory config fuel (path ++ [0]) (.view environment view) before
        (evalView fuel config environment view before))
      (loChild : ∀ value middle, evalView fuel config environment view before = .ok value middle →
        SourceHistory config fuel (path ++ [1]) (.bound environment value.count 0 lo) middle
          (evalBound fuel config environment value.count 0 lo middle))
      (hiChild : ∀ value middle low ready, evalView fuel config environment view before = .ok value middle →
        evalBound fuel config environment value.count 0 lo middle = .ok low ready →
        SourceHistory config fuel (path ++ [2]) (.bound environment value.count value.count hi) ready
          (evalBound fuel config environment value.count value.count hi ready)) :
      SourceHistory config (fuel + 1) path (.value environment (.slice mutability view lo hi origin)) before
        (evalValue (fuel + 1) config environment (.slice mutability view lo hi origin) before)
  | printArgumentText (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (text : String)
      (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.printArgument environment (.text text)) before (.ok text.toUTF8 before)
  | printArgumentExpression {fuel : Nat} {path : List Nat} {environment : RuntimeActivation}
      {expression : Expr} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment expression) before
        (evalValue fuel config environment expression before)) :
      SourceHistory config (fuel + 1) path (.printArgument environment (.expr expression)) before
        (evalPrintArg (fuel + 1) config environment (.expr expression) before)
  | printArgumentView {fuel : Nat} {path : List Nat} {environment : RuntimeActivation}
      {view : View} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.view environment view) before
        (evalView fuel config environment view before)) :
      SourceHistory config (fuel + 1) path (.printArgument environment (.view view)) before
        (evalPrintArg (fuel + 1) config environment (.view view) before)
  | printArguments (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (arguments : List PrintArg)
      (origin : Goose.Core.OriginId) (before : ExecutionState)
      (children : ∀ outcome visits,
        OperandReplay (evalPrintArg fuel config environment) 0 arguments [] before outcome visits →
        ∀ visit ∈ visits, SourceHistory config fuel (path ++ [visit.ordinal]) (.printArgument environment visit.operand)
          visit.before visit.outcome) :
      SourceHistory config (fuel + 1) path (.statement environment (.print arguments origin)) before
        (execStmt (fuel + 1) config environment (.print arguments origin) before)
  | printText (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (text : String)
      (origin : Goose.Core.OriginId) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.statement environment (.print [.text text] origin)) before
        (execStmt (fuel + 1) config environment (.print [.text text] origin) before)
  | builderBytes (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (destination : Goose.Core.DestinationId) (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId)
      (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.builder environment destination (.bytes ty bytes origin)) before
        (buildExpr (fuel + 1) config environment destination (.bytes ty bytes origin) before)
  | builderArray (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (incoming : Goose.Core.DestinationId) (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId)
      (before : ExecutionState)
      (elements : ∀ current prepared ready pending element outcome visits,
        liftConstruction origin (renewReceivingDestination incoming) before = .ok current prepared →
        getDestination current prepared = .ok pending ready →
        elementType pending.capability.logicalType = some element →
        OperandReplay (fun operand => buildElement fuel config environment current element operand) 0 operands [] ready outcome visits →
        ∀ visit ∈ visits, SourceHistory config fuel (path ++ [visit.ordinal])
          (.element environment current element visit.operand) visit.before visit.outcome) :
      SourceHistory config (fuel + 1) path (.builder environment incoming (.arrLit ty operands origin)) before
        (buildExpr (fuel + 1) config environment incoming (.arrLit ty operands origin) before)
  | fixedElement {fuel : Nat} {path : List Nat} {environment : RuntimeActivation}
      {parent : Goose.Core.DestinationId} {element : Ty} {operand : Expr} {before : ExecutionState}
      {outcome : ExecutionStep Value} (fixed : element.nonfixed = false)
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome) :
      SourceHistory config (fuel + 1) path (.element environment parent element operand) before
        (fixedElementContinuation fuel config parent element operand outcome)
  | nonfixedElement {fuel : Nat} {path : List Nat} {environment : RuntimeActivation}
      {parent : Goose.Core.DestinationId} {element : Ty} {operand : Expr} {before : ExecutionState}
      (nonfixed : element.nonfixed = true)
      (child : ∀ layout layoutReady destination ready,
        receivingLayout config.layout element before = .ok layout layoutReady →
        receivingAction (expressionOrigin operand) parent (fun current => openChild current element layout) layoutReady =
          .ok destination ready →
        SourceHistory config fuel (path ++ [0]) (.builder environment destination operand) ready
          (buildExpr fuel config environment destination operand ready)) :
      SourceHistory config (fuel + 1) path (.element environment parent element operand) before
        (buildElement (fuel + 1) config environment parent element operand before)
  | argumentsDone (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (vars : Array LocalVar)
      (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.arguments environment vars [] []) before (.ok [] before)
  | argumentValue {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {vars : Array LocalVar}
      {parameter : Param} {parameters : List Param} {operand : Expr} {arguments : List Arg}
      {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome)
      (tail : ∀ value middle, outcome = .ok value middle →
        SourceHistory config fuel (path ++ [1]) (.arguments environment vars parameters arguments) middle
          (evalArguments fuel config environment vars parameters arguments middle)) :
      SourceHistory config (fuel + 1) path (.arguments environment vars (parameter :: parameters) (.byVal operand :: arguments))
        before (argumentResult fuel config environment vars parameters arguments outcome)
  | argumentConstruct {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {vars : Array LocalVar}
      {parameter : Param} {parameters : List Param} {operand : Expr} {arguments : List Arg} {before : ExecutionState}
      (materialized : ∀ localVar count, vars[parameter.var]? = some localVar →
        ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = some count →
        SourceHistory config fuel (path ++ [0]) (.value environment operand) before
          (evalValue fuel config environment operand before))
      (direct : ∀ localVar destination ready, vars[parameter.var]? = some localVar →
        ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none →
        newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
          (producerCount? ⟨config.module, environment.vars⟩ operand) before = .ok destination ready →
        SourceHistory config fuel (path ++ [0]) (.builder environment destination operand) ready
          (buildExpr fuel config environment destination operand ready))
      (tail : ∀ value middle, argumentValue fuel config environment vars parameter (.construct operand) before = .ok value middle →
        SourceHistory config fuel (path ++ [1]) (.arguments environment vars parameters arguments) middle
          (evalArguments fuel config environment vars parameters arguments middle)) :
      SourceHistory config (fuel + 1) path (.arguments environment vars (parameter :: parameters) (.construct operand :: arguments)) before
        (evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.construct operand :: arguments) before)
  | argumentReference {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {vars : Array LocalVar}
      {parameter : Param} {parameters : List Param} {mutability : Goose.Core.Mutability} {place : Place} {arguments : List Arg}
      {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.place environment place) before
        (evalPlace fuel config environment place before))
      (tail : ∀ location middle, evalPlace fuel config environment place before = .ok location middle →
        SourceHistory config fuel (path ++ [1]) (.arguments environment vars parameters arguments) middle
          (evalArguments fuel config environment vars parameters arguments middle)) :
      SourceHistory config (fuel + 1) path
        (.arguments environment vars (parameter :: parameters) (.byRef mutability place :: arguments)) before
        (evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.byRef mutability place :: arguments) before)
  | scalarBuilder (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (incoming : Goose.Core.DestinationId) (expression : Expr) (before : ExecutionState) (scalar : ScalarExpression expression)
      (child : ∀ destination ready,
        liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) before = .ok destination ready →
        SourceHistory config fuel (path ++ [0]) (.value environment expression) ready
          (evalValue fuel config environment expression ready)) :
      SourceHistory config (fuel + 1) path (.builder environment incoming expression) before
        (buildExpr (fuel + 1) config environment incoming expression before)
  | fillBuilder (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId)
      (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState)
      (valueChild : ∀ destination ready,
        liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready → element.nonfixed = false →
        SourceHistory config fuel (path ++ [0]) (.value environment operand) ready (evalValue fuel config environment operand ready))
      (builderChild : ∀ destination ready source allocated,
        liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready → element.nonfixed = true →
        newDestination config.layout environment.act element .value origin none none ready = .ok source allocated →
        SourceHistory config fuel (path ++ [0]) (.builder environment source operand) allocated (buildExpr fuel config environment source operand allocated)) :
      SourceHistory config (fuel + 1) path (.builder environment incoming (.fill (.arr element count) operand origin)) before
        (buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand origin) before)
  | supportedBuilder (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (incoming : Goose.Core.DestinationId) (expression : Expr) (before : ExecutionState) (supported : SupportedValue expression)
      (valueChild : ∀ destination ready,
        liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) before = .ok destination ready →
        supportedBuilderNeedsValue expression = true →
        SourceHistory config fuel (path ++ [0]) (.value environment (supportedBuilderOperand expression)) ready
          (evalValue fuel config environment (supportedBuilderOperand expression) ready))
      (builderChild : ∀ destination ready element count operand origin source allocated,
        liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) before = .ok destination ready →
        expression = .fill (.arr element count) operand origin → element.nonfixed = true →
        newDestination config.layout environment.act element .value origin none none ready = .ok source allocated →
        SourceHistory config fuel (path ++ [0]) (.builder environment source operand) allocated
          (buildExpr fuel config environment source operand allocated)) :
      SourceHistory config (fuel + 1) path (.builder environment incoming expression) before
        (buildExpr (fuel + 1) config environment incoming expression before)
  | valueProducer (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (channels : List Channel)
      (expression : Expr) (before : ExecutionState) (shape : ValueProducerExpression expression)
      (valueChild : ∀ selected ready,
        prepareProducerCallChannels environment expression channels before = .ok selected ready →
        (selected = [] ∨ ∃ ty, selected = [.register ty]) →
        SourceHistory config fuel (path ++ [0]) (.value environment expression) ready
          (evalValue fuel config environment expression ready))
      (builderChild : ∀ destination ready,
        prepareProducerCallChannels environment expression channels before = .ok [.construct destination] ready →
        SourceHistory config fuel (path ++ [0]) (.builder environment destination expression) ready
          (buildExpr fuel config environment destination expression ready)) :
      SourceHistory config (fuel + 1) path (.producerWith environment channels expression) before
        (evalProduce (fuel + 1) config environment channels expression before)
  | producerChannelCall (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (channels : List Channel)
      (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) (before : ExecutionState)
      (callee : ∀ selected ready,
        prepareProducerCallChannels environment (.call context arguments origin) channels before = .ok selected ready →
        SourceHistory config fuel (path ++ [0]) (.channelCall environment context arguments selected origin) ready
          (invokeCall fuel config environment context arguments selected origin ready)) :
      SourceHistory config (fuel + 1) path (.producerWith environment channels (.call context arguments origin)) before
        (evalProduce (fuel + 1) config environment channels (.call context arguments origin) before)
  | valueChannelCall (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) (before : ExecutionState)
      (callee : ∀ id implementation lookupReady channels ready,
        getImplementation config context before = .ok (id, implementation) lookupReady →
        channelsFor config.layout environment.act implementation.results.toList origin lookupReady = .ok channels ready →
        SourceHistory config fuel (path ++ [0]) (.channelCall environment context arguments channels origin) ready
          (invokeCall fuel config environment context arguments channels origin ready)) :
      SourceHistory config (fuel + 1) path (.value environment (.call context arguments origin)) before
        (evalValue (fuel + 1) config environment (.call context arguments origin) before)
  | channelCall (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
      (origin : Goose.Core.OriginId) (before : ExecutionState)
      (argumentChildren : ∀ id implementation lookupReady callableChannels ready,
        getImplementation config context before = .ok (id, implementation) lookupReady →
        channels.length = implementation.results.size →
        prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels ready →
        SourceHistory config fuel (path ++ [0]) (.arguments environment implementation.vars implementation.params.toList arguments) ready
          (evalArguments fuel config environment implementation.vars implementation.params.toList arguments ready))
      (activationChildren : ∀ id implementation lookupReady callableChannels argumentsReady values valuesReady refreshed activationReady,
        getImplementation config context before = .ok (id, implementation) lookupReady →
        channels.length = implementation.results.size →
        prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady →
        evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady = .ok values valuesReady →
        refreshCallableChannels callableChannels origin valuesReady = .ok refreshed activationReady →
        activationReady.activations.length < Goose.Core.maxCallDepth →
        let activation : RuntimeActivation := ⟨id, activationReady.nextAct, implementation.vars, [], refreshed⟩
        let activated := { activationReady with nextAct := activationReady.nextAct + 1, activations := activation :: activationReady.activations }
        let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
        SourceHistory config fuel (path ++ [1]) (.boundActivation activation pre implementation.body origin) activated
          (enterActivation fuel config activation pre implementation.body origin activated)) :
      SourceHistory config (fuel + 1) path (.channelCall environment context arguments channels origin) before
        (invokeCall (fuel + 1) config environment context arguments channels origin before)
  | ifStatement {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {condition : Expr}
      {yes : Block} {no : Option Block} {origin : Goose.Core.OriginId} {before : ExecutionState}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment condition) before
        (evalValue fuel config environment condition before))
      (yesChild : ∀ value middle ready, evalValue fuel config environment condition before = .ok value middle →
        expectBool value middle = .ok true ready →
        SourceHistory config fuel (path ++ [1]) (.block environment yes) ready
          (execBlock fuel config environment [] [] yes ready))
      (noChild : ∀ value middle ready block, evalValue fuel config environment condition before = .ok value middle →
        expectBool value middle = .ok false ready → no = some block →
        SourceHistory config fuel (path ++ [2]) (.block environment block) ready
          (execBlock fuel config environment [] [] block ready)) :
      SourceHistory config (fuel + 1) path (.statement environment (.ifS condition yes no origin)) before
        (execStmt (fuel + 1) config environment (.ifS condition yes no origin) before)
  | declaration (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState)
      (fixed : ∀ descriptor root ready, environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = false →
        rootOf environment localVar before = .ok root ready →
        SourceHistory config fuel (path ++ [0]) (.value environment expression) ready (evalValue fuel config environment expression ready))
      (materialized : ∀ descriptor root rootReady implementation ready count,
        environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
        rootOf environment localVar before = .ok root rootReady →
        config.module.impls[environment.implementation]? = some implementation →
        DeclarationFallback environment implementation localVar origin rootReady ready →
        ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count →
        SourceHistory config fuel (path ++ [0]) (.value environment expression) ready (evalValue fuel config environment expression ready))
      (direct : ∀ descriptor root rootReady implementation ready destination buildReady,
        environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
        rootOf environment localVar before = .ok root rootReady →
        config.module.impls[environment.implementation]? = some implementation →
        DeclarationFallback environment implementation localVar origin rootReady ready →
        ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = none →
        newDestination config.layout environment.act descriptor.ty .value origin none
          (producerCount? ⟨config.module, environment.vars⟩ expression) ready = .ok destination buildReady →
        SourceHistory config fuel (path ++ [0]) (.builder environment destination expression) buildReady
          (buildExpr fuel config environment destination expression buildReady))
      (named : ∀ descriptor root rootReady implementation result index incoming selected selectedReady pending ready destination renewedReady buildReady,
        environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
        rootOf environment localVar before = .ok root rootReady →
        config.module.impls[environment.implementation]? = some implementation →
        (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index) →
        environment.channels[index]? = some (.construct incoming) →
        liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady →
        getDestination selected selectedReady = .ok pending ready → pending.capability.request = .value →
        liftConstruction origin (renewReceivingDestination incoming) ready = .ok destination renewedReady →
        liftConstruction origin (prepareNamedBinding destination descriptor.ty) renewedReady = .ok () buildReady →
        SourceHistory config fuel (path ++ [0]) (.builder environment destination expression) buildReady
          (buildExpr fuel config environment destination expression buildReady)) :
      SourceHistory config (fuel + 1) path (.statement environment (.letS localVar expression origin)) before
        (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)
  | expression {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operand : Expr}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome) :
      SourceHistory config (fuel + 1) path (.statement environment (.expr operand origin)) before
        (expressionStatementResult outcome)
  | done (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.statements environment []) before (.ok (.normal .unit) before)
  | next {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {statement : Stmt} {rest : List Stmt}
      {before : ExecutionState} {outcome : ExecutionStep Flow}
      (head : SourceHistory config fuel (path ++ [0]) (.statement environment statement) before outcome)
      (tail : ∀ value middle, outcome = .ok (.normal value) middle →
        SourceHistory config fuel (path ++ [1]) (.statements environment rest) middle
          (execStmts fuel config environment rest middle)) :
      SourceHistory config (fuel + 1) path (.statements environment (statement :: rest)) before
        (sequenceResult fuel config environment rest outcome)
  | discard {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {expression : Expr}
      {before : ExecutionState} {outcome : ExecutionStep Value} (supported : SupportedValue expression)
      (child : SourceHistory config fuel (path ++ [0]) (.value environment expression) before outcome) :
      SourceHistory config (fuel + 1) path (.producer environment expression) before (discardValue outcome)

theorem SourceHistory.sound (history : SourceHistory config fuel path operation before outcome) :
    execute fuel config operation before = outcome := by
  induction history with
  | timeout path operation before => cases operation <;> simp [execute, evalValue, execStmt, execStmts, execBlock, execActivationBody, enterActivation, invokeCall, evalArguments, evalBound, evalPlace, evalView, execWhile, execRange, execEach, Goose.Construct.loopBody, evalPrintArg, buildExpr, buildElement, evalProduce, Goose.Construct.timeout, EvalM.stop]
  | integer | boolean => simp [execute, evalValue, pure]
  | declaration | valueNonfixedArray | valueNonfixedFill | fillBuilder | valueBytes | builderArray | aggregate | unary | conversion | comparison | binary | logical | channelCall | valueChannelCall | producerChannelCall | boundActivationTail | supportedBuilder | valueProducer | scalarBuilder => rfl
  | @negation fuel path environment operand before outcome child ih =>
      simp only [execute] at ih ⊢
      simp only [evalValue, bind, ih, negationResult]
      cases outcome <;> rfl
  | @fill fuel path environment element count operand origin before outcome fixed child ih =>
      simp only [execute] at ih ⊢
      simp only [evalValue, fixed, Bool.false_eq_true, ↓reduceIte, bind, ih, fillResult]
      cases outcome <;> rfl
  | @singleton fuel path environment operand before outcome child ih =>
      simp only [execute] at ih ⊢
      simpa [evalValue, bind] using ih
  | @conditional fuel path environment condition yes no origin before outcome child branch ihChild ihBranch =>
      simp only [execute] at ihChild ⊢
      simp only [evalValue, bind, ihChild, conditionalResult]
      cases outcome with
      | ok value state =>
          simp only
          cases result : expectBool value state with
          | ok selected ready => simp only [result]; cases selected <;> rfl
          | stop | escape | jump => simp only [result]
      | stop | escape | jump => rfl
  | @block fuel path environment scope statements before outcome body ihBody =>
      simp only [execute] at ihBody ⊢
      have bound : bindAll environment.act before.nextScope [] { before with nextScope := before.nextScope + 1 } =
          .ok () { before with nextScope := before.nextScope + 1 } := by simp [bindAll, bind, pure]
      obtain ⟨actual, visits, replay, execution⟩ := execBlock_statementReplay fuel config environment [] [] scope
        statements none before { before with nextScope := before.nextScope + 1 } bound
      rw [execution, ← replay.sound, ihBody]
  | @activationBody fuel path activation scope statements before outcome body ihBody =>
      simp only [execute] at ihBody ⊢
      rw [activationBody_source, ihBody]
  | @activation fuel path activation block origin before body ihBody =>
      simp only [execute]
      exact activationEnter_source fuel config activation block origin before
  | @valueCall fuel path environment contextId origin before context implementation outcome contextFound
      implementationFound resultsEmpty child ih =>
      simp only [execute] at ih ⊢
      rw [valueCall_source fuel config environment contextId context implementation origin before
        contextFound implementationFound resultsEmpty, ih]
  | @valueCallWith fuel path environment contextId arguments origin before context implementation outcome contextFound
      implementationFound resultsEmpty child ih =>
      simp only [execute] at ih ⊢
      rw [valueCallWith_source fuel config environment contextId arguments context implementation origin before
        contextFound implementationFound resultsEmpty, ih]
  | @producerCallWith fuel path environment contextId arguments origin before outcome child ih =>
      simp only [execute] at ih ⊢
      rw [producerCallWith_source fuel config environment contextId arguments origin before, ih]
  | @producerCall fuel path environment contextId origin before outcome child ih =>
      simp only [execute] at ih ⊢
      rw [producerCall_source fuel config environment contextId origin before, ih]
  | @boundActivationBody fuel path activation pre scope statements before body ihBody =>
      simp only [execute]
      exact boundActivationBody_source fuel config activation pre scope statements before
  | boundActivation => rfl
  | @callWith fuel path environment contextId arguments origin before context implementation outcome contextFound
      implementationFound resultsEmpty argumentsHistory activationHistory ihArguments ihActivation =>
      simp only [execute] at ihArguments ⊢
      rw [callWith_source fuel config environment contextId arguments origin context implementation before
        contextFound implementationFound resultsEmpty, ihArguments]
  | callOne contextFound implementationFound resultsEmpty =>
      exact emptyCall_one _ _ _ _ _ _ _ contextFound implementationFound resultsEmpty
  | callDepth contextFound implementationFound parametersEmpty resultsEmpty depth =>
      exact emptyCall_depth _ _ _ _ _ _ _ _ contextFound implementationFound parametersEmpty resultsEmpty depth
  | @callEnter fuel path environment contextId origin before context implementation outcome contextFound
      implementationFound parametersEmpty resultsEmpty depth child ih =>
      simp only [execute] at ih ⊢
      rw [emptyCall_enter fuel config environment contextId context implementation origin before
        contextFound implementationFound parametersEmpty resultsEmpty depth]
      simp only [bind, ih, callDeliveryResult]
      cases outcome <;> rfl
  | omittedBound => simp [execute, evalBound, pure]
  | expressionBound | localPlace | globalPlace | dereferencePlace | fieldPlace | elementPlace | placeView | valueView |
    readValue | referenceValue | lengthValue | popValue | sliceValue | boundBlock | boundLoopBody | whileLoop | loopBody | rangeLoop | rangeStatement | eachStatement | whileStatement => rfl
  | printArgumentText => simp [execute, evalPrintArg, pure]
  | printArgumentExpression | printArgumentView | printArguments | printText | ifStatement => rfl
  | builderBytes => rfl
  | @eachLoop fuel path environment localVar index byRef body view current before bodyChild nextChild ihBody ihNext =>
      simp only [execute]
      exact eachCount_source fuel config environment localVar index byRef body view current before
  | @fixedElement fuel path environment parent element operand before outcome fixed child ih =>
      simp only [execute] at ih ⊢
      rw [fixedElement_execution fuel config environment parent element operand before fixed, ih]
  | nonfixedElement => rfl
  | argumentConstruct | argumentReference => rfl
  | argumentsDone => simp [execute, evalArguments, pure]
  | @argumentValue fuel path environment vars parameter parameters operand arguments before outcome child tail ihChild ihTail =>
      simp only [execute] at ihChild ⊢
      rw [valueArgument_source fuel config environment vars parameter parameters operand arguments before, ihChild]
  | @expression fuel path environment operand origin before outcome child ih =>
      simp only [execute] at ih ⊢
      simp only [execStmt, bind, ih, expressionStatementResult]
      cases outcome <;> rfl
  | done => simp [execute, execStmts, pure]
  | @next fuel path environment statement rest before outcome head tail ihHead ihTail =>
      simp only [execute] at ihHead ⊢
      simp only [execStmts, bind, ihHead, sequenceResult]
      cases outcome with
      | ok flow state => cases flow <;> rfl
      | stop | escape | jump => rfl
  | @discard fuel path environment expression before outcome supported child ih =>
      simp only [execute] at ih ⊢
      rw [emptyProducer_source fuel config environment expression before supported, ih]

theorem ValueHistory.toSource (history : ValueHistory config environment fuel path expression before outcome) :
    SourceHistory config fuel path (.value environment expression) before outcome := by
  induction history with
  | timeout => exact .timeout _ _ _
  | integer => exact .integer _ _ _ _ _ _
  | boolean => exact .boolean _ _ _ _ _
  | negation child ih => exact .negation ih
  | fill fixed child ih => exact .fill fixed ih

theorem StatementHistory.toSource (history : StatementHistory config environment fuel path statement before outcome) :
    SourceHistory config fuel path (.statement environment statement) before outcome := by
  cases history with
  | timeout => exact .timeout _ _ _
  | expression child => exact .expression (ValueHistory.toSource child)

theorem StatementSequenceHistory.toSource
    (history : StatementSequenceHistory config environment fuel path statements before outcome) :
    SourceHistory config fuel path (.statements environment statements) before outcome := by
  induction history with
  | timeout => exact .timeout _ _ _
  | done => exact .done _ _ _ _
  | next head tail ih => exact .next (StatementHistory.toSource head) ih

theorem ProducerHistory.toSource (history : ProducerHistory config environment fuel path expression before outcome) :
    SourceHistory config fuel path (.producer environment expression) before outcome := by
  cases history with
  | timeout => exact .timeout _ _ _
  | discard supported child => exact .discard supported (ValueHistory.toSource child)

theorem value_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (expression : Expr) (before : ExecutionState) (supported : SupportedValue expression) :
    SourceHistory config fuel path (.value environment expression) before (evalValue fuel config environment expression before) :=
  ValueHistory.toSource (valueHistory_exists fuel config environment path expression before supported)

theorem statements_exist (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (statements : List Stmt) (before : ExecutionState)
    (supported : ∀ statement ∈ statements, SupportedStatement statement) :
    SourceHistory config fuel path (.statements environment statements) before
      (execStmts fuel config environment statements before) :=
  StatementSequenceHistory.toSource (statementSequenceHistory_exists fuel config environment path statements before supported)

inductive SupportedOperation (config : EvalConfig) : {α : Type} → SourceOperation α → Prop
  | value (environment : RuntimeActivation) {expression : Expr} (supported : SupportedValue expression) :
      SupportedOperation config (.value environment expression)
  | valueBytes (environment : RuntimeActivation) (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
      SupportedOperation config (.value environment (.bytes ty bytes origin))
  | fill (environment : RuntimeActivation) (element : Ty) (count : Nat) (origin : Goose.Core.OriginId)
      (operand : Expr) (fixed : (Ty.arr element count).nonfixed = false)
      (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.value environment (.fill (.arr element count) operand origin))
  | aggregate (environment : RuntimeActivation) (expression : Expr) (operands : List Expr)
      (shape : ValueAggregate expression operands)
      (children : ∀ operand ∈ operands, SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.value environment expression)
  | unary (environment : RuntimeActivation) (operation : Goose.Core.UnOp) (operand : Expr) (origin : Goose.Core.OriginId)
      (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.value environment (.un operation operand origin))
  | conversion (environment : RuntimeActivation) (kind : Goose.Core.ConvKind) (target : Ty) (operand : Expr)
      (origin : Goose.Core.OriginId) (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.value environment (.conv kind target operand origin))
  | negation (environment : RuntimeActivation) (operand : Expr)
      (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.value environment (.not operand))
  | comparison (environment : RuntimeActivation) (operation : Goose.Core.CmpOp) (first second : Expr)
      (left : SupportedOperation config (.value environment first))
      (right : SupportedOperation config (.value environment second)) :
      SupportedOperation config (.value environment (.cmp operation first second))
  | binary (environment : RuntimeActivation) (operation : Goose.Core.BinOp) (first second : Expr)
      (origin : Goose.Core.OriginId) (left : SupportedOperation config (.value environment first))
      (right : SupportedOperation config (.value environment second)) :
      SupportedOperation config (.value environment (.bin operation first second origin))
  | logical (environment : RuntimeActivation) (isAnd : Bool) (first second : Expr)
      (left : SupportedOperation config (.value environment first))
      (right : SupportedOperation config (.value environment second)) :
      SupportedOperation config (.value environment (logicalExpression isAnd first second))
  | singleton (environment : RuntimeActivation) (operand : Expr)
      (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.value environment (.values [operand]))
  | conditional (environment : RuntimeActivation) {condition : Expr} {yes no : Block} (origin : Goose.Core.OriginId)
      (conditionSupported : SupportedOperation config (.value environment condition))
      (yesSupported : SupportedOperation config (.block environment yes))
      (noSupported : SupportedOperation config (.block environment no)) :
      SupportedOperation config (.value environment (.ifE condition yes no origin))
  | expression (environment : RuntimeActivation) {operand : Expr} (origin : Goose.Core.OriginId)
      (supported : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.statement environment (.expr operand origin))
  | ifStatement (environment : RuntimeActivation) (condition : Expr) (yes : Block) (no : Option Block)
      (origin : Goose.Core.OriginId) (child : SupportedOperation config (.value environment condition))
      (yesChild : SupportedOperation config (.block environment yes))
      (noChild : ∀ block, no = some block → SupportedOperation config (.block environment block)) :
      SupportedOperation config (.statement environment (.ifS condition yes no origin))
  | empty (environment : RuntimeActivation) : SupportedOperation config (.statements environment [])
  | sequence (environment : RuntimeActivation) {statement : Stmt} {rest : List Stmt}
      (head : SupportedOperation config (.statement environment statement))
      (tail : SupportedOperation config (.statements environment rest)) :
      SupportedOperation config (.statements environment (statement :: rest))
  | block (environment : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (body : ∀ scopedEnvironment, SupportedOperation config (.statements scopedEnvironment statements)) :
      SupportedOperation config (.block environment (.mk scope statements none))
  | activationBody (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (body : ∀ environment, SupportedOperation config (.statements environment statements)) :
      SupportedOperation config (.activationBody activation (.mk scope statements none))
  | activation (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (origin : Goose.Core.OriginId)
      (body : ∀ environment, SupportedOperation config (.statements environment statements)) :
      SupportedOperation config (.activation activation (.mk scope statements none) origin)
  | boundActivationBody (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt)
      (body : ∀ environment, SupportedOperation config (.statements environment statements)) :
      SupportedOperation config (.boundActivationBody activation pre (.mk scope statements none))
  | boundActivation (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt) (origin : Goose.Core.OriginId)
      (body : ∀ environment, SupportedOperation config (.statements environment statements)) :
      SupportedOperation config (.boundActivation activation pre (.mk scope statements none) origin)
  | valueCall (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (callee : SupportedOperation config (.call environment contextId origin)) :
      SupportedOperation config (.value environment (.call contextId [] origin))
  | valueCallWith (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (arguments : List Arg)
      (origin : Goose.Core.OriginId) (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (callee : SupportedOperation config (.callWith environment contextId arguments origin)) :
      SupportedOperation config (.value environment (.call contextId arguments origin))
  | producerCallWith (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (arguments : List Arg)
      (origin : Goose.Core.OriginId) (callee : SupportedOperation config (.callWith environment contextId arguments origin)) :
      SupportedOperation config (.producer environment (.call contextId arguments origin))
  | producerCall (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (callee : SupportedOperation config (.call environment contextId origin)) :
      SupportedOperation config (.producer environment (.call contextId [] origin))
  | callWith (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (arguments : List Arg)
      (origin : Goose.Core.OriginId) (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (argumentsSupported : SupportedOperation config
        (.arguments environment implementation.vars implementation.params.toList arguments))
      (body : ∀ act pre, SupportedOperation config
        (.boundActivation ⟨context.impl, act, implementation.vars, [], []⟩ pre implementation.body origin)) :
      SupportedOperation config (.callWith environment contextId arguments origin)
  | call (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
      (body : ∀ act, SupportedOperation config
        (.activation ⟨context.impl, act, implementation.vars, [], []⟩ implementation.body origin)) :
      SupportedOperation config (.call environment contextId origin)
  | boundBlock (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (scope : Nat) (statements : List Stmt)
      (body : ∀ scopedEnvironment, SupportedOperation config (.statements scopedEnvironment statements)) :
      SupportedOperation config (.blockWith environment pre (.mk scope statements none))
  | boundLoopBody (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
      (child : SupportedOperation config (.blockWith environment pre body)) :
      SupportedOperation config (.loopBodyWith environment pre body)
  | whileLoop (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (conditionChild : SupportedOperation config (.value environment condition))
      (bodyChild : SupportedOperation config (.block environment body)) :
      SupportedOperation config (.whileLoop environment condition body)
  | loopBody (environment : RuntimeActivation) (body : Block)
      (child : SupportedOperation config (.block environment body)) :
      SupportedOperation config (.loopBody environment body)
  | eachLoop (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId)
      (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat)
      (bodyChild : ∀ pre, SupportedOperation config (.loopBodyWith environment pre body)) :
      SupportedOperation config (.eachLoop environment localVar index byRef body view current)
  | eachStatement (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId)
      (view : View) (byRef : Bool) (body : Block) (origin : Goose.Core.OriginId)
      (viewChild : SupportedOperation config (.view environment view))
      (bodyChild : ∀ pre, SupportedOperation config (.loopBodyWith environment pre body)) :
      SupportedOperation config (.statement environment (.forEach localVar index view byRef body origin))
  | rangeLoop (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (ty : Goose.Core.IntTy)
      (first last : Int) (body : Block)
      (bodyChild : ∀ pre, SupportedOperation config (.loopBodyWith environment pre body)) :
      SupportedOperation config (.rangeLoop environment localVar ty first last body)
  | rangeStatement (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (first last : Expr) (body : Block)
      (origin : Goose.Core.OriginId) (firstChild : SupportedOperation config (.value environment first))
      (lastChild : SupportedOperation config (.value environment last))
      (bodyChild : ∀ pre, SupportedOperation config (.loopBodyWith environment pre body)) :
      SupportedOperation config (.statement environment (.forRange localVar first last body origin))
  | whileStatement (environment : RuntimeActivation) (condition : Expr) (body : Block) (origin : Goose.Core.OriginId)
      (child : SupportedOperation config (.whileLoop environment condition body)) :
      SupportedOperation config (.statement environment (.while condition body origin))
  | omittedBound (environment : RuntimeActivation) (count : Nat) (defaultValue : Int) :
      SupportedOperation config (.bound environment count defaultValue .omitted)
  | expressionBound (environment : RuntimeActivation) (count : Nat) (defaultValue : Int) (operand : Expr) (fromEnd : Bool)
      (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.bound environment count defaultValue (if fromEnd then .fromEnd operand else .expr operand))
  | localPlace (environment : RuntimeActivation) (localVar : Goose.Core.VarId) :
      SupportedOperation config (.place environment (.var localVar))
  | globalPlace (environment : RuntimeActivation) (global : Goose.Core.GlobalId) :
      SupportedOperation config (.place environment (.global global))
  | dereferencePlace (environment : RuntimeActivation) (operand : Expr)
      (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.place environment (.deref operand))
  | fieldPlace (environment : RuntimeActivation) (owner : Place) (index : Nat)
      (child : SupportedOperation config (.place environment owner)) :
      SupportedOperation config (.place environment (.field owner index))
  | elementPlace (environment : RuntimeActivation) (view : View) (operand : Expr) (origin : Goose.Core.OriginId)
      (viewChild : SupportedOperation config (.view environment view))
      (indexChild : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.place environment (.elem view operand origin))
  | placeView (environment : RuntimeActivation) (place : Place)
      (child : SupportedOperation config (.place environment place)) :
      SupportedOperation config (.view environment (.of place))
  | valueView (environment : RuntimeActivation) (operand : Expr)
      (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.view environment (.val operand))
  | readValue (environment : RuntimeActivation) (place : Place)
      (child : SupportedOperation config (.place environment place)) :
      SupportedOperation config (.value environment (.read place))
  | referenceValue (environment : RuntimeActivation) (mutability : Goose.Core.Mutability) (place : Place)
      (child : SupportedOperation config (.place environment place)) :
      SupportedOperation config (.value environment (.ref mutability place))
  | lengthValue (environment : RuntimeActivation) (view : View)
      (child : SupportedOperation config (.view environment view)) :
      SupportedOperation config (.value environment (.len view))
  | popValue (environment : RuntimeActivation) (owner : Place) (origin : Goose.Core.OriginId)
      (child : SupportedOperation config (.place environment owner)) :
      SupportedOperation config (.value environment (.pop owner origin))
  | sliceValue (environment : RuntimeActivation) (mutability : Goose.Core.Mutability) (view : View)
      (lo hi : Bound) (origin : Goose.Core.OriginId)
      (viewChild : SupportedOperation config (.view environment view))
      (loChild : ∀ count, SupportedOperation config (.bound environment count 0 lo))
      (hiChild : ∀ count, SupportedOperation config (.bound environment count count hi)) :
      SupportedOperation config (.value environment (.slice mutability view lo hi origin))
  | printArgumentText (environment : RuntimeActivation) (text : String) :
      SupportedOperation config (.printArgument environment (.text text))
  | printArgumentExpression (environment : RuntimeActivation) (expression : Expr)
      (child : SupportedOperation config (.value environment expression)) :
      SupportedOperation config (.printArgument environment (.expr expression))
  | printArgumentView (environment : RuntimeActivation) (view : View)
      (child : SupportedOperation config (.view environment view)) :
      SupportedOperation config (.printArgument environment (.view view))
  | printArguments (environment : RuntimeActivation) (arguments : List PrintArg) (origin : Goose.Core.OriginId)
      (children : ∀ argument ∈ arguments, SupportedOperation config (.printArgument environment argument)) :
      SupportedOperation config (.statement environment (.print arguments origin))
  | printText (environment : RuntimeActivation) (text : String) (origin : Goose.Core.OriginId) :
      SupportedOperation config (.statement environment (.print [.text text] origin))
  | builderBytes (environment : RuntimeActivation) (destination : Goose.Core.DestinationId) (ty : Ty)
      (bytes : List UInt8) (origin : Goose.Core.OriginId) :
      SupportedOperation config (.builder environment destination (.bytes ty bytes origin))
  | builderArray (environment : RuntimeActivation) (incoming : Goose.Core.DestinationId) (ty : Ty)
      (operands : List Expr) (origin : Goose.Core.OriginId)
      (elements : ∀ operand ∈ operands, ∀ current element,
        SupportedOperation config (.element environment current element operand)) :
      SupportedOperation config (.builder environment incoming (.arrLit ty operands origin))
  | fixedElement (environment : RuntimeActivation) (parent : Goose.Core.DestinationId) (element : Ty)
      (operand : Expr) (fixed : element.nonfixed = false)
      (child : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.element environment parent element operand)
  | nonfixedElement (environment : RuntimeActivation) (parent : Goose.Core.DestinationId) (element : Ty)
      (operand : Expr) (nonfixed : element.nonfixed = true)
      (child : ∀ destination, SupportedOperation config (.builder environment destination operand)) :
      SupportedOperation config (.element environment parent element operand)
  | argumentsDone (environment : RuntimeActivation) (vars : Array LocalVar) :
      SupportedOperation config (.arguments environment vars [] [])
  | argumentValue (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param)
      (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (child : SupportedOperation config (.value environment operand))
      (tail : SupportedOperation config (.arguments environment vars parameters arguments)) :
      SupportedOperation config (.arguments environment vars (parameter :: parameters) (.byVal operand :: arguments))
  | argumentConstruct (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param)
      (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (materialized : SupportedOperation config (.value environment operand))
      (direct : ∀ destination, SupportedOperation config (.builder environment destination operand))
      (tail : SupportedOperation config (.arguments environment vars parameters arguments)) :
      SupportedOperation config (.arguments environment vars (parameter :: parameters) (.construct operand :: arguments))
  | argumentReference (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param)
      (parameters : List Param) (mutability : Goose.Core.Mutability) (place : Place) (arguments : List Arg)
      (child : SupportedOperation config (.place environment place))
      (tail : SupportedOperation config (.arguments environment vars parameters arguments)) :
      SupportedOperation config (.arguments environment vars (parameter :: parameters) (.byRef mutability place :: arguments))
  | producer (environment : RuntimeActivation) {expression : Expr} (supported : SupportedValue expression) :
      SupportedOperation config (.producer environment expression)

theorem history_exists (fuel : Nat) (config : EvalConfig) {α : Type} (operation : SourceOperation α)
    (path : List Nat) (before : ExecutionState) (supported : SupportedOperation config operation) :
    SourceHistory config fuel path operation before (execute fuel config operation before) := by
  induction fuel generalizing α operation path before with
  | zero =>
      cases operation <;> simpa [execute, evalValue, execStmt, execStmts, execBlock, execActivationBody, enterActivation, invokeCall, evalArguments, evalBound, evalPlace, evalView, execWhile, execRange, execEach, Goose.Construct.loopBody, evalPrintArg, buildExpr, buildElement, evalProduce,
        Goose.Construct.timeout, EvalM.stop] using (SourceHistory.timeout path _ before)
  | succ fuel ih =>
      cases supported with
      | value environment supported =>
          exact value_exists (fuel + 1) config environment path _ before supported
      | valueBytes environment ty bytes origin => exact .valueBytes fuel path environment ty bytes origin before
      | fill environment element count origin operand fixed childSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          have actual : evalValue (fuel + 1) config environment (.fill (.arr element count) operand origin) before =
              fillResult count (evalValue fuel config environment operand before) := by
            simp only [evalValue, fixed, Bool.false_eq_true, ↓reduceIte, bind, fillResult]
            cases evalValue fuel config environment operand before <;> rfl
          simp only [execute] at child ⊢
          rw [actual]
          exact .fill fixed child
      | aggregate environment expression operands shape childrenSupported =>
          refine .aggregate fuel path environment expression operands before shape ?_
          intro outcome visits replay visit member
          have inMapped : visit.operand ∈ visits.map Invocation.operand := List.mem_map_of_mem member
          rw [replay.sourceOrder] at inMapped
          have inOperands : visit.operand ∈ operands := List.mem_of_mem_take inMapped
          have child := ih (.value environment visit.operand) (path ++ [visit.ordinal]) visit.before
            (childrenSupported visit.operand inOperands)
          simp only [execute] at child
          rw [← visit_executes replay visit member]
          exact child
      | unary environment operation operand origin childSupported =>
          exact .unary (ih (.value environment operand) (path ++ [0]) before childSupported)
      | conversion environment kind target operand origin childSupported =>
          exact .conversion (ih (.value environment operand) (path ++ [0]) before childSupported)
      | negation environment operand childSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          have actual : evalValue (fuel + 1) config environment (.not operand) before =
              Goose.Proofs.ConstructionGhostSourceTransition.negationResult (evalValue fuel config environment operand before) := by
            simp only [evalValue, bind, Goose.Proofs.ConstructionGhostSourceTransition.negationResult]
            cases evalValue fuel config environment operand before <;> rfl
          simp only [execute] at child ⊢
          rw [actual]
          exact .negation child
      | comparison environment operation first second leftSupported rightSupported =>
          have left := ih (.value environment first) (path ++ [0]) before leftSupported
          refine .comparison left ?_
          intro value middle result
          exact ih (.value environment second) (path ++ [1]) middle rightSupported
      | binary environment operation first second origin leftSupported rightSupported =>
          have left := ih (.value environment first) (path ++ [0]) before leftSupported
          refine .binary left ?_
          intro value middle ty number ready result checked
          exact ih (.value environment second) (path ++ [1]) ready rightSupported
      | logical environment isAnd first second leftSupported rightSupported =>
          have left := ih (.value environment first) (path ++ [0]) before leftSupported
          refine .logical left ?_
          intro value middle ready result checked
          exact ih (.value environment second) (path ++ [1]) ready rightSupported
      | singleton environment operand childSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          simpa [execute, evalValue, bind] using (SourceHistory.singleton child)
      | @conditional environment condition yes no origin conditionSupported yesSupported noSupported =>
          have child := ih (.value environment condition) (path ++ [0]) before conditionSupported
          have branch : ∀ value middle selected ready,
              evalValue fuel config environment condition before = .ok value middle →
              expectBool value middle = .ok selected ready →
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
      | @expression environment operand origin supported =>
          have child := ih (.value environment operand) (path ++ [0]) before supported
          have actual : execStmt (fuel + 1) config environment (.expr operand origin) before =
              expressionStatementResult (evalValue fuel config environment operand before) := by
            simp only [execStmt, bind, expressionStatementResult]
            cases evalValue fuel config environment operand before <;> rfl
          simp only [execute]
          rw [actual]
          exact .expression child
      | ifStatement environment condition yes no origin childSupported yesSupported noSupported =>
          refine .ifStatement (ih (.value environment condition) (path ++ [0]) before childSupported) ?_ ?_
          · intro value middle ready result checked
            exact ih (.block environment yes) (path ++ [1]) ready yesSupported
          · intro value middle ready block result checked selected
            exact ih (.block environment block) (path ++ [2]) ready (noSupported block selected)
      | empty environment => simpa [execute, execStmts, pure] using
          (SourceHistory.done fuel path environment before :
            SourceHistory config (fuel + 1) path (.statements environment []) before _)
      | @sequence environment statement rest headSupported tailSupported =>
          have head := ih (.statement environment statement) (path ++ [0]) before headSupported
          have tail : ∀ value middle, execStmt fuel config environment statement before = .ok (.normal value) middle →
              SourceHistory config fuel (path ++ [1]) (.statements environment rest) middle
                (execStmts fuel config environment rest middle) := by
            intro value middle _
            exact ih (.statements environment rest) (path ++ [1]) middle tailSupported
          have actual : execStmts (fuel + 1) config environment (statement :: rest) before =
              sequenceResult fuel config environment rest (execStmt fuel config environment statement before) := by
            simp only [execStmts, bind, sequenceResult]
            cases execStmt fuel config environment statement before with
            | ok flow state => cases flow <;> rfl
            | stop | escape | jump => rfl
          simp only [execute]
          rw [actual]
          exact .next head tail
      | block environment scope statements bodySupported =>
          let scopedEnvironment := { environment with scopes := (scope, before.nextScope) :: environment.scopes }
          let ready := { before with nextScope := before.nextScope + 1 }
          have child := ih (.statements scopedEnvironment statements) (path ++ [0]) ready (bodySupported scopedEnvironment)
          have bound : bindAll environment.act before.nextScope [] ready = .ok () ready := by simp [ready, bindAll, bind, pure]
          obtain ⟨outcome, visits, replay, execution⟩ :=
            execBlock_statementReplay fuel config environment [] [] scope statements none before ready bound
          simp only [execute]
          rw [execution, ← replay.sound]
          exact .block child
      | activationBody activation scope statements bodySupported =>
          let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
          let ready := resultScopeStart activation scope before
          have child := ih (.statements environment statements) (path ++ [0]) ready (bodySupported environment)
          simp only [execute]
          rw [activationBody_source]
          exact .activationBody child
      | activation activation scope statements origin bodySupported =>
          have body : ∀ implementation, config.module.impls[activation.implementation]? = some implementation →
              SourceHistory config fuel (path ++ [0]) (.activationBody activation (.mk scope statements none)) before
                (execActivationBody fuel config activation [] (.mk scope statements none) before) := by
            intro implementation _
            exact ih (.activationBody activation (.mk scope statements none)) (path ++ [0]) before
              (.activationBody activation scope statements bodySupported)
          simp only [execute]
          rw [activationEnter_source]
          exact .activation body
      | boundActivationBody activation pre scope statements bodySupported =>
          simp only [execute]
          rw [boundActivationBody_source]
          refine .boundActivationBody ?_
          intro ready bound
          exact ih (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements)
            (path ++ [0]) ready (bodySupported _)
      | boundActivation activation pre scope statements origin bodySupported =>
          refine .boundActivation ?_
          intro implementation found
          exact ih (.boundActivationBody activation pre (.mk scope statements none)) (path ++ [0]) before
            (.boundActivationBody activation pre scope statements bodySupported)
      | valueCall environment contextId origin context implementation contextFound implementationFound resultsEmpty callee =>
          have child := ih (.call environment contextId origin) (path ++ [0]) before callee
          simp only [execute] at child ⊢
          rw [valueCall_source fuel config environment contextId context implementation origin before
            contextFound implementationFound resultsEmpty]
          exact .valueCall contextFound implementationFound resultsEmpty child
      | valueCallWith environment contextId arguments origin context implementation contextFound implementationFound resultsEmpty callee =>
          have child := ih (.callWith environment contextId arguments origin) (path ++ [0]) before callee
          simp only [execute] at child ⊢
          rw [valueCallWith_source fuel config environment contextId arguments context implementation origin before
            contextFound implementationFound resultsEmpty]
          exact .valueCallWith contextFound implementationFound resultsEmpty child
      | producerCallWith environment contextId arguments origin callee =>
          have child := ih (.callWith environment contextId arguments origin) (path ++ [0]) before callee
          simp only [execute] at child ⊢
          rw [producerCallWith_source]
          exact .producerCallWith child
      | producerCall environment contextId origin callee =>
          have child := ih (.call environment contextId origin) (path ++ [0]) before callee
          simp only [execute] at child ⊢
          rw [producerCall_source]
          exact .producerCall child
      | callWith environment contextId arguments origin context implementation contextFound implementationFound resultsEmpty argumentsSupported bodySupported =>
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
      | call environment contextId origin context implementation contextFound implementationFound parametersEmpty resultsEmpty body =>
          cases fuel with
          | zero =>
              simpa only [execute, emptyCall_one config environment contextId context implementation origin before
                contextFound implementationFound resultsEmpty] using
                (SourceHistory.callOne contextFound implementationFound resultsEmpty :
                  SourceHistory config 1 path (.call environment contextId origin) before _)
          | succ fuel =>
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
      | boundBlock environment pre scope statements bodySupported =>
          refine .boundBlock ?_
          intro ready bound
          exact ih (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements)
            (path ++ [0]) ready (bodySupported _)
      | boundLoopBody environment pre body childSupported =>
          exact .boundLoopBody (ih (.blockWith environment pre body) (path ++ [0]) (loopStart environment before) childSupported)
      | whileLoop environment condition body conditionSupported bodySupported =>
          refine .whileLoop (ih (.value environment condition) (path ++ [0]) before conditionSupported) ?_ ?_
          · intro value middle ready result checked
            exact ih (.loopBody environment body) (path ++ [1]) ready (.loopBody environment body bodySupported)
          · intro value middle ready flow after result checked loopResult continuing
            exact ih (.whileLoop environment condition body) (path ++ [2]) after
              (.whileLoop environment condition body conditionSupported bodySupported)
      | loopBody environment body bodySupported =>
          exact .loopBody (ih (.block environment body) (path ++ [0])
            (loopStart environment before) bodySupported)
      | eachLoop environment localVar index byRef body view current bodySupported =>
          simp only [execute]
          rw [eachCount_source]
          refine .eachLoop ?_ ?_
          · intro count countReady pre ready counted inside selected
            exact ih (.loopBodyWith environment pre body) (path ++ [0]) ready (bodySupported pre)
          · intro count countReady pre ready flow after counted inside selected result continuing
            exact ih (.eachLoop environment localVar index byRef body view (current + 1)) (path ++ [1]) after
              (.eachLoop environment localVar index byRef body view (current + 1) bodySupported)
      | eachStatement environment localVar index view byRef body origin viewSupported bodySupported =>
          refine .eachStatement (ih (.view environment view) (path ++ [0]) before viewSupported) ?_
          intro runtime ready result
          exact ih (.eachLoop environment localVar index byRef body runtime 0) (path ++ [1]) ready
            (.eachLoop environment localVar index byRef body runtime 0 bodySupported)
      | rangeLoop environment localVar ty first last body bodySupported =>
          refine .rangeLoop ?_ ?_
          · intro inside
            exact ih (.loopBodyWith environment [(localVar, .int ty first)] body) (path ++ [0]) before (bodySupported _)
          · intro flow after inside result continuing
            exact ih (.rangeLoop environment localVar ty (first + 1) last body) (path ++ [1]) after
              (.rangeLoop environment localVar ty (first + 1) last body bodySupported)
      | rangeStatement environment localVar first last body origin firstSupported lastSupported bodySupported =>
          refine .rangeStatement (ih (.value environment first) (path ++ [0]) before firstSupported) ?_ ?_
          · intro firstValue middle ty low ready result checked
            exact ih (.value environment last) (path ++ [1]) ready lastSupported
          · intro firstValue middle ty low ready lastValue lastState otherTy high checked final firstResult firstChecked lastResult lastChecked same
            exact ih (.rangeLoop environment localVar ty low high body) (path ++ [2]) final
              (.rangeLoop environment localVar ty low high body bodySupported)
      | whileStatement environment condition body origin childSupported =>
          exact .whileStatement (ih (.whileLoop environment condition body) (path ++ [0]) before childSupported)
      | omittedBound environment count defaultValue =>
          simpa [execute, evalBound, pure] using (SourceHistory.omittedBound fuel path environment count defaultValue before)
      | expressionBound environment count defaultValue operand fromEnd child =>
          exact .expressionBound (ih (.value environment operand) (path ++ [0]) before child)
      | localPlace environment localVar => exact .localPlace fuel path environment localVar before
      | globalPlace environment global => exact .globalPlace fuel path environment global before
      | dereferencePlace environment operand child =>
          exact .dereferencePlace (ih (.value environment operand) (path ++ [0]) before child)
      | fieldPlace environment owner index child =>
          exact .fieldPlace (ih (.place environment owner) (path ++ [0]) before child)
      | elementPlace environment view operand origin viewChild indexChild =>
          refine .elementPlace (ih (.view environment view) (path ++ [0]) before viewChild) ?_
          intro value ready result
          exact ih (.value environment operand) (path ++ [1]) ready indexChild
      | placeView environment place child =>
          exact .placeView (ih (.place environment place) (path ++ [0]) before child)
      | valueView environment operand child =>
          exact .valueView (ih (.value environment operand) (path ++ [0]) before child)
      | readValue environment place child =>
          exact .readValue (ih (.place environment place) (path ++ [0]) before child)
      | referenceValue environment mutability place child =>
          exact .referenceValue (ih (.place environment place) (path ++ [0]) before child)
      | lengthValue environment view child =>
          exact .lengthValue (ih (.view environment view) (path ++ [0]) before child)
      | popValue environment owner origin child =>
          exact .popValue (ih (.place environment owner) (path ++ [0]) before child)
      | sliceValue environment mutability view lo hi origin viewChild loChild hiChild =>
          refine .sliceValue (ih (.view environment view) (path ++ [0]) before viewChild) ?_ ?_
          · intro value middle result
            exact ih (.bound environment value.count 0 lo) (path ++ [1]) middle (loChild value.count)
          · intro value middle low ready result bounded
            exact ih (.bound environment value.count value.count hi) (path ++ [2]) ready (hiChild value.count)
      | printArgumentText environment text =>
          simpa [execute, evalPrintArg, pure] using (SourceHistory.printArgumentText fuel path environment text before)
      | printArgumentExpression environment expression childSupported =>
          exact .printArgumentExpression (ih (.value environment expression) (path ++ [0]) before childSupported)
      | printArgumentView environment view childSupported =>
          exact .printArgumentView (ih (.view environment view) (path ++ [0]) before childSupported)
      | printArguments environment arguments origin childrenSupported =>
          refine .printArguments fuel path environment arguments origin before ?_
          intro outcome visits replay visit member
          have inMapped : visit.operand ∈ visits.map Invocation.operand := List.mem_map_of_mem member
          rw [replay.sourceOrder] at inMapped
          have inArguments : visit.operand ∈ arguments := List.mem_of_mem_take inMapped
          have child := ih (.printArgument environment visit.operand) (path ++ [visit.ordinal]) visit.before
            (childrenSupported visit.operand inArguments)
          simp only [execute] at child
          rw [← visit_executes replay visit member]
          exact child
      | printText environment text origin => exact .printText fuel path environment text origin before
      | builderBytes environment destination ty bytes origin => exact .builderBytes fuel path environment destination ty bytes origin before
      | builderArray environment incoming ty operands origin elementsSupported =>
          refine .builderArray fuel path environment incoming ty operands origin before ?_
          intro current prepared ready pending element outcome visits renewed found elementFound replay visit member
          have inMapped : visit.operand ∈ visits.map Invocation.operand := List.mem_map_of_mem member
          rw [replay.sourceOrder] at inMapped
          have inOperands : visit.operand ∈ operands := List.mem_of_mem_take inMapped
          have child := ih (.element environment current element visit.operand) (path ++ [visit.ordinal]) visit.before
            (elementsSupported visit.operand inOperands current element)
          simp only [execute] at child
          rw [← visit_executes replay visit member]
          exact child
      | fixedElement environment parent element operand fixed childSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          simp only [execute] at child ⊢
          rw [fixedElement_execution fuel config environment parent element operand before fixed]
          exact .fixedElement fixed child
      | nonfixedElement environment parent element operand nonfixed childSupported =>
          refine .nonfixedElement nonfixed ?_
          intro layout layoutReady destination ready layoutResult opened
          exact ih (.builder environment destination operand) (path ++ [0]) ready (childSupported destination)
      | argumentsDone environment vars => simpa [execute, evalArguments, pure] using
          (SourceHistory.argumentsDone fuel path environment vars before :
            SourceHistory config (fuel + 1) path (.arguments environment vars [] []) before _)
      | argumentValue environment vars parameter parameters operand arguments childSupported tailSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          have tail : ∀ value middle, evalValue fuel config environment operand before = .ok value middle →
              SourceHistory config fuel (path ++ [1]) (.arguments environment vars parameters arguments) middle
                (evalArguments fuel config environment vars parameters arguments middle) := by
            intro value middle _
            exact ih (.arguments environment vars parameters arguments) (path ++ [1]) middle tailSupported
          simp only [execute]
          rw [valueArgument_source]
          exact .argumentValue child tail
      | argumentConstruct environment vars parameter parameters operand arguments materializedSupported directSupported tailSupported =>
          refine .argumentConstruct ?_ ?_ ?_
          · intro localVar count found query
            exact ih (.value environment operand) (path ++ [0]) before materializedSupported
          · intro localVar destination ready found query allocated
            exact ih (.builder environment destination operand) (path ++ [0]) ready (directSupported destination)
          · intro value middle result
            exact ih (.arguments environment vars parameters arguments) (path ++ [1]) middle tailSupported
      | argumentReference environment vars parameter parameters mutability place arguments childSupported tailSupported =>
          refine .argumentReference (ih (.place environment place) (path ++ [0]) before childSupported) ?_
          intro location middle result
          exact ih (.arguments environment vars parameters arguments) (path ++ [1]) middle tailSupported
      | producer environment supported =>
          exact ProducerHistory.toSource (producerHistory_exists (fuel + 1) config environment path _ before supported)

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessExpression : Expr :=
  .ifE (.bool true) (.mk 1 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none)
    (.mk 2 [] none) 0
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem witness_nestedFill : ∃ after,
    evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial = .ok .unit after ∧
    SourceHistory witnessConfig 40 [] (.value witnessEnvironment witnessExpression) .initial (.ok .unit after) := by
  have supported : SupportedOperation witnessConfig (.value witnessEnvironment witnessExpression) := by
    unfold witnessExpression
    apply SupportedOperation.conditional
    · exact .value _ (.boolean true)
    · apply SupportedOperation.block
      intro environment
      exact .sequence environment (.expression environment 0 (.value environment
        (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment)
    · exact .block _ _ _ (fun environment => .empty environment)
  have history := history_exists 40 witnessConfig (.value witnessEnvironment witnessExpression) [] .initial supported
  refine ⟨witnessState (evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial), ?_, ?_⟩
  · unfold witnessConfig witnessEnvironment witnessExpression witnessState
    cbv
  · have actual : evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial =
        .ok .unit (witnessState (evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial)) := by
      unfold witnessConfig witnessEnvironment witnessExpression witnessState
      cbv
    change SourceHistory witnessConfig 40 [] (.value witnessEnvironment witnessExpression) .initial
      (evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial) at history
    rw [actual] at history
    exact history

theorem witness_activationBody : ∃ after,
    execActivationBody 40 witnessConfig witnessEnvironment [] (.mk 0 [.expr witnessExpression 0] none) .initial =
      .ok [] after ∧
    SourceHistory witnessConfig 40 [] (.activationBody witnessEnvironment (.mk 0 [.expr witnessExpression 0] none))
      .initial (.ok [] after) := by
  have bodySupported : ∀ environment, SupportedOperation witnessConfig (.statements environment [.expr witnessExpression 0]) := by
    intro environment
    apply SupportedOperation.sequence
    · apply SupportedOperation.expression
      unfold witnessExpression
      apply SupportedOperation.conditional
      · exact .value _ (.boolean true)
      · apply SupportedOperation.block
        intro inner
        exact .sequence inner (.expression inner 0 (.value inner
          (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty inner)
      · exact .block _ _ _ (fun inner => .empty inner)
    · exact .empty environment
  have history := history_exists 40 witnessConfig
    (.activationBody witnessEnvironment (.mk 0 [.expr witnessExpression 0] none)) [] .initial
    (.activationBody witnessEnvironment 0 [.expr witnessExpression 0] bodySupported)
  refine ⟨witnessState (execActivationBody 40 witnessConfig witnessEnvironment []
    (.mk 0 [.expr witnessExpression 0] none) .initial), ?_, ?_⟩
  · unfold witnessConfig witnessEnvironment witnessExpression witnessState
    cbv
  · have actual : execActivationBody 40 witnessConfig witnessEnvironment []
        (.mk 0 [.expr witnessExpression 0] none) .initial =
        .ok [] (witnessState (execActivationBody 40 witnessConfig witnessEnvironment []
          (.mk 0 [.expr witnessExpression 0] none) .initial)) := by
      unfold witnessConfig witnessEnvironment witnessExpression witnessState
      cbv
    change SourceHistory witnessConfig 40 [] (.activationBody witnessEnvironment (.mk 0 [.expr witnessExpression 0] none))
      .initial (execActivationBody 40 witnessConfig witnessEnvironment [] (.mk 0 [.expr witnessExpression 0] none) .initial) at history
    rw [actual] at history
    exact history

private def activationWitnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"callee", #[], #[], #[],
    .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none, .unknown⟩], #[], 0, #[], #[], #[]⟩⟩
private def activationWitnessBlock : Block :=
  .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none

theorem witness_activationEntry : ∃ after,
    enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial = .ok [] after ∧
    SourceHistory activationWitnessConfig 40 [] (.activation witnessEnvironment activationWitnessBlock 0)
      .initial (.ok [] after) := by
  have bodySupported : ∀ environment, SupportedOperation activationWitnessConfig
      (.statements environment [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0]) := by
    intro environment
    exact .sequence environment (.expression environment 0 (.value environment
      (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment)
  have supported : SupportedOperation activationWitnessConfig (.activation witnessEnvironment activationWitnessBlock 0) := by
    unfold activationWitnessBlock
    exact .activation witnessEnvironment 0 _ 0 bodySupported
  have history := history_exists 40 activationWitnessConfig (.activation witnessEnvironment activationWitnessBlock 0)
    [] .initial supported
  refine ⟨witnessState (enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial), ?_, ?_⟩
  · unfold activationWitnessConfig witnessEnvironment activationWitnessBlock witnessState
    cbv
  · have actual : enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial =
        .ok [] (witnessState (enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial)) := by
      unfold activationWitnessConfig witnessEnvironment activationWitnessBlock witnessState
      cbv
    change SourceHistory activationWitnessConfig 40 [] (.activation witnessEnvironment activationWitnessBlock 0)
      .initial (enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial) at history
    rw [actual] at history
    exact history

private def callWitnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"callee", #[], #[], #[],
    .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none, .unknown⟩],
    #[⟨0, "callee", [], [], []⟩], 0, #[], #[], #[]⟩⟩
private def callWitnessContext : Context := ⟨0, "callee", [], [], []⟩
private def callWitnessImplementation : Impl := ⟨"callee", #[], #[], #[],
  .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none, .unknown⟩

private theorem callWitness_supported : SupportedOperation callWitnessConfig (.call witnessEnvironment 0 0) := by
  have bodySupported : ∀ environment, SupportedOperation callWitnessConfig
      (.statements environment [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0]) := by
    intro environment
    exact .sequence environment (.expression environment 0 (.value environment
      (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment)
  apply SupportedOperation.call witnessEnvironment 0 0 callWitnessContext callWitnessImplementation
  · rfl
  · rfl
  · rfl
  · rfl
  · intro act
    exact .activation _ 0 _ 0 bodySupported

theorem witness_call : ∃ after,
    invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial = .ok [] after ∧
    SourceHistory callWitnessConfig 40 [] (.call witnessEnvironment 0 0) .initial (.ok [] after) := by
  have supported := callWitness_supported
  have history := history_exists 40 callWitnessConfig (.call witnessEnvironment 0 0) [] .initial supported
  refine ⟨witnessState (invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial), ?_, ?_⟩
  · unfold callWitnessConfig witnessEnvironment witnessState
    cbv
  · have actual : invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial =
        .ok [] (witnessState (invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial)) := by
      unfold callWitnessConfig witnessEnvironment witnessState
      cbv
    change SourceHistory callWitnessConfig 40 [] (.call witnessEnvironment 0 0) .initial
      (invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial) at history
    rw [actual] at history
    exact history

theorem witness_valueCall : ∃ after,
    evalValue 40 callWitnessConfig witnessEnvironment (.call 0 [] 0) .initial = .ok .unit after ∧
    SourceHistory callWitnessConfig 40 [] (.value witnessEnvironment (.call 0 [] 0)) .initial (.ok .unit after) := by
  have callee := callWitness_supported
  have supported : SupportedOperation callWitnessConfig (.value witnessEnvironment (.call 0 [] 0)) :=
    .valueCall witnessEnvironment 0 0 callWitnessContext callWitnessImplementation rfl rfl rfl callee
  have history := history_exists 40 callWitnessConfig (.value witnessEnvironment (.call 0 [] 0)) [] .initial supported
  refine ⟨witnessState (evalValue 40 callWitnessConfig witnessEnvironment (.call 0 [] 0) .initial), ?_, ?_⟩
  · unfold callWitnessConfig witnessEnvironment witnessState
    cbv
  · have actual : evalValue 40 callWitnessConfig witnessEnvironment (.call 0 [] 0) .initial =
        .ok .unit (witnessState (evalValue 40 callWitnessConfig witnessEnvironment (.call 0 [] 0) .initial)) := by
      unfold callWitnessConfig witnessEnvironment witnessState
      cbv
    change SourceHistory callWitnessConfig 40 [] (.value witnessEnvironment (.call 0 [] 0)) .initial
      (evalValue 40 callWitnessConfig witnessEnvironment (.call 0 [] 0) .initial) at history
    rw [actual] at history
    exact history

private def argumentWitnessParameters : List Param := [⟨0, .byValue⟩, ⟨1, .byValue⟩]
private def argumentWitnessArguments : List Arg := [.byVal (.call 0 [] 0), .byVal (.lit .i64 9)]

theorem witness_nestedCallArgument : ∃ after,
    evalArguments 40 callWitnessConfig witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments .initial =
      .ok [.unit, .int .i64 9] after ∧
    SourceHistory callWitnessConfig 40 []
      (.arguments witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments) .initial
      (.ok [.unit, .int .i64 9] after) := by
  have callee := callWitness_supported
  have supported : SupportedOperation callWitnessConfig
      (.arguments witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments) := by
    unfold argumentWitnessParameters argumentWitnessArguments
    exact .argumentValue _ _ _ _ _ _
      (.valueCall witnessEnvironment 0 0 callWitnessContext callWitnessImplementation rfl rfl rfl callee)
      (.argumentValue _ _ _ _ _ _ (.value _ (.integer .i64 9)) (.argumentsDone _ _))
  have history := history_exists 40 callWitnessConfig
    (.arguments witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments) [] .initial supported
  refine ⟨witnessState (evalArguments 40 callWitnessConfig witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments .initial), ?_, ?_⟩
  · unfold callWitnessConfig witnessEnvironment argumentWitnessParameters argumentWitnessArguments witnessState
    cbv
  · have actual : evalArguments 40 callWitnessConfig witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments .initial =
        .ok [.unit, .int .i64 9] (witnessState (evalArguments 40 callWitnessConfig witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments .initial)) := by
      unfold callWitnessConfig witnessEnvironment argumentWitnessParameters argumentWitnessArguments witnessState
      cbv
    change SourceHistory callWitnessConfig 40 []
      (.arguments witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments) .initial
      (evalArguments 40 callWitnessConfig witnessEnvironment #[] argumentWitnessParameters argumentWitnessArguments .initial) at history
    rw [actual] at history
    exact history

theorem witness_producerCall : ∃ after,
    evalProduce 40 callWitnessConfig witnessEnvironment [] (.call 0 [] 0) .initial = .ok [] after ∧
    SourceHistory callWitnessConfig 40 [] (.producer witnessEnvironment (.call 0 [] 0)) .initial (.ok [] after) := by
  have callee := callWitness_supported
  have history := history_exists 40 callWitnessConfig (.producer witnessEnvironment (.call 0 [] 0)) [] .initial
    (.producerCall witnessEnvironment 0 0 callee)
  refine ⟨witnessState (evalProduce 40 callWitnessConfig witnessEnvironment [] (.call 0 [] 0) .initial), ?_, ?_⟩
  · unfold callWitnessConfig witnessEnvironment witnessState
    cbv
  · have actual : evalProduce 40 callWitnessConfig witnessEnvironment [] (.call 0 [] 0) .initial =
        .ok [] (witnessState (evalProduce 40 callWitnessConfig witnessEnvironment [] (.call 0 [] 0) .initial)) := by
      unfold callWitnessConfig witnessEnvironment witnessState
      cbv
    change SourceHistory callWitnessConfig 40 [] (.producer witnessEnvironment (.call 0 [] 0)) .initial
      (evalProduce 40 callWitnessConfig witnessEnvironment [] (.call 0 [] 0) .initial) at history
    rw [actual] at history
    exact history

private def sideEffectContext : Context := ⟨0, "source", [], [], []⟩
private def sideEffectImplementation : Impl := ⟨"source", #[], #[], #[], .mk 0 [.print [.text "x"] 0] none, .unknown⟩
private def sideEffectConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[sideEffectImplementation], #[sideEffectContext], 0, #[], #[], #[]⟩⟩
private def sideEffectFill : Expr := .fill (.arr .unit 3) (.call 0 [] 0) 0

private theorem sideEffectCallee_supported (environment : RuntimeActivation) :
    SupportedOperation sideEffectConfig (.call environment 0 0) := by
  have bodySupported : ∀ scopedEnvironment, SupportedOperation sideEffectConfig
      (.statements scopedEnvironment [.print [.text "x"] 0]) := by
    intro scopedEnvironment
    exact .sequence scopedEnvironment (.printText scopedEnvironment "x" 0) (.empty scopedEnvironment)
  apply SupportedOperation.call environment 0 0 sideEffectContext sideEffectImplementation
  · rfl
  · rfl
  · rfl
  · rfl
  · intro act
    exact .activation _ 0 _ 0 bodySupported

theorem witness_fillSourceOnce : ∃ after,
    evalValue 40 sideEffectConfig witnessEnvironment sideEffectFill .initial = .ok (.fixed #[.unit, .unit, .unit]) after ∧
    after.construction.stdout.data.toList = [120, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment sideEffectFill) .initial
      (.ok (.fixed #[.unit, .unit, .unit]) after) := by
  have callee := sideEffectCallee_supported witnessEnvironment
  have valueCall : SupportedOperation sideEffectConfig (.value witnessEnvironment (.call 0 [] 0)) :=
    .valueCall witnessEnvironment 0 0 sideEffectContext sideEffectImplementation rfl rfl rfl callee
  have supported : SupportedOperation sideEffectConfig (.value witnessEnvironment sideEffectFill) :=
    .fill witnessEnvironment .unit 3 0 (.call 0 [] 0) rfl valueCall
  have history := history_exists 40 sideEffectConfig (.value witnessEnvironment sideEffectFill) [] .initial supported
  refine ⟨witnessState (evalValue 40 sideEffectConfig witnessEnvironment sideEffectFill .initial), ?_, ?_, ?_⟩
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation sideEffectFill witnessEnvironment
    cbv
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation sideEffectFill witnessEnvironment
    cbv
  · have actual : evalValue 40 sideEffectConfig witnessEnvironment sideEffectFill .initial =
        .ok (.fixed #[.unit, .unit, .unit]) (witnessState (evalValue 40 sideEffectConfig witnessEnvironment sideEffectFill .initial)) := by
      unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation sideEffectFill witnessEnvironment
      cbv
    change SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment sideEffectFill) .initial
      (evalValue 40 sideEffectConfig witnessEnvironment sideEffectFill .initial) at history
    rw [actual] at history
    exact history

private def elementWitnessBefore : ExecutionState :=
  witnessState (newDestination sideEffectConfig.layout 0 (.varr (.int .i64)) .value 0 none (some 1) .initial)

theorem witness_elementSourceCall : ∃ after,
    newDestination sideEffectConfig.layout 0 (.varr (.int .i64)) .value 0 none (some 1) .initial =
      .ok 0 elementWitnessBefore ∧
    buildElement 40 sideEffectConfig witnessEnvironment 0 (.int .i64) (.call 0 [] 0) elementWitnessBefore =
      .stop (.fault .shape) after ∧ after.construction.stdout.data.toList = [120, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.element witnessEnvironment 0 (.int .i64) (.call 0 [] 0))
      elementWitnessBefore (.stop (.fault .shape) after) := by
  have callee := sideEffectCallee_supported witnessEnvironment
  have operand : SupportedOperation sideEffectConfig (.value witnessEnvironment (.call 0 [] 0)) :=
    .valueCall witnessEnvironment 0 0 sideEffectContext sideEffectImplementation rfl rfl rfl callee
  have history := history_exists 40 sideEffectConfig (.element witnessEnvironment 0 (.int .i64) (.call 0 [] 0))
    [] elementWitnessBefore (.fixedElement witnessEnvironment 0 (.int .i64) (.call 0 [] 0) rfl operand)
  refine ⟨witnessState (buildElement 40 sideEffectConfig witnessEnvironment 0 (.int .i64) (.call 0 [] 0) elementWitnessBefore), ?_, ?_, ?_, ?_⟩
  · unfold elementWitnessBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation
    cbv
  · unfold elementWitnessBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold elementWitnessBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · have actual : buildElement 40 sideEffectConfig witnessEnvironment 0 (.int .i64) (.call 0 [] 0) elementWitnessBefore =
        .stop (.fault .shape) (witnessState (buildElement 40 sideEffectConfig witnessEnvironment 0 (.int .i64) (.call 0 [] 0) elementWitnessBefore)) := by
      unfold elementWitnessBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
      cbv
    change SourceHistory sideEffectConfig 40 [] (.element witnessEnvironment 0 (.int .i64) (.call 0 [] 0))
      elementWitnessBefore (buildElement 40 sideEffectConfig witnessEnvironment 0 (.int .i64) (.call 0 [] 0) elementWitnessBefore) at history
    rw [actual] at history
    exact history

private def nestedElementBefore : ExecutionState := witnessState
  (newDestination sideEffectConfig.layout 0 (.varr (.varr (.int .u8))) .value 0 none (some 1) .initial)

theorem witness_nonfixedElement : ∃ after,
    newDestination sideEffectConfig.layout 0 (.varr (.varr (.int .u8))) .value 0 none (some 1) .initial =
      .ok 0 nestedElementBefore ∧
    buildElement 40 sideEffectConfig witnessEnvironment 0 (.varr (.int .u8))
      (.bytes (.varr (.int .u8)) [65, 66] 0) nestedElementBefore = .ok () after ∧
    after.construction.events = [.begin 0, .begin 1, .write 1 0, .write 1 1, .write 0 0] ∧
    SourceHistory sideEffectConfig 40 [] (.element witnessEnvironment 0 (.varr (.int .u8))
      (.bytes (.varr (.int .u8)) [65, 66] 0)) nestedElementBefore (.ok () after) := by
  have supported : SupportedOperation sideEffectConfig (.element witnessEnvironment 0 (.varr (.int .u8))
      (.bytes (.varr (.int .u8)) [65, 66] 0)) :=
    .nonfixedElement witnessEnvironment 0 (.varr (.int .u8)) (.bytes (.varr (.int .u8)) [65, 66] 0) rfl
      (fun destination => .builderBytes witnessEnvironment destination (.varr (.int .u8)) [65, 66] 0)
  have history := history_exists 40 sideEffectConfig _ [] nestedElementBefore supported
  refine ⟨witnessState (buildElement 40 sideEffectConfig witnessEnvironment 0 (.varr (.int .u8))
    (.bytes (.varr (.int .u8)) [65, 66] 0) nestedElementBefore), ?_, ?_, ?_, ?_⟩
  · unfold nestedElementBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation
    cbv
  · unfold nestedElementBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold nestedElementBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · have actual : buildElement 40 sideEffectConfig witnessEnvironment 0 (.varr (.int .u8))
        (.bytes (.varr (.int .u8)) [65, 66] 0) nestedElementBefore =
        .ok () (witnessState (buildElement 40 sideEffectConfig witnessEnvironment 0 (.varr (.int .u8))
          (.bytes (.varr (.int .u8)) [65, 66] 0) nestedElementBefore)) := by
      unfold nestedElementBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
      cbv
    change SourceHistory sideEffectConfig 40 [] (.element witnessEnvironment 0 (.varr (.int .u8))
      (.bytes (.varr (.int .u8)) [65, 66] 0)) nestedElementBefore
      (buildElement 40 sideEffectConfig witnessEnvironment 0 (.varr (.int .u8))
        (.bytes (.varr (.int .u8)) [65, 66] 0) nestedElementBefore) at history
    rw [actual] at history
    exact history

theorem byteElement_supported (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Goose.Core.DestinationId) (element ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    SupportedOperation config (.element environment parent element (.bytes ty bytes origin)) := by
  cases fixed : element.nonfixed with
  | false => exact .fixedElement environment parent element _ fixed (.valueBytes environment ty bytes origin)
  | true =>
    exact .nonfixedElement environment parent element _ fixed
      (fun destination => .builderBytes environment destination ty bytes origin)

#print axioms byteElement_supported

private def nestedArrayOperand : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def nestedArraySource : Expr := .arrLit (.varr (.varr (.int .u8))) [nestedArrayOperand, nestedArrayOperand] 0
private def nestedArrayBefore : ExecutionState := witnessState
  (newDestination sideEffectConfig.layout 0 (.varr (.varr (.int .u8))) .value 0 none (some 2) .initial)

private theorem nestedArray_supported : SupportedOperation sideEffectConfig
    (.builder witnessEnvironment 0 nestedArraySource) := by
  unfold nestedArraySource
  apply SupportedOperation.builderArray
  intro operand member current element
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals exact byteElement_supported sideEffectConfig witnessEnvironment current element (.varr (.int .u8)) [65, 66] 0

theorem witness_nestedArray : ∃ after,
    newDestination sideEffectConfig.layout 0 (.varr (.varr (.int .u8))) .value 0 none (some 2) .initial =
      .ok 0 nestedArrayBefore ∧
    buildExpr 40 sideEffectConfig witnessEnvironment 0 nestedArraySource nestedArrayBefore = .ok () after ∧
    after.construction.events = [.begin 0, .begin 1, .write 1 0, .write 1 1, .write 0 0,
      .begin 2, .write 2 0, .write 2 1, .write 0 1] ∧
    SourceHistory sideEffectConfig 40 [] (.builder witnessEnvironment 0 nestedArraySource) nestedArrayBefore (.ok () after) := by
  have history := history_exists 40 sideEffectConfig (.builder witnessEnvironment 0 nestedArraySource) []
    nestedArrayBefore nestedArray_supported
  refine ⟨witnessState (buildExpr 40 sideEffectConfig witnessEnvironment 0 nestedArraySource nestedArrayBefore), ?_, ?_, ?_, ?_⟩
  · unfold nestedArrayBefore witnessState sideEffectConfig sideEffectContext sideEffectImplementation
    cbv
  · unfold nestedArrayBefore nestedArraySource nestedArrayOperand witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold nestedArrayBefore nestedArraySource nestedArrayOperand witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · have actual : buildExpr 40 sideEffectConfig witnessEnvironment 0 nestedArraySource nestedArrayBefore =
        .ok () (witnessState (buildExpr 40 sideEffectConfig witnessEnvironment 0 nestedArraySource nestedArrayBefore)) := by
      unfold nestedArrayBefore nestedArraySource nestedArrayOperand witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
      cbv
    change SourceHistory sideEffectConfig 40 [] (.builder witnessEnvironment 0 nestedArraySource) nestedArrayBefore
      (buildExpr 40 sideEffectConfig witnessEnvironment 0 nestedArraySource nestedArrayBefore) at history
    rw [actual] at history
    exact history

#print axioms witness_nestedArray

#print axioms witness_nonfixedElement

#print axioms witness_elementSourceCall

private def comparisonWitness : Expr := .cmp .eq (.call 0 [] 0) (.call 0 [] 0)
private def shortCircuitWitness : Expr := .and (.bool false) (.call 0 [] 0)

private theorem sideEffectValue_supported : SupportedOperation sideEffectConfig (.value witnessEnvironment (.call 0 [] 0)) :=
  .valueCall witnessEnvironment 0 0 sideEffectContext sideEffectImplementation rfl rfl rfl
    (sideEffectCallee_supported witnessEnvironment)

theorem witness_comparisonCalls : ∃ after,
    evalValue 40 sideEffectConfig witnessEnvironment comparisonWitness .initial = .stop (.fault .shape) after ∧
    after.construction.stdout.data.toList = [120, 10, 120, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment comparisonWitness) .initial (.stop (.fault .shape) after) := by
  have supported : SupportedOperation sideEffectConfig (.value witnessEnvironment comparisonWitness) :=
    .comparison witnessEnvironment .eq _ _ sideEffectValue_supported sideEffectValue_supported
  have history := history_exists 40 sideEffectConfig (.value witnessEnvironment comparisonWitness) [] .initial supported
  refine ⟨witnessState (evalValue 40 sideEffectConfig witnessEnvironment comparisonWitness .initial), ?_, ?_, ?_⟩
  · unfold witnessState comparisonWitness sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold witnessState comparisonWitness sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · have actual : evalValue 40 sideEffectConfig witnessEnvironment comparisonWitness .initial =
        .stop (.fault .shape) (witnessState (evalValue 40 sideEffectConfig witnessEnvironment comparisonWitness .initial)) := by
      unfold witnessState comparisonWitness sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
      cbv
    change SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment comparisonWitness) .initial
      (evalValue 40 sideEffectConfig witnessEnvironment comparisonWitness .initial) at history
    rw [actual] at history
    exact history

theorem witness_shortCircuitSkipsCall :
    evalValue 40 sideEffectConfig witnessEnvironment shortCircuitWitness .initial = .ok (.bool false) .initial ∧
    SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment shortCircuitWitness) .initial (.ok (.bool false) .initial) := by
  have supported : SupportedOperation sideEffectConfig (.value witnessEnvironment shortCircuitWitness) :=
    .logical witnessEnvironment true (.bool false) (.call 0 [] 0) (.value witnessEnvironment (.boolean false)) sideEffectValue_supported
  have history := history_exists 40 sideEffectConfig (.value witnessEnvironment shortCircuitWitness) [] .initial supported
  have actual : evalValue 40 sideEffectConfig witnessEnvironment shortCircuitWitness .initial = .ok (.bool false) .initial := by
    unfold sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment shortCircuitWitness
    cbv
  refine ⟨actual, ?_⟩
  change SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment shortCircuitWitness) .initial
    (evalValue 40 sideEffectConfig witnessEnvironment shortCircuitWitness .initial) at history
  rw [actual] at history
  exact history

theorem witness_negationCall : ∃ after,
    evalValue 40 sideEffectConfig witnessEnvironment (.not (.call 0 [] 0)) .initial = .stop (.fault .shape) after ∧
    after.construction.stdout.data.toList = [120, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment (.not (.call 0 [] 0))) .initial
      (.stop (.fault .shape) after) := by
  have supported : SupportedOperation sideEffectConfig (.value witnessEnvironment (.not (.call 0 [] 0))) :=
    .negation witnessEnvironment (.call 0 [] 0) sideEffectValue_supported
  have history := history_exists 40 sideEffectConfig (.value witnessEnvironment (.not (.call 0 [] 0))) [] .initial supported
  refine ⟨witnessState (evalValue 40 sideEffectConfig witnessEnvironment (.not (.call 0 [] 0)) .initial), ?_, ?_, ?_⟩
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · have actual : evalValue 40 sideEffectConfig witnessEnvironment (.not (.call 0 [] 0)) .initial =
        .stop (.fault .shape) (witnessState (evalValue 40 sideEffectConfig witnessEnvironment (.not (.call 0 [] 0)) .initial)) := by
      unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
      cbv
    change SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment (.not (.call 0 [] 0))) .initial
      (evalValue 40 sideEffectConfig witnessEnvironment (.not (.call 0 [] 0)) .initial) at history
    rw [actual] at history
    exact history

#print axioms witness_negationCall

#print axioms witness_comparisonCalls
#print axioms witness_shortCircuitSkipsCall

private def printWitnessArguments : List PrintArg := [.text "a", .expr (.call 0 [] 0), .text "b"]

theorem witness_printArgumentCall : ∃ after,
    execStmt 40 sideEffectConfig witnessEnvironment (.print printWitnessArguments 0) .initial = .ok (.normal .unit) after ∧
    after.construction.stdout.data.toList = [120, 10, 97, 40, 41, 98, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.statement witnessEnvironment (.print printWitnessArguments 0)) .initial
      (.ok (.normal .unit) after) := by
  have supported : SupportedOperation sideEffectConfig (.statement witnessEnvironment (.print printWitnessArguments 0)) := by
    apply SupportedOperation.printArguments
    intro argument member
    simp only [printWitnessArguments, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .printArgumentText witnessEnvironment "a"
    · exact .printArgumentExpression witnessEnvironment (.call 0 [] 0) sideEffectValue_supported
    · exact .printArgumentText witnessEnvironment "b"
  have history := history_exists 40 sideEffectConfig (.statement witnessEnvironment (.print printWitnessArguments 0)) [] .initial supported
  refine ⟨witnessState (execStmt 40 sideEffectConfig witnessEnvironment (.print printWitnessArguments 0) .initial), ?_, ?_, ?_⟩
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment printWitnessArguments
    cbv
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment printWitnessArguments
    cbv
  · have actual : execStmt 40 sideEffectConfig witnessEnvironment (.print printWitnessArguments 0) .initial =
        .ok (.normal .unit) (witnessState (execStmt 40 sideEffectConfig witnessEnvironment (.print printWitnessArguments 0) .initial)) := by
      unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment printWitnessArguments
      cbv
    change SourceHistory sideEffectConfig 40 [] (.statement witnessEnvironment (.print printWitnessArguments 0)) .initial
      (execStmt 40 sideEffectConfig witnessEnvironment (.print printWitnessArguments 0) .initial) at history
    rw [actual] at history
    exact history

theorem witness_printViewCall : ∃ after,
    execStmt 40 sideEffectConfig witnessEnvironment (.print [.view (.val (.call 0 [] 0))] 0) .initial =
      .stop (.fault .shape) after ∧ after.construction.stdout.data.toList = [120, 10] ∧
    SourceHistory sideEffectConfig 40 []
      (.statement witnessEnvironment (.print [.view (.val (.call 0 [] 0))] 0)) .initial (.stop (.fault .shape) after) := by
  have supported : SupportedOperation sideEffectConfig
      (.statement witnessEnvironment (.print [.view (.val (.call 0 [] 0))] 0)) := by
    apply SupportedOperation.printArguments
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst argument
    exact .printArgumentView witnessEnvironment _ (.valueView witnessEnvironment _ sideEffectValue_supported)
  have history := history_exists 40 sideEffectConfig _ [] .initial supported
  refine ⟨witnessState (execStmt 40 sideEffectConfig witnessEnvironment (.print [.view (.val (.call 0 [] 0))] 0) .initial), ?_, ?_, ?_⟩
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · have actual : execStmt 40 sideEffectConfig witnessEnvironment (.print [.view (.val (.call 0 [] 0))] 0) .initial =
        .stop (.fault .shape) (witnessState (execStmt 40 sideEffectConfig witnessEnvironment (.print [.view (.val (.call 0 [] 0))] 0) .initial)) := by
      unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
      cbv
    change SourceHistory sideEffectConfig 40 []
      (.statement witnessEnvironment (.print [.view (.val (.call 0 [] 0))] 0)) .initial
      (execStmt 40 sideEffectConfig witnessEnvironment (.print [.view (.val (.call 0 [] 0))] 0) .initial) at history
    rw [actual] at history
    exact history

#print axioms witness_printViewCall

#print axioms witness_printArgumentCall

private def boundCallWitness : Expr := .slice .readOnly
  (.val (.fill (.arr (.int .i64) 2) (.lit .i64 7) 0)) (.expr (.call 0 [] 0)) .omitted 0

theorem witness_sliceBoundCall : ∃ after,
    evalValue 40 sideEffectConfig witnessEnvironment boundCallWitness .initial = .stop (.fault .shape) after ∧
    after.construction.stdout.data.toList = [120, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment boundCallWitness) .initial (.stop (.fault .shape) after) := by
  have supported : SupportedOperation sideEffectConfig (.value witnessEnvironment boundCallWitness) := by
    unfold boundCallWitness
    apply SupportedOperation.sliceValue
    · exact .valueView witnessEnvironment _ (.value witnessEnvironment (.fill (.int .i64) 2 0 rfl (.integer .i64 7)))
    · intro count
      exact .expressionBound witnessEnvironment count 0 (.call 0 [] 0) false sideEffectValue_supported
    · intro count
      exact .omittedBound witnessEnvironment count count
  have history := history_exists 40 sideEffectConfig (.value witnessEnvironment boundCallWitness) [] .initial supported
  refine ⟨witnessState (evalValue 40 sideEffectConfig witnessEnvironment boundCallWitness .initial), ?_, ?_, ?_⟩
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment boundCallWitness
    cbv
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment boundCallWitness
    cbv
  · have actual : evalValue 40 sideEffectConfig witnessEnvironment boundCallWitness .initial =
        .stop (.fault .shape) (witnessState (evalValue 40 sideEffectConfig witnessEnvironment boundCallWitness .initial)) := by
      unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment boundCallWitness
      cbv
    change SourceHistory sideEffectConfig 40 [] (.value witnessEnvironment boundCallWitness) .initial
      (evalValue 40 sideEffectConfig witnessEnvironment boundCallWitness .initial) at history
    rw [actual] at history
    exact history

#print axioms witness_sliceBoundCall

private def conditionalStatementWitness : Stmt := .ifS (.bool true)
  (.mk 0 [.expr (.fill (.arr .unit 3) (.call 0 [] 0) 0) 0] none) none 0

theorem witness_conditionalStatement : ∃ after,
    execStmt 40 sideEffectConfig witnessEnvironment conditionalStatementWitness .initial = .ok (.normal .unit) after ∧
    after.construction.stdout.data.toList = [120, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.statement witnessEnvironment conditionalStatementWitness) .initial
      (.ok (.normal .unit) after) := by
  have supported : SupportedOperation sideEffectConfig (.statement witnessEnvironment conditionalStatementWitness) := by
    unfold conditionalStatementWitness
    apply SupportedOperation.ifStatement
    · exact .value _ (.boolean true)
    · apply SupportedOperation.block
      intro environment
      have source : SupportedOperation sideEffectConfig (.value environment (.call 0 [] 0)) :=
        .valueCall environment 0 0 sideEffectContext sideEffectImplementation rfl rfl rfl (sideEffectCallee_supported environment)
      exact .sequence environment (.expression environment 0 (.fill environment .unit 3 0 (.call 0 [] 0) rfl source))
        (.empty environment)
    · intro block impossible
      cases impossible
  have history := history_exists 40 sideEffectConfig (.statement witnessEnvironment conditionalStatementWitness) [] .initial supported
  refine ⟨witnessState (execStmt 40 sideEffectConfig witnessEnvironment conditionalStatementWitness .initial), ?_, ?_, ?_⟩
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment conditionalStatementWitness
    cbv
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment conditionalStatementWitness
    cbv
  · have actual : execStmt 40 sideEffectConfig witnessEnvironment conditionalStatementWitness .initial =
        .ok (.normal .unit) (witnessState (execStmt 40 sideEffectConfig witnessEnvironment conditionalStatementWitness .initial)) := by
      unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment conditionalStatementWitness
      cbv
    change SourceHistory sideEffectConfig 40 [] (.statement witnessEnvironment conditionalStatementWitness) .initial
      (execStmt 40 sideEffectConfig witnessEnvironment conditionalStatementWitness .initial) at history
    rw [actual] at history
    exact history

private def whileWitnessBody : Block := .mk 0 [.print [.text "x"] 0,
  .expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none
private def whileWitness : Stmt := .while (.bool true) whileWitnessBody 0

theorem witness_whileInitializerTimeout : ∃ after,
    execStmt 20 sideEffectConfig witnessEnvironment whileWitness .initial = .stop .timeout after ∧
    0 < after.construction.stdout.data.size ∧
    SourceHistory sideEffectConfig 20 [] (.statement witnessEnvironment whileWitness) .initial (.stop .timeout after) := by
  have body : SupportedOperation sideEffectConfig (.block witnessEnvironment whileWitnessBody) := by
    unfold whileWitnessBody
    apply SupportedOperation.block
    intro environment
    exact .sequence environment (.printText environment "x" 0)
      (.sequence environment (.expression environment 0 (.value environment
        (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment))
  have supported : SupportedOperation sideEffectConfig (.statement witnessEnvironment whileWitness) := by
    unfold whileWitness
    exact .whileStatement witnessEnvironment (.bool true) whileWitnessBody 0
      (.whileLoop witnessEnvironment (.bool true) whileWitnessBody (.value witnessEnvironment (.boolean true)) body)
  have history := history_exists 20 sideEffectConfig (.statement witnessEnvironment whileWitness) [] .initial supported
  refine ⟨witnessState (execStmt 20 sideEffectConfig witnessEnvironment whileWitness .initial), ?_, ?_, ?_⟩
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment whileWitness whileWitnessBody
    cbv
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment whileWitness whileWitnessBody
    cbv
  · have actual : execStmt 20 sideEffectConfig witnessEnvironment whileWitness .initial =
        .stop .timeout (witnessState (execStmt 20 sideEffectConfig witnessEnvironment whileWitness .initial)) := by
      unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment whileWitness whileWitnessBody
      cbv
    change SourceHistory sideEffectConfig 20 [] (.statement witnessEnvironment whileWitness) .initial
      (execStmt 20 sideEffectConfig witnessEnvironment whileWitness .initial) at history
    rw [actual] at history
    exact history

private def rangeWitness : Stmt := .forRange 0 (.lit .i64 0) (.lit .i64 2) whileWitnessBody 0

theorem witness_rangeInitializers : ∃ after,
    execStmt 40 sideEffectConfig witnessEnvironment rangeWitness .initial = .ok (.normal .unit) after ∧
    after.construction.stdout.data.toList = [120, 10, 120, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.statement witnessEnvironment rangeWitness) .initial (.ok (.normal .unit) after) := by
  have body : ∀ pre, SupportedOperation sideEffectConfig (.loopBodyWith witnessEnvironment pre whileWitnessBody) := by
    intro pre
    apply SupportedOperation.boundLoopBody
    unfold whileWitnessBody
    apply SupportedOperation.boundBlock
    intro environment
    exact .sequence environment (.printText environment "x" 0)
      (.sequence environment (.expression environment 0 (.value environment
        (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment))
  have supported : SupportedOperation sideEffectConfig (.statement witnessEnvironment rangeWitness) := by
    unfold rangeWitness
    exact .rangeStatement witnessEnvironment 0 (.lit .i64 0) (.lit .i64 2) whileWitnessBody 0
      (.value witnessEnvironment (.integer .i64 0)) (.value witnessEnvironment (.integer .i64 2)) body
  have history := history_exists 40 sideEffectConfig (.statement witnessEnvironment rangeWitness) [] .initial supported
  refine ⟨witnessState (execStmt 40 sideEffectConfig witnessEnvironment rangeWitness .initial), ?_, ?_, ?_⟩
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment rangeWitness whileWitnessBody
    cbv
  · unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment rangeWitness whileWitnessBody
    cbv
  · have actual : execStmt 40 sideEffectConfig witnessEnvironment rangeWitness .initial =
        .ok (.normal .unit) (witnessState (execStmt 40 sideEffectConfig witnessEnvironment rangeWitness .initial)) := by
      unfold witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment rangeWitness whileWitnessBody
      cbv
    change SourceHistory sideEffectConfig 40 [] (.statement witnessEnvironment rangeWitness) .initial
      (execStmt 40 sideEffectConfig witnessEnvironment rangeWitness .initial) at history
    rw [actual] at history
    exact history

private def eachWitnessSetup : EvalM Unit := do
  let destination ← newDestination sideEffectConfig.layout 0 (.grow (.int .u8)) .value 0 none (some 2)
  buildExpr 40 sideEffectConfig witnessEnvironment destination (.bytes (.grow (.int .u8)) [65, 66] 0)
  let destination ← completedReceivingDestination destination
  publishCarriers 0 [.completed destination]
  let stored ← storedDestination destination
  bindRoot (.global 0) (.stored stored)
private def eachWitnessBefore : ExecutionState := witnessState (eachWitnessSetup .initial)
private def eachWitness : Stmt := .forEach 0 none (.of (.global 0)) false whileWitnessBody 0

theorem witness_dynamicEachInitializers : ∃ after,
    eachWitnessSetup .initial = .ok () eachWitnessBefore ∧
    evalView 39 sideEffectConfig witnessEnvironment (.of (.global 0)) eachWitnessBefore =
      .ok ⟨⟨.global 0, []⟩, 0, 2, true⟩ eachWitnessBefore ∧
    execStmt 40 sideEffectConfig witnessEnvironment eachWitness eachWitnessBefore = .ok (.normal .unit) after ∧
    after.construction.stdout.data.toList = [120, 10, 120, 10] ∧
    SourceHistory sideEffectConfig 40 [] (.statement witnessEnvironment eachWitness) eachWitnessBefore (.ok (.normal .unit) after) := by
  have body : ∀ pre, SupportedOperation sideEffectConfig (.loopBodyWith witnessEnvironment pre whileWitnessBody) := by
    intro pre
    apply SupportedOperation.boundLoopBody
    unfold whileWitnessBody
    apply SupportedOperation.boundBlock
    intro environment
    exact .sequence environment (.printText environment "x" 0)
      (.sequence environment (.expression environment 0 (.value environment
        (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment))
  have supported : SupportedOperation sideEffectConfig (.statement witnessEnvironment eachWitness) := by
    unfold eachWitness
    exact .eachStatement witnessEnvironment 0 none (.of (.global 0)) false whileWitnessBody 0
      (.placeView witnessEnvironment _ (.globalPlace witnessEnvironment 0)) body
  have history := history_exists 40 sideEffectConfig (.statement witnessEnvironment eachWitness) [] eachWitnessBefore supported
  refine ⟨witnessState (execStmt 40 sideEffectConfig witnessEnvironment eachWitness eachWitnessBefore), ?_, ?_, ?_, ?_, ?_⟩
  · unfold eachWitnessBefore eachWitnessSetup witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold eachWitnessBefore eachWitnessSetup witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold eachWitnessBefore eachWitnessSetup eachWitness whileWitnessBody witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · unfold eachWitnessBefore eachWitnessSetup eachWitness whileWitnessBody witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
    cbv
  · have actual : execStmt 40 sideEffectConfig witnessEnvironment eachWitness eachWitnessBefore =
        .ok (.normal .unit) (witnessState (execStmt 40 sideEffectConfig witnessEnvironment eachWitness eachWitnessBefore)) := by
      unfold eachWitnessBefore eachWitnessSetup eachWitness whileWitnessBody witnessState sideEffectConfig sideEffectContext sideEffectImplementation witnessEnvironment
      cbv
    change SourceHistory sideEffectConfig 40 [] (.statement witnessEnvironment eachWitness) eachWitnessBefore
      (execStmt 40 sideEffectConfig witnessEnvironment eachWitness eachWitnessBefore) at history
    rw [actual] at history
    exact history

#print axioms witness_dynamicEachInitializers

#print axioms witness_rangeInitializers

#print axioms witness_whileInitializerTimeout

#print axioms witness_conditionalStatement

#print axioms witness_fillSourceOnce

#print axioms witness_producerCall

private def parameterSourceContext : Context := ⟨0, "source", [], [], []⟩
private def parameterTargetContext : Context := ⟨1, "target", [], [], []⟩
private def parameterSourceImplementation : Impl := ⟨"source", #[], #[], #[], .mk 0 [.print [.text "x"] 0] none, .unknown⟩
private def parameterTargetImplementation : Impl := ⟨"target", #[⟨0, .byValue⟩, ⟨1, .byValue⟩], #[], #[],
  .mk 1 [.print [.text "y"] 0] none, .unknown⟩
private def parameterConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[parameterSourceImplementation, parameterTargetImplementation],
    #[parameterSourceContext, parameterTargetContext], 0, #[], #[], #[]⟩⟩
private def parameterArguments : List Arg := [.byVal (.call 0 [] 0), .byVal (.lit .i64 9)]

private theorem parameterCall_supported (environment : RuntimeActivation) :
    SupportedOperation parameterConfig (.callWith environment 1 parameterArguments 0) := by
  have sourceBody : ∀ environment, SupportedOperation parameterConfig
      (.statements environment [.print [.text "x"] 0]) := by
    intro environment
    exact .sequence environment (.printText environment "x" 0) (.empty environment)
  have sourceCall : SupportedOperation parameterConfig (.call environment 0 0) := by
    apply SupportedOperation.call environment 0 0 parameterSourceContext parameterSourceImplementation
    · rfl
    · rfl
    · rfl
    · rfl
    · intro act
      exact .activation _ 0 _ 0 sourceBody
  have arguments : SupportedOperation parameterConfig
      (.arguments environment parameterTargetImplementation.vars parameterTargetImplementation.params.toList parameterArguments) := by
    unfold parameterTargetImplementation parameterArguments
    exact .argumentValue _ _ _ _ _ _
      (.valueCall environment 0 0 parameterSourceContext parameterSourceImplementation rfl rfl rfl sourceCall)
      (.argumentValue _ _ _ _ _ _ (.value _ (.integer .i64 9)) (.argumentsDone _ _))
  have targetBody : ∀ environment, SupportedOperation parameterConfig
      (.statements environment [.print [.text "y"] 0]) := by
    intro environment
    exact .sequence environment (.printText environment "y" 0) (.empty environment)
  have supported : SupportedOperation parameterConfig (.callWith environment 1 parameterArguments 0) := by
    apply SupportedOperation.callWith environment 1 parameterArguments 0 parameterTargetContext parameterTargetImplementation
    · rfl
    · rfl
    · rfl
    · exact arguments
    · intro act pre
      exact .boundActivation _ pre 1 _ 0 targetBody
  exact supported

theorem witness_parameterCall : ∃ after,
    invokeCall 40 parameterConfig witnessEnvironment 1 parameterArguments [] 0 .initial = .ok [] after ∧
    after.construction.stdout.data.toList = [120, 10, 121, 10] ∧ after.nextAct = 2 ∧
    SourceHistory parameterConfig 40 [] (.callWith witnessEnvironment 1 parameterArguments 0) .initial (.ok [] after) := by
  have supported := parameterCall_supported witnessEnvironment
  have history := history_exists 40 parameterConfig (.callWith witnessEnvironment 1 parameterArguments 0) [] .initial supported
  refine ⟨witnessState (invokeCall 40 parameterConfig witnessEnvironment 1 parameterArguments [] 0 .initial), ?_, ?_, ?_, ?_⟩
  · unfold witnessState parameterConfig parameterSourceContext parameterTargetContext parameterSourceImplementation parameterTargetImplementation parameterArguments witnessEnvironment
    cbv
  · unfold witnessState parameterConfig parameterSourceContext parameterTargetContext parameterSourceImplementation parameterTargetImplementation parameterArguments witnessEnvironment
    cbv
  · unfold witnessState parameterConfig parameterSourceContext parameterTargetContext parameterSourceImplementation parameterTargetImplementation parameterArguments witnessEnvironment
    cbv
  · have actual : invokeCall 40 parameterConfig witnessEnvironment 1 parameterArguments [] 0 .initial =
        .ok [] (witnessState (invokeCall 40 parameterConfig witnessEnvironment 1 parameterArguments [] 0 .initial)) := by
      unfold witnessState parameterConfig parameterSourceContext parameterTargetContext parameterSourceImplementation parameterTargetImplementation parameterArguments witnessEnvironment
      cbv
    change SourceHistory parameterConfig 40 [] (.callWith witnessEnvironment 1 parameterArguments 0) .initial
      (invokeCall 40 parameterConfig witnessEnvironment 1 parameterArguments [] 0 .initial) at history
    rw [actual] at history
    exact history

theorem witness_parameterValueCall : ∃ after,
    evalValue 40 parameterConfig witnessEnvironment (.call 1 parameterArguments 0) .initial = .ok .unit after ∧
    after.construction.stdout.data.toList = [120, 10, 121, 10] ∧ after.nextAct = 2 ∧
    SourceHistory parameterConfig 40 [] (.value witnessEnvironment (.call 1 parameterArguments 0)) .initial (.ok .unit after) := by
  have supported : SupportedOperation parameterConfig (.value witnessEnvironment (.call 1 parameterArguments 0)) :=
    .valueCallWith witnessEnvironment 1 parameterArguments 0 parameterTargetContext parameterTargetImplementation rfl rfl rfl
      (parameterCall_supported witnessEnvironment)
  have history := history_exists 40 parameterConfig (.value witnessEnvironment (.call 1 parameterArguments 0)) [] .initial supported
  refine ⟨witnessState (evalValue 40 parameterConfig witnessEnvironment (.call 1 parameterArguments 0) .initial), ?_, ?_, ?_, ?_⟩
  · unfold witnessState parameterConfig parameterSourceContext parameterTargetContext parameterSourceImplementation parameterTargetImplementation parameterArguments witnessEnvironment
    cbv
  · unfold witnessState parameterConfig parameterSourceContext parameterTargetContext parameterSourceImplementation parameterTargetImplementation parameterArguments witnessEnvironment
    cbv
  · unfold witnessState parameterConfig parameterSourceContext parameterTargetContext parameterSourceImplementation parameterTargetImplementation parameterArguments witnessEnvironment
    cbv
  · have actual : evalValue 40 parameterConfig witnessEnvironment (.call 1 parameterArguments 0) .initial =
        .ok .unit (witnessState (evalValue 40 parameterConfig witnessEnvironment (.call 1 parameterArguments 0) .initial)) := by
      unfold witnessState parameterConfig parameterSourceContext parameterTargetContext parameterSourceImplementation parameterTargetImplementation parameterArguments witnessEnvironment
      cbv
    change SourceHistory parameterConfig 40 [] (.value witnessEnvironment (.call 1 parameterArguments 0)) .initial
      (evalValue 40 parameterConfig witnessEnvironment (.call 1 parameterArguments 0) .initial) at history
    rw [actual] at history
    exact history

private def referenceTargetImplementation : Impl := ⟨"target", #[⟨0, .byRef⟩], #[], #[],
  .mk 1 [.print [.text "y"] 0] none, .unknown⟩
private def referenceConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[parameterSourceImplementation, referenceTargetImplementation],
    #[parameterSourceContext, parameterTargetContext], 0, #[], #[], #[]⟩⟩
private def referenceArguments : List Arg := [.byRef .mutable (.deref (.call 0 [] 0))]

theorem witness_referenceArgumentStop : ∃ after,
    invokeCall 40 referenceConfig witnessEnvironment 1 referenceArguments [] 0 .initial = .stop (.fault .shape) after ∧
    after.construction.stdout.data.toList = [120, 10] ∧ after.nextAct = 1 ∧
    SourceHistory referenceConfig 40 [] (.callWith witnessEnvironment 1 referenceArguments 0) .initial (.stop (.fault .shape) after) := by
  have sourceBody : ∀ environment, SupportedOperation referenceConfig (.statements environment [.print [.text "x"] 0]) := by
    intro environment
    exact .sequence environment (.printText environment "x" 0) (.empty environment)
  have sourceCall : SupportedOperation referenceConfig (.call witnessEnvironment 0 0) := by
    apply SupportedOperation.call witnessEnvironment 0 0 parameterSourceContext parameterSourceImplementation
    · rfl
    · rfl
    · rfl
    · rfl
    · intro act
      exact .activation _ 0 _ 0 sourceBody
  have args : SupportedOperation referenceConfig
      (.arguments witnessEnvironment referenceTargetImplementation.vars referenceTargetImplementation.params.toList referenceArguments) := by
    unfold referenceTargetImplementation referenceArguments
    exact .argumentReference _ _ _ _ .mutable _ _
      (.dereferencePlace witnessEnvironment _
        (.valueCall witnessEnvironment 0 0 parameterSourceContext parameterSourceImplementation rfl rfl rfl sourceCall))
      (.argumentsDone _ _)
  have targetBody : ∀ environment, SupportedOperation referenceConfig (.statements environment [.print [.text "y"] 0]) := by
    intro environment
    exact .sequence environment (.printText environment "y" 0) (.empty environment)
  have supported : SupportedOperation referenceConfig (.callWith witnessEnvironment 1 referenceArguments 0) := by
    apply SupportedOperation.callWith witnessEnvironment 1 referenceArguments 0 parameterTargetContext referenceTargetImplementation
    · rfl
    · rfl
    · rfl
    · exact args
    · intro act pre
      exact .boundActivation _ pre 1 _ 0 targetBody
  have history := history_exists 40 referenceConfig (.callWith witnessEnvironment 1 referenceArguments 0) [] .initial supported
  refine ⟨witnessState (invokeCall 40 referenceConfig witnessEnvironment 1 referenceArguments [] 0 .initial), ?_, ?_, ?_, ?_⟩
  · unfold witnessState referenceConfig referenceTargetImplementation referenceArguments parameterSourceContext parameterTargetContext parameterSourceImplementation witnessEnvironment
    cbv
  · unfold witnessState referenceConfig referenceTargetImplementation referenceArguments parameterSourceContext parameterTargetContext parameterSourceImplementation witnessEnvironment
    cbv
  · unfold witnessState referenceConfig referenceTargetImplementation referenceArguments parameterSourceContext parameterTargetContext parameterSourceImplementation witnessEnvironment
    cbv
  · have actual : invokeCall 40 referenceConfig witnessEnvironment 1 referenceArguments [] 0 .initial =
        .stop (.fault .shape) (witnessState (invokeCall 40 referenceConfig witnessEnvironment 1 referenceArguments [] 0 .initial)) := by
      unfold witnessState referenceConfig referenceTargetImplementation referenceArguments parameterSourceContext parameterTargetContext parameterSourceImplementation witnessEnvironment
      cbv
    change SourceHistory referenceConfig 40 [] (.callWith witnessEnvironment 1 referenceArguments 0) .initial
      (invokeCall 40 referenceConfig witnessEnvironment 1 referenceArguments [] 0 .initial) at history
    rw [actual] at history
    exact history

private def constructedTargetContext : Context := ⟨0, "target", [], [], []⟩
private def constructedTargetImplementation : Impl := ⟨"target", #[⟨0, .byValue⟩], #[],
  #[⟨"x", .varr (.int .u8), .immutable, 0, 0⟩], .mk 0 [.print [.text "y"] 0] none, .unknown⟩
private def constructedConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[constructedTargetImplementation], #[constructedTargetContext], 0, #[], #[], #[]⟩⟩
private def constructedArguments : List Arg := [.construct (.bytes (.varr (.int .u8)) [65, 66] 0)]

theorem witness_constructedArgument : ∃ after,
    invokeCall 40 constructedConfig witnessEnvironment 0 constructedArguments [] 0 .initial = .ok [] after ∧
    after.construction.stdout.data.toList = [121, 10] ∧
    after.construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] ∧
    SourceHistory constructedConfig 40 [] (.callWith witnessEnvironment 0 constructedArguments 0) .initial (.ok [] after) := by
  have args : SupportedOperation constructedConfig
      (.arguments witnessEnvironment constructedTargetImplementation.vars constructedTargetImplementation.params.toList constructedArguments) := by
    unfold constructedTargetImplementation constructedArguments
    exact .argumentConstruct _ _ _ _ _ _ (.valueBytes witnessEnvironment (.varr (.int .u8)) [65, 66] 0)
      (fun destination => .builderBytes witnessEnvironment destination (.varr (.int .u8)) [65, 66] 0) (.argumentsDone _ _)
  have body : ∀ environment, SupportedOperation constructedConfig (.statements environment [.print [.text "y"] 0]) := by
    intro environment
    exact .sequence environment (.printText environment "y" 0) (.empty environment)
  have supported : SupportedOperation constructedConfig (.callWith witnessEnvironment 0 constructedArguments 0) := by
    apply SupportedOperation.callWith witnessEnvironment 0 constructedArguments 0 constructedTargetContext constructedTargetImplementation
    · rfl
    · rfl
    · rfl
    · exact args
    · intro act pre
      exact .boundActivation _ pre 0 _ 0 body
  have history := history_exists 40 constructedConfig (.callWith witnessEnvironment 0 constructedArguments 0) [] .initial supported
  refine ⟨witnessState (invokeCall 40 constructedConfig witnessEnvironment 0 constructedArguments [] 0 .initial), ?_, ?_, ?_, ?_⟩
  · unfold witnessState constructedConfig constructedTargetContext constructedTargetImplementation constructedArguments witnessEnvironment
    cbv
  · unfold witnessState constructedConfig constructedTargetContext constructedTargetImplementation constructedArguments witnessEnvironment
    cbv
  · unfold witnessState constructedConfig constructedTargetContext constructedTargetImplementation constructedArguments witnessEnvironment
    cbv
  · have actual : invokeCall 40 constructedConfig witnessEnvironment 0 constructedArguments [] 0 .initial =
        .ok [] (witnessState (invokeCall 40 constructedConfig witnessEnvironment 0 constructedArguments [] 0 .initial)) := by
      unfold witnessState constructedConfig constructedTargetContext constructedTargetImplementation constructedArguments witnessEnvironment
      cbv
    change SourceHistory constructedConfig 40 [] (.callWith witnessEnvironment 0 constructedArguments 0) .initial
      (invokeCall 40 constructedConfig witnessEnvironment 0 constructedArguments [] 0 .initial) at history
    rw [actual] at history
    exact history

#print axioms witness_constructedArgument

#print axioms witness_referenceArgumentStop

#print axioms witness_parameterValueCall

#print axioms witness_parameterCall

#print axioms witness_nestedCallArgument

#print axioms witness_valueCall

#print axioms witness_call

theorem witness_boundActivation : ∃ after,
    enterActivation 40 activationWitnessConfig witnessEnvironment [(0, .int .i64 7)] activationWitnessBlock 0 .initial =
      .ok [] after ∧ after.construction.storage.size = 1 ∧
    SourceHistory activationWitnessConfig 40 []
      (.boundActivation witnessEnvironment [(0, .int .i64 7)] activationWitnessBlock 0) .initial (.ok [] after) := by
  have bodySupported : ∀ environment, SupportedOperation activationWitnessConfig
      (.statements environment [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0]) := by
    intro environment
    exact .sequence environment (.expression environment 0 (.value environment
      (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment)
  have supported : SupportedOperation activationWitnessConfig
      (.boundActivation witnessEnvironment [(0, .int .i64 7)] activationWitnessBlock 0) := by
    unfold activationWitnessBlock
    exact .boundActivation witnessEnvironment [(0, .int .i64 7)] 0 _ 0 bodySupported
  have history := history_exists 40 activationWitnessConfig
    (.boundActivation witnessEnvironment [(0, .int .i64 7)] activationWitnessBlock 0) [] .initial supported
  refine ⟨witnessState (enterActivation 40 activationWitnessConfig witnessEnvironment [(0, .int .i64 7)]
    activationWitnessBlock 0 .initial), ?_, ?_, ?_⟩
  · unfold activationWitnessConfig witnessEnvironment activationWitnessBlock witnessState
    cbv
  · unfold activationWitnessConfig witnessEnvironment activationWitnessBlock witnessState
    cbv
  · have actual : enterActivation 40 activationWitnessConfig witnessEnvironment [(0, .int .i64 7)] activationWitnessBlock 0 .initial =
        .ok [] (witnessState (enterActivation 40 activationWitnessConfig witnessEnvironment [(0, .int .i64 7)] activationWitnessBlock 0 .initial)) := by
      unfold activationWitnessConfig witnessEnvironment activationWitnessBlock witnessState
      cbv
    change SourceHistory activationWitnessConfig 40 []
      (.boundActivation witnessEnvironment [(0, .int .i64 7)] activationWitnessBlock 0) .initial
      (enterActivation 40 activationWitnessConfig witnessEnvironment [(0, .int .i64 7)] activationWitnessBlock 0 .initial) at history
    rw [actual] at history
    exact history

#print axioms witness_boundActivation

#print axioms witness_activationEntry

#print axioms witness_activationBody

#print axioms witness_nestedFill

#print axioms producerCallWith_source
#print axioms valueCallWith_source
#print axioms producerCall_source
#print axioms valueArgument_source
#print axioms valueCall_source
#print axioms emptyCall_enter
#print axioms emptyCall_depth
#print axioms emptyCall_one
#print axioms activationEnter_source
#print axioms activationBody_source
#print axioms history_exists

#print axioms ValueHistory.toSource
#print axioms StatementSequenceHistory.toSource
#print axioms value_exists
#print axioms statements_exist

#print axioms SourceHistory.sound
end Goose.Proofs.ConstructionGhostSourceMutual
