import Goose.Proofs.ExitExecutionInvocation

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

def statementInvocation_statementReceivePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVars : List Goose.Core.VarId) (producer : Expr) (origin : Goose.Core.OriginId) : EvalM (List Channel) := do
  let producerTypes := expressionResultTypes? (max fuel (expressionQueryBudget producer)) ⟨config.module, environment.vars⟩ producer
  localVars.zipIdx.mapM fun (localVar, index) => do
    let some descriptor := environment.vars[localVar]? | fault .unbound
    let inlineType := (producerTypes.bind (fun types => types[index]?)).filter fun ty => ty.flat
    match inlineType with
    | some (.arr element count) => pure (.register (.arr element count))
    | _ =>
        if descriptor.ty.nonfixed then
          pure (Channel.construct (← newDestination config.layout environment.act descriptor.ty .value origin))
        else pure (.register descriptor.ty)

def statementInvocation_globalEnvironmentPrefix (config : EvalConfig) (global : Goose.Core.GlobalId) :
    EvalM (Global × RuntimeActivation) := do
  let some descriptor := config.module.globals[global]? | fault .unbound
  let act ← freshAct
  pure (descriptor, ⟨0, act, #[], [], []⟩)

def statementInvocation_globalValuePrefix (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId) : EvalM Value := do
  let (descriptor, environment) ← statementInvocation_globalEnvironmentPrefix config global
  if descriptor.ty.nonfixed then
    let materialized ← materializeProducer fuel ⟨config.module, environment.vars⟩ descriptor.init
      (evalValue fuel config environment descriptor.init)
    let carrier ← match materialized with
      | some values => do
          let destination ← materializedDestination fuel config.layout environment.act descriptor.ty descriptor.org values.size (.fixed values)
          publishCarriers descriptor.org [.completed destination]
          pure (.completed destination)
      | none =>
          constructLocal ⟨config.module, environment.vars⟩ environment.act descriptor.ty descriptor.org descriptor.init
            (fun destination => buildExpr fuel config environment destination descriptor.init)
    carrierValue carrier
  else evalValue fuel config environment descriptor.init

inductive StatementLetNamedPrefix (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    ExecutionState → LocalVar → Goose.Core.RootInst → Option (ResultDescriptor × Nat) → ExecutionState → Prop
  | absent (initial prepared : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst)
      (implementation : Impl)
      (lookup : environment.vars[localVar]? = some descriptor)
      (nonfixed : descriptor.ty.nonfixed = true)
      (rootSelected : rootOf environment localVar initial = .ok root prepared)
      (implementationLookup : config.module.impls[environment.implementation]? = some implementation)
      (candidate : implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar) = none) :
      StatementLetNamedPrefix config environment localVar origin initial descriptor root none prepared
  | receiving (initial rooted renewed prepared : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst)
      (implementation : Impl) (result : ResultDescriptor) (index incoming destination : Nat) (receiving : PendingDestination)
      (lookup : environment.vars[localVar]? = some descriptor)
      (nonfixed : descriptor.ty.nonfixed = true)
      (rootSelected : rootOf environment localVar initial = .ok root rooted)
      (implementationLookup : config.module.impls[environment.implementation]? = some implementation)
      (candidate : implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar) = some (result, index))
      (channel : environment.channels[index]? = some (.construct incoming))
      (renewal : liftConstruction origin (renewReceivingDestination incoming) rooted = .ok destination renewed)
      (selection : getDestination destination renewed = .ok receiving prepared)
      (request : (receiving.capability.request == .value) = true) :
      StatementLetNamedPrefix config environment localVar origin initial descriptor root (some (result, index)) prepared
  | other (initial rooted renewed prepared : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst)
      (implementation : Impl) (result : ResultDescriptor) (index incoming destination : Nat) (receiving : PendingDestination)
      (lookup : environment.vars[localVar]? = some descriptor)
      (nonfixed : descriptor.ty.nonfixed = true)
      (rootSelected : rootOf environment localVar initial = .ok root rooted)
      (implementationLookup : config.module.impls[environment.implementation]? = some implementation)
      (candidate : implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localVar) = some (result, index))
      (channel : environment.channels[index]? = some (.construct incoming))
      (renewal : liftConstruction origin (renewReceivingDestination incoming) rooted = .ok destination renewed)
      (selection : getDestination destination renewed = .ok receiving prepared)
      (request : (receiving.capability.request == .value) = false) :
      StatementLetNamedPrefix config environment localVar origin initial descriptor root none prepared

inductive StatementLetBuildPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) :
    ExecutionState → Nat → ExecutionState → Prop
  | actual (initial selected materialized allocated prepared : ExecutionState) (descriptor : LocalVar)
      (root : Goose.Core.RootInst) (named : Option (ResultDescriptor × Nat)) (destination : Nat)
      (namedPrefix : StatementLetNamedPrefix config environment localVar origin initial descriptor root named selected)
      (materialization : ((if named.isNone then
          materializeProducer fuel ⟨config.module, environment.vars⟩ expression (evalValue fuel config environment expression)
        else pure none) : EvalM (Option (Array Value))) selected = .ok none materialized)
      (allocation : ((match named with
        | some (_, index) =>
            match environment.channels[index]? with
            | some (.construct destination) => liftConstruction origin (renewReceivingDestination destination)
            | _ => fault .flow
        | none => newDestination config.layout environment.act descriptor.ty .value origin none
            (producerCount? ⟨config.module, environment.vars⟩ expression)) : EvalM Nat) materialized = .ok destination allocated)
      (preparation : ((if named.isSome then liftConstruction origin (prepareNamedBinding destination descriptor.ty)
        else pure ()) : EvalM Unit) allocated = .ok () prepared) :
      StatementLetBuildPrefix fuel config environment localVar expression origin initial destination prepared

inductive StatementOwnerSnapshot (stored : StoredValue) :
    ExecutionState → Option PendingDestination → ExecutionState → Prop
  | actual (initial prepared : ExecutionState) (snapshot : Option PendingDestination)
      (selected : ((match stored.destination with
        | none => pure none
        | some id => do
            let parent ← getDestination id
            pure (match parent.progress with | .built _ => some parent | _ => none)) : EvalM (Option PendingDestination))
          initial = .ok snapshot prepared) :
      StatementOwnerSnapshot stored initial snapshot prepared

inductive StatementOwnerBuildPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) :
    Stmt → ExecutionState → Option PendingDestination → Nat → ExecutionState → Prop
  | whole (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId)
      (initial located truncated read materialized sampled prepared : ExecutionState)
      (location : Goose.Core.Loc) (stored : StoredValue) (snapshot : Option PendingDestination) (destination : Nat)
      (placeSelected : evalPlace fuel config environment owner initial = .ok location located)
      (truncation : truncateOwner fuel config.layout location 0 origin located = .ok () truncated)
      (storedSelected : readLoc fuel config.layout location truncated = .ok (.stored stored) read)
      (materialization : materializeProducer fuel ⟨config.module, environment.vars⟩ expression
        (evalValue fuel config environment expression) read = .ok none materialized)
      (snapshotSelected : StatementOwnerSnapshot stored materialized snapshot sampled)
      (allocation : ownerDestination config.layout stored .value
        (producerCount? ⟨config.module, environment.vars⟩ expression) origin sampled = .ok destination prepared) :
      StatementOwnerBuildPrefix fuel config environment (.assignWhole owner expression origin) initial snapshot destination prepared
  | append (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId)
      (initial located read sampled prepared : ExecutionState) (location : Goose.Core.Loc)
      (stored : StoredValue) (snapshot : Option PendingDestination) (destination : Nat)
      (placeSelected : evalPlace fuel config environment owner initial = .ok location located)
      (storedSelected : readLoc fuel config.layout location located = .ok (.stored stored) read)
      (snapshotSelected : StatementOwnerSnapshot stored read snapshot sampled)
      (allocation : ownerDestination config.layout stored .elementRun
        (producerCount? ⟨config.module, environment.vars⟩ expression) origin sampled = .ok destination prepared) :
      StatementOwnerBuildPrefix fuel config environment (.appendConstruct owner expression origin) initial snapshot destination prepared

inductive StatementEachBodyPrefix (fuel : Nat) (config : EvalConfig) (localVar : Goose.Core.VarId)
    (index : Option Goose.Core.VarId) (byRef : Bool) (view : RuntimeView) (current : Nat) :
    ExecutionState → List (Goose.Core.VarId × Value) → ExecutionState → Prop
  | actual (initial counted prepared : ExecutionState) (count : Nat) (value : Value)
      (countSelected : ((if view.dynamic then do pure (← arrayLength (← readLoc fuel config.layout view.location)).1
        else pure view.count) : EvalM Nat) initial = .ok count counted)
      (within : current < count)
      (valueSelected : ((if byRef then pure (.ref ⟨view.location.root, view.location.path ++ [view.start + current]⟩)
        else readLoc fuel config.layout ⟨view.location.root, view.location.path ++ [view.start + current]⟩) : EvalM Value)
          counted = .ok value prepared) :
      StatementEachBodyPrefix fuel config localVar index byRef view current initial
        ((localVar, value) :: index.toList.map (fun index => (index, Value.int .i64 current))) prepared

inductive StatementPushBuildPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    ExecutionState → Option PendingDestination → Nat → ExecutionState → Prop
  | actual (initial located read sampled snapshotted prepared : ExecutionState) (location : Goose.Core.Loc)
      (stored : StoredValue) (bytes : ByteArray) (run : SampledRun) (snapshot : Option PendingDestination) (destination : Nat)
      (placeSelected : evalPlace fuel config environment owner initial = .ok location located)
      (storedSelected : readLoc fuel config.layout location located = .ok (.stored stored) read)
      (runSelected : sampledStored stored read = .ok (bytes, run) sampled)
      (nonfixed : run.element.nonfixed = true)
      (snapshotSelected : StatementOwnerSnapshot stored sampled snapshot snapshotted)
      (allocation : openElementReceiving config.layout environment.act location stored run.element
        (producerCount? ⟨config.module, environment.vars⟩ expression) origin snapshotted = .ok destination prepared) :
      StatementPushBuildPrefix fuel config environment owner expression origin initial snapshot destination prepared

inductive StatementPushValuePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (owner : Place) : ExecutionState → ExecutionState → Prop
  | actual (initial located read prepared : ExecutionState) (location : Goose.Core.Loc)
      (stored : StoredValue) (bytes : ByteArray) (run : SampledRun)
      (placeSelected : evalPlace fuel config environment owner initial = .ok location located)
      (storedSelected : readLoc fuel config.layout location located = .ok (.stored stored) read)
      (runSelected : sampledStored stored read = .ok (bytes, run) prepared)
      (fixed : run.element.nonfixed = false) :
      StatementPushValuePrefix fuel config environment owner initial prepared

inductive StatementInvocationEdge (config : EvalConfig) :
    {α β : Type} → ExitInvocation α → ExecutionState → ExitInvocation β → ExecutionState → Prop
  | assignPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.assign owner expression origin)) initial
        (.place fuel environment owner) initial
  | assignOpPlace (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.BinOp) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.assignOp operation owner expression origin)) initial
        (.place fuel environment owner) initial
  | rebindValue (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.rebind localVar expression origin)) initial
        (.value fuel environment expression) initial
  | expression (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.expr expression origin)) initial
        (.value fuel environment expression) initial
  | appendPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (view : View) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.append owner view origin)) initial
        (.place fuel environment owner) initial
  | popPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.popN owner expression origin)) initial
        (.place fuel environment owner) initial
  | resizePlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (fill : Option Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.resize owner expression fill origin)) initial
        (.place fuel environment owner) initial
  | clearPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.clear owner origin)) initial
        (.place fuel environment owner) initial
  | assignWholePlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.assignWhole owner expression origin)) initial
        (.place fuel environment owner) initial
  | ifCondition (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes : Block) (no : Option Block) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.ifS condition yes no origin)) initial
        (.value fuel environment condition) initial
  | while (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.while condition body origin)) initial
        (.whileLoop fuel environment condition body) initial
  | rangeFirst (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.forRange localVar first last body origin)) initial
        (.value fuel environment first) initial
  | eachView (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (view : View) (byRef : Bool) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.forEach localVar index view byRef body origin)) initial
        (.view fuel environment view) initial
  | appendValuePlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.appendValue owner expression origin)) initial
        (.place fuel environment owner) initial
  | appendConstructPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.appendConstruct owner expression origin)) initial
        (.place fuel environment owner) initial
  | assertValue (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.assertS expression origin)) initial
        (.value fuel environment expression) initial
  | exitValue (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.exit expression origin)) initial
        (.value fuel environment expression) initial
  | letValue (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (descriptor : LocalVar) (root : Goose.Core.RootInst)
      (lookup : environment.vars[localVar]? = some descriptor)
      (fixed : descriptor.ty.nonfixed = false)
      (rootSelected : rootOf environment localVar initial = .ok root prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.letS localVar expression origin)) initial
        (.value fuel environment expression) prepared
  | letMaterialize (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (descriptor : LocalVar) (root : Goose.Core.RootInst) (count : Nat)
      (named : StatementLetNamedPrefix config environment localVar origin initial descriptor root none prepared)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.letS localVar expression origin)) initial
        (.value fuel environment expression) prepared
  | letBuild (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat)
      (setup : StatementLetBuildPrefix fuel config environment localVar expression origin initial destination prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.letS localVar expression origin)) initial
        (.build fuel environment destination expression) prepared
  | assignValue (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.assign owner expression origin)) initial
        (.value fuel environment expression) prepared
  | assignOpValue (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.BinOp)
      (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (old : Goose.Core.IntTy × Int)
      (setup : ((do
        let location ← evalPlace fuel config environment owner
        expectInt (← readLoc fuel config.layout location)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok old prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.assignOp operation owner expression origin)) initial
        (.value fuel environment expression) prepared
  | appendView (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (view : View)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.append owner view origin)) initial
        (.view fuel environment view) prepared
  | popValue (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.popN owner expression origin)) initial
        (.value fuel environment expression) prepared
  | resizeCount (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (fill : Option Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.resize owner expression fill origin)) initial
        (.value fuel environment expression) prepared
  | resizeFill (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression fill : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (size : Goose.Core.IntTy × Int)
      (setup : ((do
        let _ ← evalPlace fuel config environment owner
        expectInt (← evalValue fuel config environment expression)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok size prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.resize owner expression (some fill) origin)) initial
        (.value fuel environment fill) prepared
  | assignWholeMaterialize (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (stored : StoredValue) (count : Nat)
      (setup : ((do
        let location ← evalPlace fuel config environment owner
        truncateOwner fuel config.layout location 0 origin
        let .stored stored ← readLoc fuel config.layout location | fault .shape
        pure stored) : EvalM StoredValue) initial = .ok stored prepared)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.assignWhole owner expression origin)) initial
        (.value fuel environment expression) prepared
  | assignWholeBuild (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementOwnerBuildPrefix fuel config environment (.assignWhole owner expression origin) initial snapshot destination prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.assignWhole owner expression origin)) initial
        (.build fuel environment destination expression) prepared
  | ifYes (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes : Block) (no : Option Block)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.ifS condition yes no origin)) initial
        (.block fuel environment [] [] yes) prepared
  | ifNo (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes no : Block)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (conditionFalse : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok false prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.ifS condition yes (some no) origin)) initial
        (.block fuel environment [] [] no) prepared
  | rangeLast (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (start : Goose.Core.IntTy × Int)
      (firstValue : ((do expectInt (← evalValue fuel config environment first)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok start prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.forRange localVar first last body origin)) initial
        (.value fuel environment last) prepared
  | rangeLoop (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (ty : Goose.Core.IntTy) (start stop : Int)
      (setup : ((do
        let (ty, first) ← expectInt (← evalValue fuel config environment first)
        let (otherTy, last) ← expectInt (← evalValue fuel config environment last)
        sameIntType ty otherTy
        pure (ty, first, last)) : EvalM (Goose.Core.IntTy × Int × Int)) initial = .ok (ty, start, stop) prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.forRange localVar first last body origin)) initial
        (.rangeLoop fuel environment localVar ty start stop body) prepared
  | eachLoop (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (view : View) (byRef : Bool) (body : Block) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (runtimeView : RuntimeView)
      (selected : evalView fuel config environment view initial = .ok runtimeView prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.forEach localVar index view byRef body origin)) initial
        (.eachLoop fuel environment localVar index byRef body runtimeView 0) prepared
  | receiveProduce (fuel : Nat) (environment : RuntimeActivation) (localVars : List Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (channels : List Channel)
      (setup : statementInvocation_statementReceivePrefix fuel config environment localVars expression origin initial = .ok channels prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.receive localVars expression origin)) initial
        (.produce fuel environment channels expression) prepared
  | appendValue (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.appendValue owner expression origin)) initial
        (.value fuel environment expression) prepared
  | appendConstructBuild (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementOwnerBuildPrefix fuel config environment (.appendConstruct owner expression origin) initial snapshot destination prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.appendConstruct owner expression origin)) initial
        (.build fuel environment destination expression) prepared
  | printArgument (fuel : Nat) (environment : RuntimeActivation) (before after : List PrintArg) (argument : PrintArg)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (parts : List ByteArray)
      (printed : before.mapM (evalPrintArg fuel config environment) initial = .ok parts prepared) :
      StatementInvocationEdge config (.statement (fuel + 1) environment (.print (before ++ argument :: after) origin)) initial
        (.printArgument fuel environment argument) prepared
  | whileCondition (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial : ExecutionState) :
      StatementInvocationEdge config (.whileLoop (fuel + 1) environment condition body) initial
        (.value fuel environment condition) initial
  | whileBody (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial prepared : ExecutionState)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true prepared) :
      StatementInvocationEdge config (.whileLoop (fuel + 1) environment condition body) initial
        (.loop fuel environment [] body) prepared
  | whileNext (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial checked prepared : ExecutionState) (flow : Flow)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true checked)
      (bodyDone : loopBody fuel config environment [] body checked = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing) :
      StatementInvocationEdge config (.whileLoop (fuel + 1) environment condition body) initial
        (.whileLoop fuel environment condition body) prepared
  | rangeBody (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (ty : Goose.Core.IntTy) (first last : Int) (body : Block) (initial : ExecutionState)
      (within : first < last) :
      StatementInvocationEdge config (.rangeLoop (fuel + 1) environment localVar ty first last body) initial
        (.loop fuel environment [(localVar, .int ty first)] body) initial
  | rangeNext (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (ty : Goose.Core.IntTy) (first last : Int) (body : Block) (initial prepared : ExecutionState) (flow : Flow)
      (within : first < last)
      (bodyDone : loopBody fuel config environment [(localVar, .int ty first)] body initial = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing) :
      StatementInvocationEdge config (.rangeLoop (fuel + 1) environment localVar ty first last body) initial
        (.rangeLoop fuel environment localVar ty (first + 1) last body) prepared
  | eachBody (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat)
      (initial prepared : ExecutionState) (pre : List (Goose.Core.VarId × Value))
      (setup : StatementEachBodyPrefix fuel config localVar index byRef view current initial pre prepared) :
      StatementInvocationEdge config (.eachLoop (fuel + 1) environment localVar index byRef body view current) initial
        (.loop fuel environment pre body) prepared
  | eachNext (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat)
      (initial bound prepared : ExecutionState) (pre : List (Goose.Core.VarId × Value)) (flow : Flow)
      (setup : StatementEachBodyPrefix fuel config localVar index byRef view current initial pre bound)
      (bodyDone : loopBody fuel config environment pre body bound = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing) :
      StatementInvocationEdge config (.eachLoop (fuel + 1) environment localVar index byRef body view current) initial
        (.eachLoop fuel environment localVar index byRef body view (current + 1)) prepared
  | loopBlock (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) (initial : ExecutionState) :
      StatementInvocationEdge config (.loop (fuel + 1) environment pre body) initial
        (.block fuel environment pre [] body)
        { initial with nextScope := initial.nextScope + 1, breaks := ⟨initial.nextScope, environment.act, .loop, []⟩ :: initial.breaks }
  | pushPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial : ExecutionState) :
      StatementInvocationEdge config (.push (fuel + 1) environment owner expression origin) initial
        (.place fuel environment owner) initial
  | pushBuild (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementPushBuildPrefix fuel config environment owner expression origin initial snapshot destination prepared) :
      StatementInvocationEdge config (.push (fuel + 1) environment owner expression origin) initial
        (.build fuel environment destination expression) prepared
  | pushValue (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (setup : StatementPushValuePrefix fuel config environment owner initial prepared) :
      StatementInvocationEdge config (.push (fuel + 1) environment owner expression origin) initial
        (.value fuel environment expression) prepared
  | globalValue (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState) (descriptor : Global) (environment : RuntimeActivation)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (fixed : descriptor.ty.nonfixed = false) :
      StatementInvocationEdge config (.globals fuel (global :: globals)) initial
        (.value fuel environment descriptor.init) prepared
  | globalMaterialize (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState) (descriptor : Global) (environment : RuntimeActivation) (count : Nat)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (nonfixed : descriptor.ty.nonfixed = true)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ descriptor.init = some count) :
      StatementInvocationEdge config (.globals fuel (global :: globals)) initial
        (.value fuel environment descriptor.init) prepared
  | globalBuild (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared allocated : ExecutionState) (descriptor : Global) (environment : RuntimeActivation) (destination : Nat)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (nonfixed : descriptor.ty.nonfixed = true)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ descriptor.init = none)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act descriptor.ty .value descriptor.org none
        (producerCount? ⟨config.module, environment.vars⟩ descriptor.init) prepared = .ok destination allocated) :
      StatementInvocationEdge config (.globals fuel (global :: globals)) initial
        (.build fuel environment destination descriptor.init) allocated
  | globalNext (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState)
      (setup : ((do
        let value ← statementInvocation_globalValuePrefix fuel config global
        bindRoot (.global global) value) : EvalM Unit) initial = .ok () prepared) :
      StatementInvocationEdge config (.globals fuel (global :: globals)) initial
        (.globals fuel globals) prepared

end Goose.Proofs.ExitExecution
