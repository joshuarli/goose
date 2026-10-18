import Goose.Proofs.ExitExecutionInvocationStatementsBase
import Goose.Proofs.ExitExecutionInvocationValuesNative

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private def statementOwnerEscape (snapshot : Option PendingDestination) (destination : Nat)
    (address : ExitAddress) (carriers : List Carrier) (before : ExecutionState) : ExecutionStep α :=
  match snapshot with
  | none => .escape address carriers before
  | some parent =>
      match restoreCompletedOwner parent destination
          (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) before with
      | .ok () final => .escape address carriers final
      | .stop reason final => .stop reason final
      | .escape target payload final => .escape target payload final
      | .jump target kind final => .jump target kind final

inductive StatementInvocationUnwinds (config : EvalConfig)
    (address : ExitAddress) (carriers : List Carrier) (before : ExecutionState) :
    {α β : Type} → {parent : ExitInvocation α} → {child : ExitInvocation β} →
    {initial prepared : ExecutionState} → StatementInvocationEdge config parent initial child prepared → ExecutionStep α → Prop
  | assignPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.assignPlace fuel environment owner expression origin initial) outcome
  | assignOpPlace (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.BinOp) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.assignOpPlace fuel environment operation owner expression origin initial) outcome
  | rebindValue (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.rebindValue fuel environment localVar expression origin initial) outcome
  | expression (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.expression fuel environment expression origin initial) outcome
  | appendPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (view : View) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.appendPlace fuel environment owner view origin initial) outcome
  | popPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.popPlace fuel environment owner expression origin initial) outcome
  | resizePlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (fill : Option Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.resizePlace fuel environment owner expression fill origin initial) outcome
  | clearPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.clearPlace fuel environment owner origin initial) outcome
  | assignWholePlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.assignWholePlace fuel environment owner expression origin initial) outcome
  | ifCondition (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes : Block) (no : Option Block) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.ifCondition fuel environment condition yes no origin initial) outcome
  | while (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.«while» fuel environment condition body origin initial) outcome
  | rangeFirst (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.rangeFirst fuel environment localVar first last body origin initial) outcome
  | eachView (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (view : View) (byRef : Bool) (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.eachView fuel environment localVar index view byRef body origin initial) outcome
  | appendValuePlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.appendValuePlace fuel environment owner expression origin initial) outcome
  | appendConstructPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.appendConstructPlace fuel environment owner expression origin initial) outcome
  | assertValue (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.assertValue fuel environment expression origin initial) outcome
  | exitValue (fuel : Nat) (environment : RuntimeActivation) (expression : Expr) (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.exitValue fuel environment expression origin initial) outcome
  | letValue (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (descriptor : LocalVar) (root : Goose.Core.RootInst)
      (lookup : environment.vars[localVar]? = some descriptor)
      (fixed : descriptor.ty.nonfixed = false)
      (rootSelected : rootOf environment localVar initial = .ok root prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.letValue fuel environment localVar expression origin initial prepared descriptor root lookup fixed rootSelected) outcome
  | letMaterialize (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (descriptor : LocalVar) (root : Goose.Core.RootInst) (count : Nat)
      (named : StatementLetNamedPrefix config environment localVar origin initial descriptor root none prepared)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.letMaterialize fuel environment localVar expression origin initial prepared descriptor root count named materialize) outcome
  | letBuild (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat)
      (setup : StatementLetBuildPrefix fuel config environment localVar expression origin initial destination prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.letBuild fuel environment localVar expression origin initial prepared destination setup) outcome
  | assignValue (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.assignValue fuel environment owner expression origin initial prepared location selected) outcome
  | assignOpValue (fuel : Nat) (environment : RuntimeActivation) (operation : Goose.Core.BinOp)
      (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (old : Goose.Core.IntTy × Int)
      (setup : ((do
        let location ← evalPlace fuel config environment owner
        expectInt (← readLoc fuel config.layout location)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok old prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.assignOpValue fuel environment operation owner expression origin initial prepared old setup) outcome
  | appendView (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (view : View)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.appendView fuel environment owner view origin initial prepared location selected) outcome
  | popValue (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.popValue fuel environment owner expression origin initial prepared location selected) outcome
  | resizeCount (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (fill : Option Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.resizeCount fuel environment owner expression fill origin initial prepared location selected) outcome
  | resizeFill (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression fill : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (size : Goose.Core.IntTy × Int)
      (setup : ((do
        let _ ← evalPlace fuel config environment owner
        expectInt (← evalValue fuel config environment expression)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok size prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.resizeFill fuel environment owner expression fill origin initial prepared size setup) outcome
  | assignWholeMaterialize (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (stored : StoredValue) (count : Nat)
      (setup : ((do
        let location ← evalPlace fuel config environment owner
        truncateOwner fuel config.layout location 0 origin
        let .stored stored ← readLoc fuel config.layout location | fault .shape
        pure stored) : EvalM StoredValue) initial = .ok stored prepared)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.assignWholeMaterialize fuel environment owner expression origin initial prepared stored count setup materialize) outcome
  | assignWholeBuild (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementOwnerBuildPrefix fuel config environment (.assignWhole owner expression origin) initial snapshot destination prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = statementOwnerEscape snapshot destination address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.assignWholeBuild fuel environment owner expression origin initial prepared destination snapshot setup) outcome
  | ifYes (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes : Block) (no : Option Block)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.ifYes fuel environment condition yes no origin initial prepared conditionTrue) outcome
  | ifNo (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (yes no : Block)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (conditionFalse : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok false prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.ifNo fuel environment condition yes no origin initial prepared conditionFalse) outcome
  | rangeLast (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (start : Goose.Core.IntTy × Int)
      (firstValue : ((do expectInt (← evalValue fuel config environment first)) : EvalM (Goose.Core.IntTy × Int)) initial = .ok start prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.rangeLast fuel environment localVar first last body origin initial prepared start firstValue) outcome
  | rangeLoop (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (first last : Expr) (body : Block) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (ty : Goose.Core.IntTy) (start stop : Int)
      (setup : ((do
        let (ty, first) ← expectInt (← evalValue fuel config environment first)
        let (otherTy, last) ← expectInt (← evalValue fuel config environment last)
        sameIntType ty otherTy
        pure (ty, first, last)) : EvalM (Goose.Core.IntTy × Int × Int)) initial = .ok (ty, start, stop) prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.rangeLoop fuel environment localVar first last body origin initial prepared ty start stop setup) outcome
  | eachLoop (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (view : View) (byRef : Bool) (body : Block) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (runtimeView : RuntimeView)
      (selected : evalView fuel config environment view initial = .ok runtimeView prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.eachLoop fuel environment localVar index view byRef body origin initial prepared runtimeView selected) outcome
  | receiveProduce (fuel : Nat) (environment : RuntimeActivation) (localVars : List Goose.Core.VarId)
      (expression : Expr) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (channels : List Channel)
      (setup : statementInvocation_statementReceivePrefix fuel config environment localVars expression origin initial = .ok channels prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.receiveProduce fuel environment localVars expression origin initial prepared channels setup) outcome
  | appendValue (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (location : Goose.Core.Loc)
      (selected : evalPlace fuel config environment owner initial = .ok location prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.appendValue fuel environment owner expression origin initial prepared location selected) outcome
  | appendConstructBuild (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementOwnerBuildPrefix fuel config environment (.appendConstruct owner expression origin) initial snapshot destination prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = statementOwnerEscape snapshot destination address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.appendConstructBuild fuel environment owner expression origin initial prepared destination snapshot setup) outcome
  | printArgument (fuel : Nat) (environment : RuntimeActivation) (earlier after : List PrintArg) (argument : PrintArg)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (parts : List ByteArray)
      (printed : earlier.mapM (evalPrintArg fuel config environment) initial = .ok parts prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.printArgument fuel environment earlier after argument origin initial prepared parts printed) outcome
  | whileCondition (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.whileCondition fuel environment condition body initial) outcome
  | whileBody (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial prepared : ExecutionState)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.whileBody fuel environment condition body initial prepared conditionTrue) outcome
  | whileNext (fuel : Nat) (environment : RuntimeActivation) (condition : Expr) (body : Block)
      (initial checked prepared : ExecutionState) (flow : Flow)
      (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool) initial = .ok true checked)
      (bodyDone : loopBody fuel config environment [] body checked = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.whileNext fuel environment condition body initial checked prepared flow conditionTrue bodyDone continues) outcome
  | rangeBody (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (ty : Goose.Core.IntTy) (first last : Int) (body : Block) (initial : ExecutionState)
      (within : first < last)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.rangeBody fuel environment localVar ty first last body initial within) outcome
  | rangeNext (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (ty : Goose.Core.IntTy) (first last : Int) (body : Block) (initial prepared : ExecutionState) (flow : Flow)
      (within : first < last)
      (bodyDone : loopBody fuel config environment [(localVar, .int ty first)] body initial = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.rangeNext fuel environment localVar ty first last body initial prepared flow within bodyDone continues) outcome
  | eachBody (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat)
      (initial prepared : ExecutionState) (pre : List (Goose.Core.VarId × Value))
      (setup : StatementEachBodyPrefix fuel config localVar index byRef view current initial pre prepared)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.eachBody fuel environment localVar index byRef body view current initial prepared pre setup) outcome
  | eachNext (fuel : Nat) (environment : RuntimeActivation) (localVar : Goose.Core.VarId)
      (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat)
      (initial bound prepared : ExecutionState) (pre : List (Goose.Core.VarId × Value)) (flow : Flow)
      (setup : StatementEachBodyPrefix fuel config localVar index byRef view current initial pre bound)
      (bodyDone : loopBody fuel config environment pre body bound = .ok flow prepared)
      (continues : (∃ value, flow = .normal value) ∨ flow = .continuing)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.eachNext fuel environment localVar index byRef body view current initial bound prepared pre flow setup bodyDone continues) outcome
  | loopBlock (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) (initial : ExecutionState)  (outcome : ExecutionStep Flow)
      (finished : outcome = .escape address carriers { before with breaks := before.breaks.filter (fun entry => entry.id != initial.nextScope) }) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.loopBlock fuel environment pre body initial) outcome
  | pushPlace (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial : ExecutionState)  (outcome : ExecutionStep Value)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.pushPlace fuel environment owner expression origin initial) outcome
  | pushBuild (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (destination : Nat) (snapshot : Option PendingDestination)
      (setup : StatementPushBuildPrefix fuel config environment owner expression origin initial snapshot destination prepared)  (outcome : ExecutionStep Value)
      (finished : outcome = statementOwnerEscape snapshot destination address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.pushBuild fuel environment owner expression origin initial prepared destination snapshot setup) outcome
  | pushValue (fuel : Nat) (environment : RuntimeActivation) (owner : Place) (expression : Expr)
      (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
      (setup : StatementPushValuePrefix fuel config environment owner initial prepared)  (outcome : ExecutionStep Value)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.pushValue fuel environment owner expression origin initial prepared setup) outcome
  | globalValue (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState) (descriptor : Global) (environment : RuntimeActivation)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (fixed : descriptor.ty.nonfixed = false)  (outcome : ExecutionStep Unit)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.globalValue fuel global globals initial prepared descriptor environment setup fixed) outcome
  | globalMaterialize (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState) (descriptor : Global) (environment : RuntimeActivation) (count : Nat)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (nonfixed : descriptor.ty.nonfixed = true)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ descriptor.init = some count)  (outcome : ExecutionStep Unit)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.globalMaterialize fuel global globals initial prepared descriptor environment count setup nonfixed materialize) outcome
  | globalBuild (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared allocated : ExecutionState) (descriptor : Global) (environment : RuntimeActivation) (destination : Nat)
      (setup : statementInvocation_globalEnvironmentPrefix config global initial = .ok (descriptor, environment) prepared)
      (nonfixed : descriptor.ty.nonfixed = true)
      (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ descriptor.init = none)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act descriptor.ty .value descriptor.org none
        (producerCount? ⟨config.module, environment.vars⟩ descriptor.init) prepared = .ok destination allocated)  (outcome : ExecutionStep Unit)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.globalBuild fuel global globals initial prepared allocated descriptor environment destination setup nonfixed materialize allocation) outcome
  | globalNext (fuel : Nat) (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId)
      (initial prepared : ExecutionState)
      (setup : ((do
        let value ← statementInvocation_globalValuePrefix fuel config global
        bindRoot (.global global) value) : EvalM Unit) initial = .ok () prepared)  (outcome : ExecutionStep Unit)
      (finished : outcome = .escape address carriers before) :
      StatementInvocationUnwinds config address carriers before
        (StatementInvocationEdge.globalNext fuel global globals initial prepared setup) outcome

elab "statement_prefix_simp " equation:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let saved ← Lean.Elab.Tactic.saveState
  let evidence ← Lean.Elab.Term.elabTerm equation none
  let before ← Lean.Meta.inferType evidence
  Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [bind, pure, fault, EvalM.stop] at ($equation)))
  if (← Lean.Elab.Tactic.getGoals).isEmpty then return
  let after? ← Lean.Elab.Tactic.withMainContext do
    try
      let evidence ← Lean.Elab.Term.elabTerm equation none
      pure (some (← Lean.Meta.inferType evidence))
    catch _ => pure none
  if let some after := after? then
    if after == before then
      saved.restore
      throwError "native prefix is already reduced"

macro "statement_prefix " equation:ident : tactic => `(tactic|
  repeat' first
    | statement_prefix_simp $equation
    | split at ($equation))

theorem statementInvocation_bind_step (action : EvalM α) (next : α → EvalM β) (state : ExecutionState) :
    (action >>= next) state = match action state with
      | .ok value after => next value after
      | .stop reason after => .stop reason after
      | .escape address carriers after => .escape address carriers after
      | .jump target kind after => .jump target kind after := rfl

theorem statementInvocation_materialize_none (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (initial prepared : ExecutionState)
    (normal : materializeProducer fuel declarations expression evaluate initial = .ok none prepared) :
    ordinaryProducerCount? fuel declarations expression = none ∧ initial = prepared := by
  cases selectedCount : ordinaryProducerCount? fuel declarations expression with
  | none =>
      simp only [materializeProducer, selectedCount, pure, ExecutionStep.ok.injEq] at normal
      exact ⟨rfl, normal.2⟩
  | some count =>
      cases result : evaluate initial with
      | ok value after =>
          cases value <;> simp [materializeProducer, selectedCount, bind, pure, fault, EvalM.stop, result] at normal
      | stop reason after | escape target payload after | jump target kind after =>
          simp [materializeProducer, selectedCount, bind, result] at normal

theorem statementInvocation_materialize_none_iff (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (initial prepared : ExecutionState) :
    materializeProducer fuel declarations expression evaluate initial = .ok none prepared ↔
      ordinaryProducerCount? fuel declarations expression = none ∧ initial = prepared := by
  constructor
  · exact statementInvocation_materialize_none fuel declarations expression evaluate initial prepared
  · rintro ⟨count, rfl⟩
    simp [materializeProducer, count, pure]

private def statementExecutionGoal : Lean.Elab.Tactic.TacticM (Lean.Expr × Array Lean.Expr) :=
  Lean.Elab.Tactic.withMainContext do
    let target ← Lean.Elab.Tactic.getMainTarget
    let mut context := #[]
    for declaration in (← Lean.getLCtx) do
      context := context.push declaration.type
    pure (target, context)

partial def statementNativeBoundaries (expression : Lean.Expr) : Lean.MetaM (Array Lean.Expr) := do
  let expression := expression.consumeMData
  let mut result := #[expression]
  if let some matcher ← Lean.Meta.matchMatcherApp? expression then
    for discriminant in matcher.discrs do
      result := result ++ (← statementNativeBoundaries discriminant)
  else if expression.isApp then
    for argument in expression.getAppArgs do
      unless argument.isLambda || argument.isForall do
        result := result ++ (← statementNativeBoundaries argument)
  pure result

partial def statementNativeEqualities (evidence type : Lean.Expr) : Lean.MetaM (Array Lean.Expr) := do
  let type := type.consumeMData
  if type.isAppOfArity ``Eq 3 then return #[evidence]
  if type.isAppOfArity ``And 2 then
    let left ← Lean.Meta.mkAppM ``And.left #[evidence]
    let right ← Lean.Meta.mkAppM ``And.right #[evidence]
    return (← statementNativeEqualities left type.getAppArgs[0]!) ++
      (← statementNativeEqualities right type.getAppArgs[1]!)
  pure #[]

private def statementNativeArgumentHead (expression : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let expression ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf expression)
  let name := expression.getAppFn.constName?.getD .anonymous
  let type ← Lean.Meta.inferType expression
  let optionalCount := type.isAppOfArity ``Option 1 && type.getAppArgs[0]!.isConstOf ``Nat
  if optionalCount || [``OrElse.orElse, ``Option.orElse, ``Option.map, ``Option.isSome, ``Option.isNone, ``EvalConfig.layout].contains name then
    Lean.Meta.withTransparency .default (Lean.Meta.whnf expression)
  else pure expression

private def statementNativeArgumentsEqual (left right : Lean.Expr) : Lean.MetaM Bool := do
  if left == right then return true
  if left.getAppFn != right.getAppFn || left.getAppNumArgs != right.getAppNumArgs then return false
  for (left, right) in left.getAppArgs.zip right.getAppArgs do
    if left != right then
      let left ← statementNativeArgumentHead left
      let right ← statementNativeArgumentHead right
      if left.isFVar && right.isFVar && left != right then return false
      unless ← Lean.Meta.withTransparency .instances (Lean.Meta.isDefEq left right) do return false
  return true

elab "statement_execute_known" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← goal.getType).consumeMData
  unless target.isAppOfArity ``Eq 3 do throwError "expected native result equality"
  let boundaries := (← statementNativeBoundaries target.getAppArgs[1]!) ++ (← statementNativeBoundaries target.getAppArgs[2]!)
  for declaration in (← Lean.getLCtx) do
    for evidence in (← statementNativeEqualities declaration.toExpr declaration.type) do
      let type := (← Lean.Meta.inferType evidence).consumeMData
      let actual := type.getAppArgs[1]!.consumeMData
      let lhs ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf actual)
      let rhs := type.getAppArgs[2]!.consumeMData
      unless lhs == rhs do
        for boundary in boundaries do
          let normalized ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf boundary)
          let sameActual := boundary.getAppFn == actual.getAppFn
          let compared := if sameActual then actual else lhs
          let observed := if sameActual then boundary else normalized
          if boundary == actual || observed == compared || (observed.getAppFn == compared.getAppFn &&
              (← Lean.Meta.matchMatcherApp? actual).isNone) then
            let saved ← Lean.Meta.saveState
            if (← Lean.Meta.withTransparency .instances (Lean.Meta.isDefEq (← Lean.Meta.inferType boundary) (← Lean.Meta.inferType lhs))) &&
                (← statementNativeArgumentsEqual observed compared) then
              let rewritten := target.replace fun current => if current == boundary then some rhs else none
              if rewritten != target then
                let equality ← Lean.Meta.withLocalDeclD `nativeResult (← Lean.Meta.inferType boundary) fun value => do
                  let body := target.replace fun current => if current == boundary then some value else none
                  let function ← Lean.Meta.mkLambdaFVars #[value] body
                  Lean.Meta.mkAppM ``congrArg #[function, evidence]
                let goal ← goal.replaceTargetEq rewritten equality
                Lean.Elab.Tactic.replaceMainGoal [goal]
                return
            saved.restore
  throwError "no recorded native result at this boundary"

elab "statement_execute_condition" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← goal.getType).consumeMData
  unless target.isAppOfArity ``Eq 3 do throwError "expected native equality"
  for boundary in (← statementNativeBoundaries target.getAppArgs[1]!) do
    if (boundary.isAppOf ``ite || boundary.isAppOf ``dite) && boundary.getAppNumArgs >= 5 then
      let arguments := boundary.getAppArgs
      let condition := arguments[1]!
      let decision := arguments[2]!
      for declaration in (← Lean.getLCtx) do
        let saved ← Lean.Meta.saveState
        let mut chosen? := none
        if ← Lean.Meta.withTransparency .instances (Lean.Meta.isDefEq declaration.type condition) then
          chosen? := some (← Lean.Meta.mkAppM ``Decidable.isTrue #[declaration.toExpr])
        else
          let negated ← Lean.Meta.mkAppM ``Not #[condition]
          if ← Lean.Meta.withTransparency .instances (Lean.Meta.isDefEq declaration.type negated) then
            chosen? := some (← Lean.Meta.mkAppM ``Decidable.isFalse #[declaration.toExpr])
        if let some chosen := chosen? then
          let rewritten := target.replace fun current => if current == decision then some chosen else none
          if rewritten != target then
            let evidence ← Lean.Meta.mkAppM ``Subsingleton.elim #[decision, chosen]
            let equality ← Lean.Meta.withLocalDeclD `nativeDecision (← Lean.Meta.inferType decision) fun value => do
              let body := target.replace fun current => if current == decision then some value else none
              let function ← Lean.Meta.mkLambdaFVars #[value] body
              Lean.Meta.mkAppM ``congrArg #[function, evidence]
            let goal ← goal.replaceTargetEq rewritten equality
            Lean.Elab.Tactic.replaceMainGoal [goal]
            return
        saved.restore
  throwError "no recorded native branch premise"

elab "statement_execute_result" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in (← Lean.getLCtx) do
    let type := declaration.type.consumeMData
    if type.isAppOfArity ``Eq 3 then
      let lhs := type.getAppArgs[1]!.consumeMData
      let rhs := type.getAppArgs[2]!.consumeMData
      let environment ← Lean.getEnv
      let isConstructor := fun (expression : Lean.Expr) => match environment.find? (expression.getAppFn.constName?.getD .anonymous) with
        | some (.ctorInfo _) => true
        | _ => false
      if (isConstructor lhs && isConstructor rhs) || (lhs.isFVar && (rhs.isConstOf ``Bool.true || rhs.isConstOf ``Bool.false)) then
        let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
        Lean.Elab.Tactic.evalTactic (← `(tactic| cases ($evidence)))
        return
  throwError "no native result equality remains"

elab "statement_execute_unit" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in (← Lean.getLCtx) do
    let type ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf declaration.type)
    if type.isConstOf ``PUnit || type.isConstOf ``Unit then
      let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
      Lean.Elab.Tactic.evalTactic (← `(tactic| cases ($evidence)))
      return
  throwError "no native unit result remains"

elab "statement_execute_simp" : tactic => do
  let saved ← Lean.Elab.Tactic.saveState
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| assumption))
  catch _ =>
    saved.restore
    Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target := (← goal.getType).consumeMData
      unless target.isAppOfArity ``Eq 3 do throwError "expected native equality"
      let lhs := target.getAppArgs[1]!
      let rhs := target.getAppArgs[2]!
      unless lhs.getAppFn == rhs.getAppFn do throwError "different native result heads"
      Lean.Meta.withTransparency .instances goal.refl
      Lean.Elab.Tactic.replaceMainGoal []

partial def statementExecutionHead (expression : Lean.Expr) (materialize : Bool := true) : Lean.MetaM Lean.Expr := do
  let mut expression := expression.consumeMData
  if (expression.isAppOf ``ite || expression.isAppOf ``dite) && expression.getAppNumArgs >= 5 then
    let arguments := expression.getAppArgs
    let decision ← Lean.Meta.withTransparency .default
      (Lean.Meta.whnf (Lean.mkApp2 (Lean.mkConst ``Decidable.decide) arguments[1]! arguments[2]!))
    if decision.isConstOf ``Bool.true || decision.isConstOf ``Bool.false then
      let selected := arguments[if decision.isConstOf ``Bool.true then 3 else 4]!
      let selected := if expression.isAppOf ``dite then
        Lean.mkApp selected (Lean.mkApp2 (Lean.mkConst ``Decidable.reflects_decide) arguments[1]! arguments[2]!)
        else selected
      expression := Lean.mkAppN selected (arguments.extract 5 arguments.size)
  let mut reduced ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf expression)
  let name := reduced.getAppFn.constName?.getD .anonymous
  let wrappers := [``fault, ``timeout, ``abortAt, ``EvalM.stop, ``ExitInvocation.action, ``constructLocal,
    ``withOwnerExtension, ``withBreakTarget, ``mapStepState, ``statementOwnerEscape,
    ``statementInvocation_statementReceivePrefix, ``statementInvocation_globalEnvironmentPrefix,
    ``statementInvocation_globalValuePrefix]
  let mut unfoldHead := wrappers.contains name || (materialize && name == ``materializeProducer)
  if unfoldHead then
    if let some unfolded ← Lean.Meta.unfoldDefinition? reduced true then
      reduced ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf unfolded)
  if let some matcher ← Lean.Meta.matchMatcherApp? reduced then
    let discriminants ← matcher.discrs.mapM fun expression => statementExecutionHead expression materialize
    reduced := { matcher with discrs := discriminants }.toExpr
    reduced ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf reduced)
  pure reduced

elab "statement_execute_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← goal.getType).consumeMData
  unless target.isAppOfArity ``Eq 3 do throwError "expected native result equality"
  let arguments := target.getAppArgs
  let lhs ← statementExecutionHead arguments[1]!
  let rhs ← statementExecutionHead arguments[2]!
  if lhs == arguments[1]! && rhs == arguments[2]! then throwError "native execution is at a result boundary"
  let target ← Lean.Meta.mkEq lhs rhs
  let goal ← goal.change target (checkDefEq := false)
  Lean.Elab.Tactic.replaceMainGoal [goal]

elab "statement_execute_source" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless target.isAppOfArity ``Eq 3 do throwError "expected source result equality"
  let lhs := target.getAppArgs[1]!.consumeMData
  let name := lhs.getAppFn.constName?.getD .anonymous
  let arguments := lhs.getAppArgs
  if [``execStmt, ``execWhile, ``execRange, ``execEach, ``loopBody, ``Goose.Construct.pushValue].contains name then
    let fuel ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf arguments[0]!)
    unless fuel.isAppOfArity ``Nat.succ 1 || fuel.isConstOf ``Nat.zero do
      throwError "recursive child requires its recorded result"
  else if name == ``initGlobals then
    let globals ← Lean.Meta.withTransparency .instances (Lean.Meta.whnf arguments[2]!)
    unless globals.isAppOfArity ``List.cons 3 || globals.isAppOfArity ``List.nil 1 do
      throwError "recursive globals require their recorded result"
  else throwError "not an owned native source"
  match name.toString.splitOn "." |>.getLast! with
  | "execStmt" => Lean.Elab.Tactic.evalTactic (← `(tactic| rw [execStmt]))
  | "execWhile" => Lean.Elab.Tactic.evalTactic (← `(tactic| rw [execWhile]))
  | "execRange" => Lean.Elab.Tactic.evalTactic (← `(tactic| rw [execRange]))
  | "execEach" => Lean.Elab.Tactic.evalTactic (← `(tactic| rw [execEach]))
  | "loopBody" => Lean.Elab.Tactic.evalTactic (← `(tactic| rw [loopBody]))
  | "pushValue" => Lean.Elab.Tactic.evalTactic (← `(tactic| rw [Goose.Construct.pushValue]))
  | "initGlobals" => Lean.Elab.Tactic.evalTactic (← `(tactic| rw [initGlobals]))
  | _ => throwError "not an owned source equation"

partial def statementExecutionDiscriminant (expression : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if let some matcher ← Lean.Meta.matchMatcherApp? expression then
    if !matcher.discrs.isEmpty then return ← statementExecutionDiscriminant matcher.discrs[0]!
  pure expression

elab "statement_execute_split" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless target.isAppOfArity ``Eq 3 do throwError "expected native result equality"
  let lhs := target.getAppArgs[1]!.consumeMData
  let some matcher ← Lean.Meta.matchMatcherApp? lhs | throwError "no native branch remains"
  unless !matcher.discrs.isEmpty do throwError "no native discriminator remains"
  let discriminant ← statementExecutionDiscriminant matcher.discrs[0]!
  let expression ← Lean.Elab.Term.exprToSyntax discriminant
  Lean.Elab.Tactic.evalTactic (← `(tactic| cases nativeCase : ($expression)))

elab "statement_execute_step" : tactic => do
  let before ← statementExecutionGoal
  Lean.Elab.Tactic.evalTactic (← `(tactic| first
    | statement_execute_result
    | statement_execute_unit
    | statement_execute_simp
    | statement_execute_known
    | statement_execute_condition
    | statement_execute_source
    | statement_execute_reduce
    | statement_execute_split))
  if (← Lean.Elab.Tactic.getGoals).isEmpty then return
  if (← statementExecutionGoal) == before then throwError "native execution made no progress"

macro "statement_execute" : tactic => `(tactic| repeat' statement_execute_step)

elab "statement_open_prefix" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in (← Lean.getLCtx) do
    let type := (← Lean.instantiateMVars declaration.type).consumeMData
    if [``StatementLetNamedPrefix, ``StatementLetBuildPrefix, ``StatementOwnerSnapshot,
        ``StatementOwnerBuildPrefix, ``StatementEachBodyPrefix, ``StatementPushBuildPrefix,
        ``StatementPushValuePrefix].any type.getAppFn.isConstOf then
      let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
      Lean.Elab.Tactic.evalTactic (← `(tactic| cases ($evidence)))
      return
  throwError "no native prefix witness remains"

macro "statement_open_prefixes" : tactic => `(tactic| repeat' statement_open_prefix)

elab "statement_expand_prefix" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in (← Lean.getLCtx) do
    let type := declaration.type.consumeMData
    if type.isAppOfArity ``Eq 3 then
      let lhs := type.getAppArgs[1]!.consumeMData
      let rhs := type.getAppArgs[2]!.consumeMData
      if rhs.isAppOf ``ExecutionStep.ok then
        if true then
          let saved ← Lean.Elab.Tactic.saveState
          let evidence ← Lean.Elab.Term.exprToSyntax declaration.toExpr
          try
            if lhs.isAppOf ``materializeProducer && rhs.getAppArgs[1]!.isAppOf ``Option.none then
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                (obtain ⟨nativeCount, nativeState⟩ := statementInvocation_materialize_none _ _ _ _ _ _ $evidence
                 clear $evidence
                 cases nativeState)))
              return
            let reduced ← statementExecutionHead lhs false
            if reduced != lhs then
              let changed ← Lean.Meta.mkEq reduced rhs
              let goal ← (← Lean.Elab.Tactic.getMainGoal).changeLocalDecl declaration.fvarId changed (checkDefEq := false)
              Lean.Elab.Tactic.replaceMainGoal [goal]
              return
            if let some matcher ← Lean.Meta.matchMatcherApp? lhs then
              unless matcher.discrs.isEmpty do
                let discriminant ← statementExecutionDiscriminant matcher.discrs[0]!
                let expression ← Lean.Elab.Term.exprToSyntax discriminant
                Lean.Elab.Tactic.evalTactic (← `(tactic|
                  (generalize nativePrefixCase : ($expression) = nativePrefixValue at ($evidence)
                   cases nativePrefixValue)))
                return
            if lhs.isAppOf ``ite || lhs.isAppOf ``dite then
              Lean.Elab.Tactic.evalTactic (← `(tactic| split at ($evidence)))
              return
            throwError "native primitive result is already recorded"
          catch _ => saved.restore
  throwError "no compound native prefix remains"

elab "statement_prepare_step" : tactic => do
  let before ← statementExecutionGoal
  Lean.Elab.Tactic.evalTactic (← `(tactic| first | statement_execute_result | statement_open_prefix | statement_expand_prefix))
  if (← Lean.Elab.Tactic.getGoals).isEmpty then return
  if (← statementExecutionGoal) == before then throwError "native prefix made no progress"

macro "statement_prepare_prefixes" : tactic => `(tactic| repeat' statement_prepare_step)


def StatementInvocationEdge.Propagates (config : EvalConfig)
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared : ExecutionState} (edge : StatementInvocationEdge config parent initial child prepared) : Prop :=
  ∀ (address : ExitAddress) (carriers : List Carrier) (before : ExecutionState),
    child.action config prepared = .escape address carriers before →
      StatementInvocationUnwinds config address carriers before edge (parent.action config initial)

end Goose.Proofs.ExitExecution
