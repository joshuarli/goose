import Goose.Construct.Runtime

namespace Goose.Construct
open Goose.Core (ActId ScopeInst RootInst Loc StorageId DestinationId VarId GlobalId ContextId OriginId IntTy NumProfile AbortKind FaultKind BinOp)

structure EvalConfig where
  profile : NumProfile
  module : Module

def EvalConfig.layout (config : EvalConfig) : LayoutEnv := LayoutEnv.ofModule config.module

def returned (activation : ActId) (carriers : List Carrier) : EvalM α := fun state =>
  .escape ⟨activation, .ordinary⟩ carriers state

def escaped (address : ExitAddress) (carriers : List Carrier) : EvalM α := fun state =>
  .escape address carriers state

inductive Flow
  | normal (value : Value)
  | breaking (value : Option Value)
  | continuing

def expressionOrigin : Expr → OriginId
  | .bytes _ _ origin | .str _ _ origin | .copy _ _ origin | .resultLocal _ origin
  | .call _ _ origin | .un _ _ origin | .bin _ _ _ origin | .conv _ _ _ origin
  | .slice _ _ _ _ origin | .pop _ origin
  | .arrLit _ _ origin | .fill _ _ origin | .ifE _ _ _ origin | .blockE _ origin => origin
  | .push _ _ origin => origin.getD 0
  | _ => 0

def literalCount : Expr → Option Nat
  | .arrLit _ elements _ => some elements.length
  | .fill (.arr _ count) _ _ => some count
  | .bytes _ bytes _ => some bytes.length
  | .str _ arguments _ => arguments.foldlM (fun count argument => match argument with
      | .text text => some (count + text.toUTF8.size)
      | _ => none) 0
  | _ => none

def producerCount? (declarations : DeclarationEnv) (expression : Expr) : Option Nat :=
  match expression with
  | .copy _ source _ =>
      match declarations.placeType? source with
      | some (.arr _ count) => some count
      | _ => none
  | _ => literalCount expression

def ordinaryProducerCount? (fuel : Nat) (declarations : DeclarationEnv) (expression : Expr) : Option Nat :=
  if (producerCount? declarations expression).isSome then none
  else match expressionResultTypes? (max fuel (expressionQueryBudget expression)) declarations expression with
    | some [.arr element count] => if element.flat then some count else none
    | _ => none

def materializeProducer (fuel : Nat) (declarations : DeclarationEnv) (expression : Expr)
    (evaluate : EvalM Value) : EvalM (Option (Array Value)) := do
  match ordinaryProducerCount? fuel declarations expression with
  | none => pure none
  | some _ =>
      let .fixed values ← evaluate | fault .shape
      pure (some values)

def materializedDestination (fuel : Nat) (layout : LayoutEnv) (owner : ActId) (ty : Ty)
    (origin : OriginId) (count : Nat) (value : Value) : EvalM DestinationId := do
  let destination ← newDestination layout owner ty .value origin none (some count)
  copyValue fuel layout destination value origin none
  completedReceivingDestination destination

def constructLocal (declarations : DeclarationEnv) (owner : ActId) (ty : Ty) (origin : OriginId) (expression : Expr)
    (construct : DestinationId → EvalM Unit) : EvalM Carrier := do
  let destination ← newDestination (LayoutEnv.ofModule declarations.module) owner ty .value origin none
    (producerCount? declarations expression)
  construct destination
  let destination ← completedReceivingDestination destination
  publishCarriers origin [.completed destination]
  pure (.completed destination)

def getImplementation (config : EvalConfig) (context : ContextId) : EvalM (Core.ImplId × Impl) := do
  let some context := config.module.contexts[context]? | fault .unbound
  let some implementation := config.module.impls[context.impl]? | fault .unbound
  pure (context.impl, implementation)

def enclosingActivation (environment : RuntimeActivation) : EvalM RuntimeActivation := do
  let some activation := (← EvalM.get).activations.find? (fun activation => activation.act == environment.act) | fault .flow
  pure { activation with scopes := environment.scopes }

def targetActivation (config : EvalConfig) (target : Nat) : EvalM RuntimeActivation := do
  let some target := config.module.targets[target]? | fault .unbound
  let some activation := selectTarget? target (← EvalM.get).activations | fault .flow
  pure activation

def exitSource (source : RuntimeActivation) (incoming : DestinationId) (operand : Expr) : EvalM ExitSource := do
  let id ← receivingDestination incoming
  let alias ← match operand with
    | .resultLocal localVar _ => do
        let root ← rootOf source localVar
        match (← EvalM.get).objects.lookup root with
        | some (.stored stored) => pure (stored.destination == some id)
        | _ => pure false
    | _ => pure false
  pure (if alias then .namedResult else .newValue)

def selectCompletionChannel (source : RuntimeActivation) (operand : Expr) : Channel → EvalM Channel
  | .completion token => do
      let state ← EvalM.get
      let some (.waiting incoming) := state.construction.exitReservations[token]? | fault .flow
      let kind ← exitSource source incoming operand
      let selected ← liftConstruction (expressionOrigin operand) (selectWaitingExitDestination token kind)
      pure (.construct selected)
  | channel => pure channel

def exitChannels (source activation : RuntimeActivation) (operands : List Expr) (origin : OriginId) : EvalM (List Channel) := do
  if operands.length != activation.channels.length then fault .arity
  (activation.channels.zip operands).mapM fun (channel, operand) => do
    let reserve := fun incoming => do
      let kind ← exitSource source incoming operand
      let (_, selected) ← liftConstruction origin (reserveExitDestination incoming kind)
      pure (Channel.construct selected)
    match channel with
    | .register ty => pure (.register ty)
    | .construct incoming => reserve incoming
    | .completion token =>
        match (← EvalM.get).construction.exitReservations[token]? with
        | some (.waiting _) => pure (.completion token)
        | some (.active _ _ selected _) => reserve (← receivingDestination selected)
        | _ => fault .flow

def materializeOwnedCarriers (origin : OriginId) (tokens : List ExitReservationId)
    (carriers : List Carrier) : EvalM (List Carrier) :=
  carriers.mapM fun carrier => match carrier with
    | .pendingNamed token =>
        if tokens.contains token then do
          pure (.completed (← liftConstruction origin (materializeNamedReservation token)))
        else pure carrier
    | carrier => pure carrier

def withExitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : OriginId) (action : List Channel → EvalM (List Carrier)) : EvalM (List Carrier) := fun state =>
  let borrowed := activation.channels.filterMap fun channel => match channel with
    | .completion token => captureWaitingExitReservation token state.construction
    | _ => none
  let first := state.construction.exitReservations.size
  match exitChannels source activation operands origin state with
  | .ok channels prepared =>
      let tokens := (List.range (prepared.construction.exitReservations.size - first)).map (first + ·)
      let finish := fun (cancel : Bool) (carriers : List Carrier)
          (result : ExecutionState → ExecutionStep (List Carrier)) (state' : ExecutionState) =>
        let cleanup : EvalM Unit := do
          if cancel then
            for receipt in borrowed.reverse do
              let token := receipt.token
              if carriers.any (fun carrier => match carrier with
                  | .pendingNamed actual => actual == token
                  | _ => false) then pure ()
              else do
                liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
                  match carrier with | .completed id => some id | _ => none))
                match (← EvalM.get).construction.exitReservations[token]? with
                | some .restored => liftConstruction origin (rearmExitReservation receipt)
                | some (.waiting actual) => if actual != receipt.incoming then fault .flow
                | some (.active ..) => pure ()
                | _ => fault .flow
          for token in tokens.reverse do
            if cancel then
              liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
                match carrier with | .completed id => some id | _ => none))
            liftConstruction origin (releaseExitReservation token)
        match cleanup state' with
        | .ok () final => result final
        | .stop reason final => .stop reason final
        | .escape target values final => .escape target values final
        | .jump target kind final => .jump target kind final
      let evaluated : EvalM (List Carrier) := do
        materializeOwnedCarriers origin tokens (← action channels)
      match evaluated prepared with
      | .ok carriers state' => finish false carriers (.ok carriers) state'
      | .stop reason state' => finish false [] (.stop reason) state'
      | .escape target carriers state' => finish true carriers (.escape target carriers) state'
      | .jump target kind state' =>
          let carriers := match kind with | .breakValue carriers => carriers | .continueLoop => []
          finish true carriers (.jump target kind) state'
  | .stop reason state' => .stop reason state'
  | .escape target carriers state' => .escape target carriers state'
  | .jump target kind state' => .jump target kind state'


def completionChannelSetup (channels : List Channel) (origin : OriginId) : EvalM (List Channel × List ExitReservationId) := do
  let planned ← channels.mapM fun channel => match channel with
    | .construct incoming => do
        let token ← liftConstruction origin (waitExitDestination incoming)
        pure (Channel.completion token, some token)
    | .register ty => pure (Channel.register ty, none)
    | .completion _ => fault .flow
  pure (planned.map Prod.fst, planned.filterMap Prod.snd)

def withCompletionChannels (channels : List Channel) (origin : OriginId)
    (action : List Channel → EvalM (List Carrier)) : EvalM (List Carrier) := fun state =>
  match completionChannelSetup channels origin state with
  | .ok (planned, tokens) prepared =>
      let finish := fun (cancel : Bool) (carriers : List Carrier)
          (result : ExecutionState → ExecutionStep (List Carrier)) (state' : ExecutionState) =>
        let cleanup : EvalM Unit := do
          for token in tokens.reverse do
            if cancel then
              liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
                match carrier with | .completed id => some id | _ => none))
            liftConstruction origin (releaseExitReservation token)
        match cleanup state' with
        | .ok () final => result final
        | .stop reason final => .stop reason final
        | .escape target values final => .escape target values final
        | .jump target kind final => .jump target kind final
      let evaluated : EvalM (List Carrier) := do
        materializeOwnedCarriers origin tokens (← action planned)
      match evaluated prepared with
      | .ok carriers state' => finish false carriers (.ok carriers) state'
      | .stop reason state' => finish false [] (.stop reason) state'
      | .escape target carriers state' => finish true carriers (.escape target carriers) state'
      | .jump target kind state' =>
          let carriers := match kind with | .breakValue carriers => carriers | .continueLoop => []
          finish true carriers (.jump target kind) state'
  | .stop reason state' => .stop reason state'
  | .escape target carriers state' => .escape target carriers state'
  | .jump target kind state' => .jump target kind state'

def execResultScope (environment : RuntimeActivation) (pre : List (VarId × Value))
    (channels : List Channel) (block : Block)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier)) : EvalM (Flow × List Carrier) := do
  let .mk scope statements value := block
  let scopeInst ← freshScope
  let environment' := { environment with scopes := (scope, scopeInst) :: environment.scopes }
  let state ← EvalM.get
  EvalM.set { state with activations := state.activations.map (fun current =>
    if current.act == environment.act then { current with scopes := environment'.scopes } else current) }
  withScope environment scope scopeInst do
    bindAll environment.act scopeInst pre
    let flow ← statementsAction environment' statements
    match flow, value with
    | .normal _, some expression => pure (.normal .unit, ← tailAction environment' expression)
    | .normal _, none =>
        if channels.isEmpty then pure (flow, [])
        else match channels with
          | [.register .unit] => pure (flow, [.register .unit])
          | _ => fault .arity
    | flow, _ => pure (flow, [])



set_option maxHeartbeats 400000 in
mutual
def evalValue : Nat → EvalConfig → RuntimeActivation → Expr → EvalM Value
  | 0, _, _, _ => timeout
  | fuel + 1, config, environment, expression => do
      match expression with
      | .lit ty value => pure (.int ty value)
      | .bool value => pure (.bool value)
      | .read place => readLoc fuel config.layout (← evalPlace fuel config environment place)
      | .ref _ place => pure (.ref (← evalPlace fuel config environment place))
      | .slice _ view lo hi origin =>
          let view ← evalView fuel config environment view
          let lo ← evalBound fuel config environment view.count 0 lo
          let hi ← evalBound fuel config environment view.count view.count hi
          if 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ (view.count : Int) then
            pure (.slice view.location (view.start + lo.toNat) (hi - lo).toNat)
          else abortAt .sliceOob origin
      | .len view => pure (.int .i64 (← evalView fuel config environment view).count)
      | .un operation operand origin =>
          let (ty, value) ← expectInt (← evalValue fuel config environment operand)
          match Core.evalUn config.profile operation ty value with
          | .ok result => pure (.int ty result)
          | .error reason => abortAt (AbortKind.ofNum reason) origin
      | .bin operation first second origin =>
          let (ty, first) ← expectInt (← evalValue fuel config environment first)
          let (otherTy, second) ← expectInt (← evalValue fuel config environment second)
          sameIntType ty otherTy
          match Core.evalBin config.profile operation ty first second with
          | .ok result => pure (.int ty result)
          | .error reason => abortAt (AbortKind.ofNum reason) origin
      | .cmp operation first second =>
          let first ← evalValue fuel config environment first
          let second ← evalValue fuel config environment second
          let (first, second) ← comparable first second
          pure (.bool (Core.evalCmp operation first second))
      | .and first second =>
          if (← expectBool (← evalValue fuel config environment first)) then
            pure (.bool (← expectBool (← evalValue fuel config environment second)))
          else pure (.bool false)
      | .or first second =>
          if (← expectBool (← evalValue fuel config environment first)) then pure (.bool true)
          else pure (.bool (← expectBool (← evalValue fuel config environment second)))
      | .not operand => pure (.bool (!(← expectBool (← evalValue fuel config environment operand))))
      | .conv kind target operand origin =>
          let (source, value) ← expectInt (← evalValue fuel config environment operand)
          let .int target := target | fault .shape
          match Core.evalConv config.profile kind source target value with
          | .ok result => pure (.int target result)
          | .error reason => abortAt (AbortKind.ofNum reason) origin
      | .call context arguments origin =>
          let (_, implementation) ← getImplementation config context
          let channels ← channelsFor config.layout environment.act implementation.results.toList origin
          let carriers ← invokeCall fuel config environment context arguments channels origin
          publishCarriers origin carriers
          carrierValue (← singleCarrier carriers)
      | .push owner operand origin =>
          pushValue fuel config environment owner operand (origin.getD 0)
      | .pop owner origin =>
          let location ← evalPlace fuel config environment owner
          let value ← readLoc fuel config.layout location
          let (count, _) ← arrayLength value
          if count == 0 then abortAt .popEmpty origin
          let result ← readLoc fuel config.layout ⟨location.root, location.path ++ [count - 1]⟩
          truncateOwner fuel config.layout location (count - 1) origin
          pure result
      | .ifE condition yes no _ =>
          let flow ← if (← expectBool (← evalValue fuel config environment condition)) then
            execBlock fuel config environment [] [] yes
          else execBlock fuel config environment [] [] no
          match flow with
          | .normal value => pure value
          | _ => fault .flow
      | .blockE block origin =>
          let some types := blockResultTypes? (max fuel (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block | fault .shape
          let channels ← channelsFor config.layout environment.act
            (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin
          let carriers ← evalProduce fuel config environment channels expression
          publishCarriers origin carriers
          carrierValue (← singleCarrier carriers)
      | .arrLit ty operands origin =>
          if ty.nonfixed then
            carrierValue (← constructLocal ⟨config.module, environment.vars⟩ environment.act ty origin expression
              (fun destination => buildExpr fuel config environment destination expression))
          else pure (.fixed (← operands.mapM (evalValue fuel config environment)).toArray)
      | .fill ty operand origin =>
          let .arr _ count := ty | fault .shape
          if ty.nonfixed then
            carrierValue (← constructLocal ⟨config.module, environment.vars⟩ environment.act ty origin expression
              (fun destination => buildExpr fuel config environment destination expression))
          else
            let value ← evalValue fuel config environment operand
            pure (.fixed (Array.replicate count value))
      | .structLit ty operands =>
          let .structT id _ := ty | fault .shape
          pure (.record id (← operands.mapM (evalValue fuel config environment)).toArray)
      | .bytes ty bytes origin =>
          if let .slice _ (.int .u8) := ty then
            let index ← freshScope
            let root := RootInst.global (config.module.globals.size + index)
            bindStaticRoot root (.fixed (bytes.map (fun byte => Value.int .u8 byte.toNat)).toArray)
            pure (.slice ⟨root, []⟩ 0 bytes.length)
          else if ty.nonfixed then
            carrierValue (← constructLocal ⟨config.module, environment.vars⟩ environment.act ty origin expression
              (fun destination => buildExpr fuel config environment destination expression))
          else pure (.fixed (bytes.map (fun byte => Value.int .u8 byte.toNat)).toArray)
      | .str ty _ origin =>
          let carrier ← constructLocal ⟨config.module, environment.vars⟩ environment.act ty origin expression
            (fun destination => buildExpr fuel config environment destination expression)
          let value ← carrierValue carrier
          if ty.nonfixed then pure value
          else
            let .stored stored := value | fault .shape
            let storage ← getStorage stored.storage
            liftExcept (fixedValue fuel config.layout ty storage.bytes stored.start)
      | .copy ty source origin =>
          if ty.nonfixed then
            carrierValue (← constructLocal ⟨config.module, environment.vars⟩ environment.act ty origin expression
              (fun destination => buildExpr fuel config environment destination expression))
          else
            let value ← readLoc fuel config.layout (← evalPlace fuel config environment source)
            match ty, value with
            | .arr _ count, .stored stored =>
                let (_, run) ← sampledStored stored
                if count != run.count then fault .shape
                pure (.fixed (← (List.range count).mapM (readStoredElement fuel config.layout stored)).toArray)
            | _, value => pure value
      | .resultLocal localVar _ => readLoc fuel config.layout ⟨← rootOf environment localVar, []⟩
      | .values operands =>
          match operands with
          | [] => pure .unit
          | [operand] => evalValue fuel config environment operand
          | _ => fault .arity

def evalBound : Nat → EvalConfig → RuntimeActivation → Nat → Int → Bound → EvalM Int
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, count, defaultValue, bound => do
      match bound with
      | .omitted => pure defaultValue
      | .expr operand => pure (← expectInt (← evalValue fuel config environment operand)).2
      | .fromEnd operand => pure ((count : Int) - (← expectInt (← evalValue fuel config environment operand)).2)

def evalPlace : Nat → EvalConfig → RuntimeActivation → Place → EvalM Loc
  | 0, _, _, _ => timeout
  | fuel + 1, config, environment, place => do
      match place with
      | .var localVar => pure ⟨← rootOf environment localVar, []⟩
      | .global global => pure ⟨.global global, []⟩
      | .deref operand => expectRef (← evalValue fuel config environment operand)
      | .elem view operand origin =>
          let view ← evalView fuel config environment view
          let (_, index) ← expectInt (← evalValue fuel config environment operand)
          if 0 ≤ index ∧ index < (view.count : Int) then
            pure ⟨view.location.root, view.location.path ++ [view.start + index.toNat]⟩
          else abortAt .indexOob origin
      | .field owner index =>
          let location ← evalPlace fuel config environment owner
          pure ⟨location.root, location.path ++ [index]⟩

def evalView : Nat → EvalConfig → RuntimeActivation → View → EvalM RuntimeView
  | 0, _, _, _ => timeout
  | fuel + 1, config, environment, view => do
      match view with
      | .of place =>
          let location ← evalPlace fuel config environment place
          let (count, dynamic) ← arrayLength (← readLoc fuel config.layout location)
          pure ⟨location, 0, count, dynamic⟩
      | .val operand =>
          match (← evalValue fuel config environment operand) with
          | .slice location start count => pure ⟨location, start, count, false⟩
          | value =>
              let (count, dynamic) ← arrayLength value
              let index ← freshScope
              let root := RootInst.global (config.module.globals.size + index)
              bindRoot root value
              pure ⟨⟨root, []⟩, 0, count, dynamic⟩

def evalProduce : Nat → EvalConfig → RuntimeActivation → List Channel → Expr → EvalM (List Carrier)
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, channels, expression => do
      let channels : List Channel ← channels.mapM fun channel => match channel with
        | .register ty => pure (.register ty)
        | .construct id => do pure (.construct (← liftConstruction (expressionOrigin expression) (renewReceivingDestination id)))
        | .completion token => pure (.completion token)
      let planned := channels
      let channels ← match expression with
        | .values _ | .ifE .. | .blockE .. => pure channels
        | _ => channels.mapM (selectCompletionChannel environment expression)
      match expression with
      | .resultLocal localVar origin =>
          match channels with
          | [.construct destination] =>
              let .stored stored ← readLoc fuel config.layout ⟨← rootOf environment localVar, []⟩ | fault .shape
              let named ← match planned with
                | [.completion token] => prepareNamedCarrierAt origin token destination stored
                | _ => prepareNamedCarrier origin destination stored
              match named with
              | some carrier => pure [carrier]
              | none =>
                  buildExpr fuel config environment destination expression
                  pure [.completed (← completedReceivingDestination destination)]
          | [] => let _ ← evalValue fuel config environment expression; pure []
          | [.register _] => pure [.register (← evalValue fuel config environment expression)]
          | _ => fault .arity
      | .values operands => evalOperands fuel config environment channels operands
      | .call context arguments origin => invokeCall fuel config environment context arguments channels origin
      | .ifE condition yes no _ =>
          let block := if (← expectBool (← evalValue fuel config environment condition)) then yes else no
          let (flow, carriers) ← execResultBlock fuel config environment channels block
          match flow with
          | .normal _ => pure carriers
          | _ => fault .flow
      | .blockE block origin =>
          withBreakTarget environment.act .block channels
            (do
              let (flow, carriers) ← execResultBlock fuel config environment channels block
              match flow with
              | .normal _ => pure carriers
              | _ => fault .flow)
            (fun kind => do
              match kind with
              | .breakValue carriers => landCarriersInto origin channels carriers; pure carriers
              | .continueLoop => fault .flow)
      | _ =>
          match channels with
          | [] =>
              let _ ← evalValue fuel config environment expression
              pure []
          | [.register _] => pure [.register (← evalValue fuel config environment expression)]
          | [.construct destination] =>
              buildExpr fuel config environment destination expression
              pure [.completed (← completedReceivingDestination destination)]
          | _ => fault .arity

def evalOperands : Nat → EvalConfig → RuntimeActivation → List Channel → List Expr → EvalM (List Carrier)
  | 0, _, _, _, _ => timeout
  | _ + 1, _, _, [], [] => pure []
  | fuel + 1, config, environment, channel :: channels, operand :: operands => do
      let carrier ← singleCarrier (← evalProduce fuel config environment [channel] operand)
      pure (carrier :: (← evalOperands fuel config environment channels operands))
  | _ + 1, _, _, _, _ => fault .arity

def buildExpr : Nat → EvalConfig → RuntimeActivation → DestinationId → Expr → EvalM Unit
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, incoming, expression => do
      let destination ← liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming)
      protectDestination (expressionOrigin expression) destination do
        match expression with
        | .call context arguments origin =>
            let carriers ← invokeCall fuel config environment context arguments [.construct destination] origin
            let .completed actual ← singleCarrier carriers | fault .shape
            let original ← getDestination (← receivingDestination destination)
            let actual ← getDestination actual
            if actual.storage != original.storage then fault .flow
        | .ifE condition yes no _ =>
            let block := if (← expectBool (← evalValue fuel config environment condition)) then yes else no
            let (flow, _) ← execResultBlock fuel config environment [.construct destination] block
            match flow with
            | .normal _ => pure ()
            | _ => fault .flow
        | .blockE block origin =>
            withBreakTarget environment.act .block [.construct destination]
              (do
                let (flow, _) ← execResultBlock fuel config environment [.construct destination] block
                match flow with
                | .normal _ => pure ()
                | _ => fault .flow)
              (fun kind => do
                match kind with
                | .breakValue carriers => landCarriersInto origin [.construct destination] carriers
                | .continueLoop => fault .flow)
        | .values [operand] => buildExpr fuel config environment destination operand
        | .arrLit _ operands origin =>
            let pending ← getDestination destination
            let some element := elementType pending.capability.logicalType | fault .shape
            for operand in operands do
              buildElement fuel config environment destination element operand
            receivingAction origin destination finishDestination
        | .fill ty operand origin =>
            let .arr element count := ty | fault .shape
            if element.nonfixed then
              let source ← newDestination config.layout environment.act element .value origin
              buildExpr fuel config environment source operand
              let source ← completedReceivingDestination source
              for _ in [0:count] do
                repeatElement fuel config.layout destination element source origin
              receivingAction origin destination (fun destination => retireRepeatedSource destination source)
            else
              let value ← evalValue fuel config environment operand
              let bytes ← liftExcept (fixedBytes fuel config.layout element value)
              for _ in [0:count] do receivingAction origin destination (fun destination => writeElement destination bytes)
            receivingAction origin destination finishDestination
        | .bytes _ bytes origin =>
            for byte in bytes do receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)
            receivingAction origin destination finishDestination
        | .str _ arguments origin =>
            for argument in arguments do
              let bytes ← evalPrintArg fuel config environment argument
              for byte in bytes.data do receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)
            receivingAction origin destination finishDestination
        | .copy _ source origin =>
            let location ← evalPlace fuel config environment source
            let value ← readLoc fuel config.layout location
            let source := ((← EvalM.get).objectOrdinals.lookup location.root).map (fun ordinal => Core.CopySource.storage ordinal location.path)
            copyValue fuel config.layout destination value origin source
        | .resultLocal localVar origin =>
            let value ← readLoc fuel config.layout ⟨← rootOf environment localVar, []⟩
            match value with
            | .stored stored =>
                if stored.destination == some destination then
                  let pending ← getDestination destination
                  match pending.progress with
                  | .built _ => pure ()
                  | .open _ => receivingAction origin destination finishDestination
                  | _ => fault .flow
                else copyValue fuel config.layout destination value origin none
            | _ => fault .shape
        | _ =>
            let value ← evalValue fuel config environment expression
            copyValue fuel config.layout destination value (expressionOrigin expression) none

def buildElement : Nat → EvalConfig → RuntimeActivation → DestinationId → Ty → Expr → EvalM Unit
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, parent, element, operand => do
      if element.nonfixed then
        let layout ← receivingLayout config.layout element
        let child ← receivingAction (expressionOrigin operand) parent (fun parent => openChild parent element layout)
        buildExpr fuel config environment child operand
        let child ← completedReceivingDestination child
        receivingAction (expressionOrigin operand) parent (fun parent => attachChild parent child)
      else
        let value ← evalValue fuel config environment operand
        let bytes ← liftExcept (fixedBytes fuel config.layout element value)
        receivingAction (expressionOrigin operand) parent (fun parent => writeElement parent bytes)

def evalArguments : Nat → EvalConfig → RuntimeActivation → Array LocalVar → List Param → List Arg → EvalM (List Value)
  | 0, _, _, _, _, _ => timeout
  | _ + 1, _, _, _, [], [] => pure []
  | fuel + 1, config, environment, parameterVars, parameter :: parameters, argument :: arguments => do
      let value ← match argument with
        | .byRef _ place => do pure (.ref (← evalPlace fuel config environment place))
        | .byVal operand => evalValue fuel config environment operand
        | .construct operand =>
            let some localVar := parameterVars[parameter.var]? | fault .unbound
            let materialized ← materializeProducer fuel ⟨config.module, environment.vars⟩ operand
              (evalValue fuel config environment operand)
            let carrier ← match materialized with
              | some values => do
                  let destination ← materializedDestination fuel config.layout environment.act localVar.ty
                    (expressionOrigin operand) values.size (.fixed values)
                  publishCarriers (expressionOrigin operand) [.completed destination]
                  pure (.completed destination)
              | none =>
                  constructLocal ⟨config.module, environment.vars⟩ environment.act localVar.ty (expressionOrigin operand) operand
                    (fun destination => buildExpr fuel config environment destination operand)
            carrierValue carrier
      pure (value :: (← evalArguments fuel config environment parameterVars parameters arguments))
  | _ + 1, _, _, _, _, _ => fault .arity

def invokeCall : Nat → EvalConfig → RuntimeActivation → ContextId → List Arg → List Channel → OriginId → EvalM (List Carrier)
  | 0, _, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, context, arguments, channels, origin => do
      let (id, implementation) ← getImplementation config context
      if channels.length != implementation.results.size then fault .arity
      let callableChannels ← (channels.zip implementation.results.toList).mapM fun (channel, result) => do
        match result.request, channel with
        | .register, _ => pure (Channel.register result.ty)
        | .value, .construct incoming | .elementRun, .construct incoming =>
            let destination ← liftConstruction origin (renewReceivingDestination incoming)
            liftConstruction origin (adaptDestinationType destination result.ty)
            pure (.construct destination)
        | .value, .register _ | .elementRun, .register _ => fault .shape
        | _, .completion _ => fault .flow
      let values ← evalArguments fuel config environment implementation.vars implementation.params.toList arguments
      let callableChannels ← callableChannels.mapM fun channel => match channel with
        | .register ty => pure (.register ty)
        | .construct destination => do
            pure (.construct (← liftConstruction origin (renewReceivingDestination destination)))
        | .completion _ => fault .flow
      let state ← EvalM.get
      if state.activations.length ≥ Core.maxCallDepth then timeout
      let act ← freshAct
      let activation : RuntimeActivation := ⟨id, act, implementation.vars, [], callableChannels⟩
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
      let carriers ← enterActivation fuel config activation pre implementation.body origin
      deliverCarriers fuel config.layout channels carriers origin

def enterActivation : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → Block → OriginId → EvalM (List Carrier)
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, activation, pre, body, origin => do
      let some implementation := config.module.impls[activation.implementation]? | fault .unbound
      finishActivation config.layout activation (implementation.results.toList.map (·.ty)) origin
        (execActivationBody fuel config activation pre body)

def execActivationBody : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → Block → EvalM (List Carrier)
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, activation, pre, body => do
      let (flow, carriers) ← execResultScope activation pre activation.channels body
        (fun environment statements => execStmts fuel config environment statements)
        (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
          (fun channels => evalProduce fuel config environment channels expression))
      match flow with
      | .normal _ => pure carriers
      | _ => fault .flow

def execResultBlock : Nat → EvalConfig → RuntimeActivation → List Channel → Block → EvalM (Flow × List Carrier)
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, channels, block =>
      execResultBlockWith fuel config environment [] channels block

def execResultBlockWith : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → List Channel → Block → EvalM (Flow × List Carrier)
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, pre, channels, block =>
      execResultScope environment pre channels block
        (fun environment statements => execStmts fuel config environment statements)
        (fun environment expression => evalProduce fuel config environment channels expression)

def execBlock : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → List Channel → Block → EvalM Flow
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, pre, channels, .mk scope statements value => do
      let scopeInst ← freshScope
      let environment' := { environment with scopes := (scope, scopeInst) :: environment.scopes }
      withScope environment scope scopeInst do
        bindAll environment.act scopeInst pre
        let flow ← execStmts fuel config environment' statements
        match flow, value with
        | .normal _, some expression =>
            if channels.isEmpty then pure (.normal (← evalValue fuel config environment' expression))
            else pure (.normal (← carrierValue (← singleCarrier (← evalProduce fuel config environment' channels expression))))
        | flow, _ => pure flow

def execStmts : Nat → EvalConfig → RuntimeActivation → List Stmt → EvalM Flow
  | 0, _, _, _ => timeout
  | _ + 1, _, _, [] => pure (.normal .unit)
  | fuel + 1, config, environment, statement :: statements => do
      match (← execStmt fuel config environment statement) with
      | .normal _ => execStmts fuel config environment statements
      | flow => pure flow

def execStmt : Nat → EvalConfig → RuntimeActivation → Stmt → EvalM Flow
  | 0, _, _, _ => timeout
  | fuel + 1, config, environment, statement => do
      match statement with
      | .letS localVar expression origin =>
          let some descriptor := environment.vars[localVar]? | fault .unbound
          let root ← rootOf environment localVar
          let value ←
            if descriptor.ty.nonfixed then
              let some implementation := config.module.impls[environment.implementation]? | fault .unbound
              let namedCandidate := implementation.results.toList.zipIdx |>.find? (fun (result, _) => result.namedLocal == some localVar)
              let named ← match namedCandidate with
                | some (result, index) =>
                    match environment.channels[index]? with
                    | some (.construct incoming) => do
                        let destination ← liftConstruction origin (renewReceivingDestination incoming)
                        let destination ← getDestination destination
                        pure (if destination.capability.request == .value then some (result, index) else none)
                    | _ => fault .flow
                | none => pure none
              let materialized ← if named.isNone then
                  materializeProducer fuel ⟨config.module, environment.vars⟩ expression (evalValue fuel config environment expression)
                else pure none
              let destination ← match named with
                | some (_, index) =>
                    match environment.channels[index]? with
                    | some (.construct destination) => liftConstruction origin (renewReceivingDestination destination)
                    | _ => fault .flow
                | none =>
                    newDestination config.layout environment.act descriptor.ty .value origin none
                      (materialized.map Array.size <|> producerCount? ⟨config.module, environment.vars⟩ expression)
              if named.isSome then liftConstruction origin (prepareNamedBinding destination descriptor.ty)
              match materialized with
              | some values => copyValue fuel config.layout destination (.fixed values) origin none
              | none => buildExpr fuel config environment destination expression
              let destination ← completedReceivingDestination destination
              if named.isNone then publishCarriers origin [.completed destination]
              let stored ← storedDestination destination
              let object ← if named.isSome then do pure (some (← liftConstruction origin reserveStorage)) else pure none
              pure (.stored { stored with ty := descriptor.ty, object := object })
            else evalValue fuel config environment expression
          bindRoot root value
          pure (.normal .unit)
      | .assign place expression _ =>
          let location ← evalPlace fuel config environment place
          let value ← evalValue fuel config environment expression
          writeLoc fuel config.layout location value
          pure (.normal .unit)
      | .assignOp operation place expression origin =>
          let location ← evalPlace fuel config environment place
          let (ty, oldValue) ← expectInt (← readLoc fuel config.layout location)
          let (otherTy, value) ← expectInt (← evalValue fuel config environment expression)
          sameIntType ty otherTy
          match Core.evalBin config.profile operation ty oldValue value with
          | .ok result => writeLoc fuel config.layout location (.int ty result); pure (.normal .unit)
          | .error reason => abortAt (AbortKind.ofNum reason) origin
      | .rebind localVar expression _ =>
          let value ← evalValue fuel config environment expression
          writeLoc fuel config.layout ⟨← rootOf environment localVar, []⟩ value
          pure (.normal .unit)
      | .expr expression _ =>
          let _ ← evalValue fuel config environment expression
          pure (.normal .unit)
      | .append owner source origin =>
          let location ← evalPlace fuel config environment owner
          let view ← evalView fuel config environment source
          appendRun fuel config.layout location view origin
          pure (.normal .unit)
      | .popN owner expression origin =>
          let location ← evalPlace fuel config environment owner
          let (_, count) ← expectInt (← evalValue fuel config environment expression)
          let (length, _) ← arrayLength (← readLoc fuel config.layout location)
          if count < 0 || count > (length : Int) then abortAt .popNRange origin
          truncateOwner fuel config.layout location (length - count.toNat) origin
          pure (.normal .unit)
      | .resize owner expression fill origin =>
          let location ← evalPlace fuel config environment owner
          let (_, size) ← expectInt (← evalValue fuel config environment expression)
          let value ← match fill with
            | none => pure none
            | some expression => do pure (some (← evalValue fuel config environment expression))
          let (length, _) ← arrayLength (← readLoc fuel config.layout location)
          let size := Core.wrap .i64 size
          if size < 0 then abortAt .resizeNegative origin
          if size.toNat ≤ length then truncateOwner fuel config.layout location size.toNat origin
          else
            match value with
            | none => abortAt .resizeFill origin
            | some value => appendFixedValues fuel config.layout location (List.replicate (size.toNat - length) value) origin
          pure (.normal .unit)
      | .clear owner origin =>
          truncateOwner fuel config.layout (← evalPlace fuel config environment owner) 0 origin
          pure (.normal .unit)
      | .assignWhole owner expression origin =>
          let location ← evalPlace fuel config environment owner
          truncateOwner fuel config.layout location 0 origin
          let .stored stored ← readLoc fuel config.layout location | fault .shape
          let materialized ← materializeProducer fuel ⟨config.module, environment.vars⟩ expression
            (evalValue fuel config environment expression)
          withOwnerExtension stored
            (ownerDestination config.layout stored .value
              (materialized.map Array.size <|> producerCount? ⟨config.module, environment.vars⟩ expression) origin)
            (fun destination => do
              match materialized with
              | some values => copyValue fuel config.layout destination (.fixed values) origin none
              | none => buildExpr fuel config environment destination expression
              publishOwner fuel config.layout location stored (← completedReceivingDestination destination) origin)
          pure (.normal .unit)
      | .ifS condition yes no _ =>
          if (← expectBool (← evalValue fuel config environment condition)) then execBlock fuel config environment [] [] yes
          else match no with
            | none => pure (.normal .unit)
            | some block => execBlock fuel config environment [] [] block
      | .while condition body _ => execWhile fuel config environment condition body
      | .forRange localVar first last body _ =>
          let (ty, first) ← expectInt (← evalValue fuel config environment first)
          let (otherTy, last) ← expectInt (← evalValue fuel config environment last)
          sameIntType ty otherTy
          execRange fuel config environment localVar ty first last body
      | .forEach localVar index view byRef body _ =>
          execEach fuel config environment localVar index byRef body (← evalView fuel config environment view) 0
      | .receive localVars producer origin =>
          let producerTypes := expressionResultTypes? (max fuel (expressionQueryBudget producer)) ⟨config.module, environment.vars⟩ producer
          let channels ← localVars.zipIdx.mapM fun (localVar, index) => do
            let some descriptor := environment.vars[localVar]? | fault .unbound
            let inlineType := (producerTypes.bind (fun types => types[index]?)).filter fun ty => ty.flat
            match inlineType with
            | some (.arr element count) => pure (.register (.arr element count))
            | _ =>
                if descriptor.ty.nonfixed then
                  pure (Channel.construct (← newDestination config.layout environment.act descriptor.ty .value origin))
                else pure (.register descriptor.ty)
          let carriers ← evalProduce fuel config environment channels producer
          if carriers.length != localVars.length then fault .arity
          let carriers ← (localVars.zip carriers).mapM fun (localVar, carrier) => do
            let some descriptor := environment.vars[localVar]? | fault .unbound
            match carrier with
            | .register (.fixed values) =>
                if descriptor.ty.nonfixed then
                  pure (.completed (← materializedDestination fuel config.layout environment.act descriptor.ty origin values.size (.fixed values)))
                else pure carrier
            | _ => pure carrier
          publishCarriers origin carriers
          for (localVar, carrier) in localVars.zip carriers do
            bindRoot (← rootOf environment localVar) (← carrierValue carrier)
          pure (.normal .unit)
      | .appendValue owner producer origin =>
          let location ← evalPlace fuel config environment owner
          let .fixed values ← evalValue fuel config environment producer | fault .shape
          appendFixedValues fuel config.layout location values.toList origin
          pure (.normal .unit)
      | .appendConstruct owner producer origin =>
          let location ← evalPlace fuel config environment owner
          let .stored stored ← readLoc fuel config.layout location | fault .shape
          withOwnerExtension stored
            (ownerDestination config.layout stored .elementRun (producerCount? ⟨config.module, environment.vars⟩ producer) origin)
            (fun destination => do
              buildExpr fuel config environment destination producer
              publishOwner fuel config.layout location stored (← completedReceivingDestination destination) origin)
          pure (.normal .unit)
      | .retValues operands origin =>
          let activation ← enclosingActivation environment
          let carriers ← withExitChannels environment activation operands origin
            (fun channels => evalOperands fuel config environment channels operands)
          returned activation.act carriers
      | .retForward producer origin =>
          let activation ← enclosingActivation environment
          let carriers ← withExitChannels environment activation (List.replicate activation.channels.length producer) origin
            (fun channels => evalProduce fuel config environment channels producer)
          returned activation.act carriers
      | .returnFrom target operands origin =>
          let activation ← targetActivation config target
          let carriers ← withExitChannels environment activation operands origin
            (fun channels => evalOperands fuel config environment channels operands)
          escaped ⟨activation.act, .nonlocal target⟩ carriers
      | .returnFromForward target producer origin =>
          let activation ← targetActivation config target
          let carriers ← withExitChannels environment activation (List.replicate activation.channels.length producer) origin
            (fun channels => evalProduce fuel config environment channels producer)
          escaped ⟨activation.act, .nonlocal target⟩ carriers
      | .breakValue expression origin =>
          let target ← currentBreak environment.act (some .block)
          let activation := { environment with channels := target.channels }
          let operands := match expression with
            | .values operands => operands
            | _ => List.replicate activation.channels.length expression
          let carriers ← withExitChannels environment activation operands origin
            (fun channels => evalProduce fuel config environment channels expression)
          jump target.id (.breakValue carriers)
      | .ret expression origin =>
          let activation ← enclosingActivation environment
          match expression with
          | some expression =>
              let operands := match expression with
                | .values operands => operands
                | _ => List.replicate activation.channels.length expression
              let carriers ← withExitChannels environment activation operands origin
                (fun channels => evalProduce fuel config environment channels expression)
              returned activation.act carriers
          | none =>
              if activation.channels.isEmpty then returned activation.act []
              else if activation.channels.length == 1 then returned activation.act [.register .unit]
              else fault .arity
      | .brk _ => jump (← currentBreak environment.act (some .loop)).id (.breakValue [])
      | .cont _ => jump (← currentBreak environment.act (some .loop)).id .continueLoop
      | .print arguments _ =>
          let parts ← arguments.mapM (evalPrintArg fuel config environment)
          emitStdout (parts.foldl (· ++ ·) ByteArray.empty ++ "\n".toUTF8)
          pure (.normal .unit)
      | .assertS expression origin =>
          if (← expectBool (← evalValue fuel config environment expression)) then pure (.normal .unit)
          else abortAt .assert origin
      | .abort _ origin => abortAt .userAbort origin
      | .exit expression _ =>
          let (_, code) ← expectInt (← evalValue fuel config environment expression)
          EvalM.stop (.exit code)

def evalPrintArg : Nat → EvalConfig → RuntimeActivation → PrintArg → EvalM ByteArray
  | 0, _, _, _ => timeout
  | fuel + 1, config, environment, argument => do
      match argument with
      | .text text => pure text.toUTF8
      | .expr expression => renderAny fuel config.layout .topLevel (← evalValue fuel config environment expression)
      | .view view => renderView fuel config.layout .topLevel (← evalView fuel config environment view)

def execWhile : Nat → EvalConfig → RuntimeActivation → Expr → Block → EvalM Flow
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, condition, body => do
      if (← expectBool (← evalValue fuel config environment condition)) then
        match (← loopBody fuel config environment [] body) with
        | .normal _ | .continuing => execWhile fuel config environment condition body
        | .breaking value => pure (.normal (value.getD .unit))
      else pure (.normal .unit)

def execRange : Nat → EvalConfig → RuntimeActivation → VarId → IntTy → Int → Int → Block → EvalM Flow
  | 0, _, _, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, localVar, ty, first, last, body => do
      if first < last then
        match (← loopBody fuel config environment [(localVar, .int ty first)] body) with
        | .normal _ | .continuing => execRange fuel config environment localVar ty (first + 1) last body
        | .breaking value => pure (.normal (value.getD .unit))
      else pure (.normal .unit)

def execEach : Nat → EvalConfig → RuntimeActivation → VarId → Option VarId → Bool → Block → RuntimeView → Nat → EvalM Flow
  | 0, _, _, _, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, localVar, index, byRef, body, view, current => do
      let count ← if view.dynamic then do pure (← arrayLength (← readLoc fuel config.layout view.location)).1 else pure view.count
      if current < count then
        let location : Loc := ⟨view.location.root, view.location.path ++ [view.start + current]⟩
        let value ← if byRef then pure (.ref location) else readLoc fuel config.layout location
        let pre := (localVar, value) :: (index.toList.map fun index => (index, Value.int .i64 current))
        match (← loopBody fuel config environment pre body) with
        | .normal _ | .continuing => execEach fuel config environment localVar index byRef body view (current + 1)
        | .breaking value => pure (.normal (value.getD .unit))
      else pure (.normal .unit)

def loopBody : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → Block → EvalM Flow
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, pre, body =>
      withBreakTarget environment.act .loop []
        (execBlock fuel config environment pre [] body)
        (fun kind => do
          match kind with
          | .continueLoop => pure .continuing
          | .breakValue [] => pure (.breaking none)
          | .breakValue carriers => pure (.breaking (some (← carrierValue (← singleCarrier carriers)))))

def pushValue : Nat → EvalConfig → RuntimeActivation → Place → Expr → OriginId → EvalM Value
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, owner, expression, origin => do
      let location ← evalPlace fuel config environment owner
      let .stored stored ← readLoc fuel config.layout location | fault .shape
      let (_, run) ← sampledStored stored
      let index ← if run.element.nonfixed then do
        withOwnerExtension stored
          (openElementReceiving config.layout environment.act location stored run.element
            (producerCount? ⟨config.module, environment.vars⟩ expression) origin)
          (fun destination => do
            buildExpr fuel config environment destination expression
            publishElementReceiving fuel config.layout location stored (← completedReceivingDestination destination) origin)
        pure run.count
      else do
        let value ← evalValue fuel config environment expression
        let (count, _) ← arrayLength (← readLoc fuel config.layout location)
        appendFixedValues fuel config.layout location [value] origin
        pure count
      pure (.ref ⟨location.root, location.path ++ [index]⟩)
end

def initGlobals (fuel : Nat) (config : EvalConfig) : List GlobalId → EvalM Unit
  | [] => pure ()
  | global :: globals => do
      let some descriptor := config.module.globals[global]? | fault .unbound
      let act ← freshAct
      let environment : RuntimeActivation := ⟨0, act, #[], [], []⟩
      let value ← if descriptor.ty.nonfixed then
        let materialized ← materializeProducer fuel ⟨config.module, environment.vars⟩ descriptor.init
          (evalValue fuel config environment descriptor.init)
        let carrier ← match materialized with
          | some values => do
              let destination ← materializedDestination fuel config.layout act descriptor.ty descriptor.org values.size (.fixed values)
              publishCarriers descriptor.org [.completed destination]
              pure (.completed destination)
          | none =>
              constructLocal ⟨config.module, environment.vars⟩ act descriptor.ty descriptor.org descriptor.init
                (fun destination => buildExpr fuel config environment destination descriptor.init)
        carrierValue carrier
      else evalValue fuel config environment descriptor.init
      bindRoot (.global global) value
      initGlobals fuel config globals

def runModule (fuel : Nat) (config : EvalConfig) : EvalM Unit := do
  initGlobals fuel config (List.range config.module.globals.size)
  let (_, implementation) ← getImplementation config config.module.entry
  let channels ← channelsFor config.layout 0 implementation.results.toList 0
  let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
  let carriers ← invokeCall fuel config environment config.module.entry [] channels 0
  publishCarriers 0 carriers

def eval (fuel : Nat) (profile : NumProfile) (module : Module) : ExecutionResult :=
  match runModule fuel ⟨profile, module⟩ .initial with
  | .ok () state => .done .returned state.construction.stdout state.construction.events
  | .stop (.abort kind origin) state => .done (.aborted kind origin) state.construction.stdout state.construction.events
  | .stop (.exit code) state => .done (.exited code) state.construction.stdout state.construction.events
  | .stop .timeout state => .timeout state.construction.stdout state.construction.events
  | .stop (.fault kind) _ => .fault kind
  | .escape _ _ _ | .jump _ _ _ => .fault .flow

end Goose.Construct
