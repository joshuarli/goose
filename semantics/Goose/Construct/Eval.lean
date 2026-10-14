import Goose.Construct.Runtime

namespace Goose.Construct
open Goose.Core (ActId ScopeInst RootInst Loc StorageId DestinationId VarId GlobalId ContextId OriginId IntTy NumProfile AbortKind FaultKind BinOp)

private def returned (activation : ActId) (carriers : List Carrier) : EvalM α := fun state =>
  .escape activation carriers state

private inductive Flow
  | normal (value : Value)
  | breaking (value : Option Value)
  | continuing

private def expressionOrigin : Expr → OriginId
  | .bytes _ _ origin | .str _ _ origin | .copy _ _ origin | .resultLocal _ origin
  | .call _ _ origin | .un _ _ origin | .bin _ _ _ origin | .conv _ _ _ origin
  | .slice _ _ _ _ origin | .pop _ origin => origin
  | .push _ _ origin => origin.getD 0
  | _ => 0

private def literalCount : Expr → Option Nat
  | .arrLit _ elements => some elements.length
  | .fill (.arr _ count) _ => some count
  | .bytes _ bytes _ => some bytes.length
  | _ => none

private def constructLocal (module : Module) (owner : ActId) (ty : Ty) (origin : OriginId) (expression : Expr)
    (construct : DestinationId → EvalM Unit) : EvalM Carrier := do
  let destination ← newDestination module owner ty .value origin none (literalCount expression)
  construct destination
  let destination ← completedDestination destination
  publishCarriers origin [.completed destination]
  pure (.completed destination)

private def getImplementation (config : EvalConfig) (context : ContextId) : EvalM (Core.ImplId × Impl) := do
  let some context := config.module.contexts[context]? | fault .unbound
  let some implementation := config.module.impls[context.impl]? | fault .unbound
  pure (context.impl, implementation)

private def enclosingActivation (environment : RuntimeActivation) : EvalM RuntimeActivation := do
  let some activation := (← EvalM.get).activations.find? (fun activation => activation.act == environment.act) | fault .flow
  pure { activation with scopes := environment.scopes }

private def targetActivation (config : EvalConfig) (target : Nat) : EvalM RuntimeActivation := do
  let some target := config.module.targets[target]? | fault .unbound
  let some activation := selectTarget? target (← EvalM.get).activations | fault .flow
  pure activation

private def exitChannels (activation : RuntimeActivation) (operands : List Expr) (origin : OriginId) : EvalM (List Channel) := do
  if operands.length != activation.channels.length then fault .arity
  (activation.channels.zip operands).mapM fun (channel, operand) => do
    match channel with
    | .register ty => pure (.register ty)
    | .construct id =>
        let destination ← getDestination id
        let direct := match destination.progress with
          | .open 0 => true
          | _ => false
        let alias ← match operand with
          | .resultLocal localVar _ => do
              let root ← rootOf activation localVar
              match (← EvalM.get).objects.lookup root with
              | some (.stored stored) => pure (stored.destination == some id)
              | _ => pure false
          | _ => pure false
        if direct || alias then pure channel
        else pure (.construct (← liftConstruction origin (openExitReplacement id)))

private def finishChannels (config : EvalConfig) (activation : RuntimeActivation)
    (carriers : List Carrier) (origin : OriginId) : EvalM Unit := do
  landCarriers origin carriers
  let some implementation := config.module.impls[activation.implementation]? | fault .unbound
  if carriers.length != implementation.results.size then fault .arity
  for (carrier, result) in carriers.zip implementation.results.toList do
    match carrier with
    | .register _ => pure ()
    | .completed id =>
        let destination ← getDestination id
        let receivingPacked := match destination.capability.layout with | .varr _ => true | _ => false
        if destination.layout == .packed && destination.capability.request == .value && !receivingPacked then
          liftConstruction origin (removeConstructionHeader id)
          liftConstruction origin (restoreReceivingLayout id (← receivingLayout config.module destination.capability.layout))
        liftConstruction origin (adaptDestinationType id result.ty)

mutual
private def evalValue : Nat → EvalConfig → RuntimeActivation → Expr → EvalM Value
  | 0, _, _, _ => timeout
  | fuel + 1, config, environment, expression => do
      match expression with
      | .lit ty value => pure (.int ty value)
      | .bool value => pure (.bool value)
      | .read place => readLoc fuel config.module (← evalPlace fuel config environment place)
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
          let channels ← channelsFor config.module environment.act implementation.results.toList origin
          let carriers ← invokeCall fuel config environment context arguments channels origin
          publishCarriers origin carriers
          carrierValue (← singleCarrier carriers)
      | .push owner operand origin =>
          pushValue fuel config environment owner operand (origin.getD 0)
      | .pop owner origin =>
          let location ← evalPlace fuel config environment owner
          let value ← readLoc fuel config.module location
          let (count, _) ← arrayLength value
          if count == 0 then abortAt .popEmpty origin
          let result ← readLoc fuel config.module ⟨location.root, location.path ++ [count - 1]⟩
          truncateOwner fuel config location (count - 1) origin
          pure result
      | .ifE condition yes no =>
          let flow ← if (← expectBool (← evalValue fuel config environment condition)) then
            execBlock fuel config environment [] [] yes
          else execBlock fuel config environment [] [] no
          match flow with
          | .normal value => pure value
          | _ => fault .flow
      | .blockE block =>
          withBreakTarget environment.act .block [.register .unit]
            (do
              match (← execBlock fuel config environment [] [] block) with
              | .normal value => pure value
              | _ => fault .flow)
            (fun kind => do
              match kind with
              | .breakValue carriers => carrierValue (← singleCarrier carriers)
              | .continueLoop => fault .flow)
      | .arrLit ty operands =>
          if ty.nonfixed then
            carrierValue (← constructLocal config.module environment.act ty (expressionOrigin expression) expression
              (fun destination => buildExpr fuel config environment destination expression))
          else pure (.fixed (← operands.mapM (evalValue fuel config environment)).toArray)
      | .fill ty operand =>
          let .arr _ count := ty | fault .shape
          if ty.nonfixed then
            carrierValue (← constructLocal config.module environment.act ty (expressionOrigin expression) expression
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
            bindRoot root (.fixed (bytes.map (fun byte => Value.int .u8 byte.toNat)).toArray)
            pure (.slice ⟨root, []⟩ 0 bytes.length)
          else if ty.nonfixed then
            carrierValue (← constructLocal config.module environment.act ty origin expression
              (fun destination => buildExpr fuel config environment destination expression))
          else pure (.fixed (bytes.map (fun byte => Value.int .u8 byte.toNat)).toArray)
      | .str ty _ origin =>
          let carrier ← constructLocal config.module environment.act ty origin expression
            (fun destination => buildExpr fuel config environment destination expression)
          let value ← carrierValue carrier
          if ty.nonfixed then pure value
          else
            let .stored stored := value | fault .shape
            let storage ← getStorage stored.storage
            liftExcept (fixedValue fuel config.module ty storage.bytes stored.start)
      | .copy ty source origin =>
          if ty.nonfixed then
            carrierValue (← constructLocal config.module environment.act ty origin expression
              (fun destination => buildExpr fuel config environment destination expression))
          else
            let value ← readLoc fuel config.module (← evalPlace fuel config environment source)
            match ty, value with
            | .arr _ count, .stored stored =>
                let (_, run) ← sampledStored stored
                if count != run.count then fault .shape
                pure (.fixed (← (List.range count).mapM (readStoredElement fuel config.module stored)).toArray)
            | _, value => pure value
      | .resultLocal localVar _ => readLoc fuel config.module ⟨← rootOf environment localVar, []⟩
      | .values operands =>
          match operands with
          | [] => pure .unit
          | [operand] => evalValue fuel config environment operand
          | _ => fault .arity

private def evalBound : Nat → EvalConfig → RuntimeActivation → Nat → Int → Bound → EvalM Int
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, count, defaultValue, bound => do
      match bound with
      | .omitted => pure defaultValue
      | .expr operand => pure (← expectInt (← evalValue fuel config environment operand)).2
      | .fromEnd operand => pure ((count : Int) - (← expectInt (← evalValue fuel config environment operand)).2)

private def evalPlace : Nat → EvalConfig → RuntimeActivation → Place → EvalM Loc
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

private def evalView : Nat → EvalConfig → RuntimeActivation → View → EvalM RuntimeView
  | 0, _, _, _ => timeout
  | fuel + 1, config, environment, view => do
      match view with
      | .of place =>
          let location ← evalPlace fuel config environment place
          let (count, dynamic) ← arrayLength (← readLoc fuel config.module location)
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

private def evalProduce : Nat → EvalConfig → RuntimeActivation → List Channel → Expr → EvalM (List Carrier)
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, channels, expression => do
      match expression with
      | .values operands => evalOperands fuel config environment channels operands
      | .call context arguments origin => invokeCall fuel config environment context arguments channels origin
      | .ifE condition yes no =>
          let block := if (← expectBool (← evalValue fuel config environment condition)) then yes else no
          let (flow, carriers) ← execResultBlock fuel config environment channels block
          match flow with
          | .normal _ => pure carriers
          | _ => fault .flow
      | .blockE block =>
          withBreakTarget environment.act .block channels
            (do
              let (flow, carriers) ← execResultBlock fuel config environment channels block
              match flow with
              | .normal _ => pure carriers
              | _ => fault .flow)
            (fun kind => do
              match kind with
              | .breakValue carriers => landCarriers 0 carriers; pure carriers
              | .continueLoop => fault .flow)
      | _ =>
          match channels with
          | [] =>
              let _ ← evalValue fuel config environment expression
              pure []
          | [.register _] => pure [.register (← evalValue fuel config environment expression)]
          | [.construct destination] =>
              buildExpr fuel config environment destination expression
              pure [.completed (← completedDestination destination)]
          | _ => fault .arity

private def evalOperands : Nat → EvalConfig → RuntimeActivation → List Channel → List Expr → EvalM (List Carrier)
  | 0, _, _, _, _ => timeout
  | _ + 1, _, _, [], [] => pure []
  | fuel + 1, config, environment, channel :: channels, operand :: operands => do
      let carrier ← singleCarrier (← evalProduce fuel config environment [channel] operand)
      pure (carrier :: (← evalOperands fuel config environment channels operands))
  | _ + 1, _, _, _, _ => fault .arity

private def buildExpr : Nat → EvalConfig → RuntimeActivation → DestinationId → Expr → EvalM Unit
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, destination, expression =>
      protectDestination (expressionOrigin expression) destination do
        match expression with
        | .call context arguments origin =>
            let carriers ← invokeCall fuel config environment context arguments [.construct destination] origin
            let .completed actual ← singleCarrier carriers | fault .shape
            let original ← getDestination destination
            let actual ← getDestination actual
            if actual.storage != original.storage then fault .flow
        | .ifE condition yes no =>
            let block := if (← expectBool (← evalValue fuel config environment condition)) then yes else no
            let (flow, _) ← execResultBlock fuel config environment [.construct destination] block
            match flow with
            | .normal _ => pure ()
            | _ => fault .flow
        | .blockE block =>
            withBreakTarget environment.act .block [.construct destination]
              (do
                let (flow, _) ← execResultBlock fuel config environment [.construct destination] block
                match flow with
                | .normal _ => pure ()
                | _ => fault .flow)
              (fun kind => do
                match kind with
                | .breakValue carriers => landCarriers 0 carriers
                | .continueLoop => fault .flow)
        | .values [operand] => buildExpr fuel config environment destination operand
        | .arrLit _ operands =>
            let pending ← getDestination destination
            let some element := elementType pending.capability.logicalType | fault .shape
            for operand in operands do
              buildElement fuel config environment destination element operand
            liftConstruction (expressionOrigin expression) (finishDestination destination)
        | .fill ty operand =>
            let .arr element count := ty | fault .shape
            if element.nonfixed then
              let source ← newDestination config.module environment.act element .value (expressionOrigin expression)
              buildExpr fuel config environment source operand
              for _ in [0:count] do
                repeatElement fuel config destination element source (expressionOrigin expression)
            else
              let value ← evalValue fuel config environment operand
              let bytes ← liftExcept (fixedBytes fuel config.module element value)
              for _ in [0:count] do liftConstruction (expressionOrigin expression) (writeElement destination bytes)
            liftConstruction (expressionOrigin expression) (finishDestination destination)
        | .bytes _ bytes origin =>
            for byte in bytes do liftConstruction origin (writeElement destination ⟨#[byte]⟩)
            liftConstruction origin (finishDestination destination)
        | .str _ arguments origin =>
            for argument in arguments do
              let bytes ← evalPrintArg fuel config environment argument
              for byte in bytes.data do liftConstruction origin (writeElement destination ⟨#[byte]⟩)
            liftConstruction origin (finishDestination destination)
        | .copy _ source origin =>
            copyValue fuel config destination (← readLoc fuel config.module (← evalPlace fuel config environment source)) origin
        | .resultLocal localVar origin =>
            let value ← readLoc fuel config.module ⟨← rootOf environment localVar, []⟩
            match value with
            | .stored stored =>
                if stored.destination == some destination then
                  let pending ← getDestination destination
                  match pending.progress with
                  | .built _ => pure ()
                  | .open _ => liftConstruction origin (finishDestination destination)
                  | _ => fault .flow
                else copyValue fuel config destination value origin
            | _ => fault .shape
        | _ =>
            let value ← evalValue fuel config environment expression
            copyValue fuel config destination value (expressionOrigin expression)

private def buildElement : Nat → EvalConfig → RuntimeActivation → DestinationId → Ty → Expr → EvalM Unit
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, parent, element, operand => do
      if element.nonfixed then
        let child ← liftConstruction (expressionOrigin operand) (openChild parent element (← receivingLayout config.module element))
        buildExpr fuel config environment child operand
        liftConstruction (expressionOrigin operand) (attachChild parent (← completedDestination child))
      else
        let value ← evalValue fuel config environment operand
        let bytes ← liftExcept (fixedBytes fuel config.module element value)
        liftConstruction (expressionOrigin operand) (writeElement parent bytes)

private def evalArguments : Nat → EvalConfig → RuntimeActivation → Array LocalVar → List Param → List Arg → EvalM (List Value)
  | 0, _, _, _, _, _ => timeout
  | _ + 1, _, _, _, [], [] => pure []
  | fuel + 1, config, environment, parameterVars, parameter :: parameters, argument :: arguments => do
      let value ← match argument with
        | .byRef _ place => do pure (.ref (← evalPlace fuel config environment place))
        | .byVal operand => evalValue fuel config environment operand
        | .construct operand =>
            let some localVar := parameterVars[parameter.var]? | fault .unbound
            carrierValue (← constructLocal config.module environment.act localVar.ty (expressionOrigin operand) operand
              (fun destination => buildExpr fuel config environment destination operand))
      pure (value :: (← evalArguments fuel config environment parameterVars parameters arguments))
  | _ + 1, _, _, _, _, _ => fault .arity

private def invokeCall : Nat → EvalConfig → RuntimeActivation → ContextId → List Arg → List Channel → OriginId → EvalM (List Carrier)
  | 0, _, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, context, arguments, channels, origin => do
      let (id, implementation) ← getImplementation config context
      if channels.length != implementation.results.size then fault .arity
      for (channel, result) in channels.zip implementation.results.toList do
        match channel with
        | .register _ => pure ()
        | .construct destination => liftConstruction origin (adaptDestinationType destination result.ty)
      let values ← evalArguments fuel config environment implementation.vars implementation.params.toList arguments
      let state ← EvalM.get
      if state.activations.length ≥ Core.maxCallDepth then timeout
      let act ← freshAct
      let activation : RuntimeActivation := ⟨id, act, implementation.vars, [], channels⟩
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
      enterActivation fuel config activation pre implementation.body origin

private def enterActivation : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → Block → OriginId → EvalM (List Carrier)
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, activation, pre, body, origin => fun state =>
      let action := do
        let (flow, carriers) ← execResultBlockWith fuel config activation pre activation.channels body
        match flow with
        | .normal _ => pure carriers
        | _ => fault .flow
      let finish := fun carriers state' =>
        let state' := { state' with activations := state'.activations.filter (fun current => current.act != activation.act) }
        match finishChannels config activation carriers origin state' with
        | .ok () state'' => ExecutionStep.ok carriers state''
        | .stop reason state'' => ExecutionStep.stop reason state''
        | .escape target escaped state'' => ExecutionStep.escape target escaped state''
        | .jump target kind state'' => ExecutionStep.jump target kind state''
      match action state with
      | .ok carriers state' => finish carriers state'
      | .escape target carriers state' =>
          if target == activation.act then finish carriers state'
          else .escape target carriers { state' with activations := state'.activations.filter (fun current => current.act != activation.act) }
      | .stop reason state' => .stop reason state'
      | .jump _ _ state' => .stop (.fault .flow) state'

private def execResultBlock : Nat → EvalConfig → RuntimeActivation → List Channel → Block → EvalM (Flow × List Carrier)
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, channels, block =>
      execResultBlockWith fuel config environment [] channels block

private def execResultBlockWith : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → List Channel → Block → EvalM (Flow × List Carrier)
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, pre, channels, .mk scope statements value => do
      let scopeInst ← freshScope
      let environment' := { environment with scopes := (scope, scopeInst) :: environment.scopes }
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map (fun current => if current.act == environment.act then { current with scopes := environment'.scopes } else current) }
      withScope environment scope scopeInst do
        bindAll environment.act scopeInst pre
        let flow ← execStmts fuel config environment' statements
        match flow, value with
        | .normal _, some expression => pure (.normal .unit, ← evalProduce fuel config environment' channels expression)
        | .normal _, none =>
            if channels.isEmpty then pure (flow, [])
            else if channels.length == 1 then
              match channels with
              | [.register .unit] => pure (flow, [.register .unit])
              | _ => fault .arity
            else fault .arity
        | flow, _ => pure (flow, [])

private def execBlock : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → List Channel → Block → EvalM Flow
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

private def execStmts : Nat → EvalConfig → RuntimeActivation → List Stmt → EvalM Flow
  | 0, _, _, _ => timeout
  | _ + 1, _, _, [] => pure (.normal .unit)
  | fuel + 1, config, environment, statement :: statements => do
      match (← execStmt fuel config environment statement) with
      | .normal _ => execStmts fuel config environment statements
      | flow => pure flow

private def execStmt : Nat → EvalConfig → RuntimeActivation → Stmt → EvalM Flow
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
                    | some (.construct destination) => do
                        let destination ← getDestination destination
                        pure (if destination.capability.request == .value then some (result, index) else none)
                    | _ => fault .flow
                | none => pure none
              let object ← if named.isSome then do pure (some (← liftConstruction origin reserveStorage)) else pure none
              let destination ← match named with
                | some (_, index) =>
                    match environment.channels[index]? with
                    | some (.construct destination) => pure destination
                    | _ => fault .flow
                | none => newDestination config.module environment.act descriptor.ty .value origin none (literalCount expression)
              if named.isSome then liftConstruction origin (prepareNamedBinding destination descriptor.ty)
              buildExpr fuel config environment destination expression
              let destination ← completedDestination destination
              if named.isNone then publishCarriers origin [.completed destination]
              let stored ← storedDestination destination
              pure (.stored { stored with ty := descriptor.ty, object := object })
            else evalValue fuel config environment expression
          bindRoot root value
          pure (.normal .unit)
      | .assign place expression _ =>
          let location ← evalPlace fuel config environment place
          let value ← evalValue fuel config environment expression
          writeLoc fuel config.module location value
          pure (.normal .unit)
      | .assignOp operation place expression origin =>
          let location ← evalPlace fuel config environment place
          let (ty, oldValue) ← expectInt (← readLoc fuel config.module location)
          let (otherTy, value) ← expectInt (← evalValue fuel config environment expression)
          sameIntType ty otherTy
          match Core.evalBin config.profile operation ty oldValue value with
          | .ok result => writeLoc fuel config.module location (.int ty result); pure (.normal .unit)
          | .error reason => abortAt (AbortKind.ofNum reason) origin
      | .rebind localVar expression _ =>
          let value ← evalValue fuel config environment expression
          writeLoc fuel config.module ⟨← rootOf environment localVar, []⟩ value
          pure (.normal .unit)
      | .expr expression _ =>
          let _ ← evalValue fuel config environment expression
          pure (.normal .unit)
      | .append owner source origin =>
          let location ← evalPlace fuel config environment owner
          let view ← evalView fuel config environment source
          appendRun fuel config location view origin
          pure (.normal .unit)
      | .popN owner expression origin =>
          let location ← evalPlace fuel config environment owner
          let (_, count) ← expectInt (← evalValue fuel config environment expression)
          let (length, _) ← arrayLength (← readLoc fuel config.module location)
          if count < 0 || count > (length : Int) then abortAt .popNRange origin
          truncateOwner fuel config location (length - count.toNat) origin
          pure (.normal .unit)
      | .resize owner expression fill origin =>
          let location ← evalPlace fuel config environment owner
          let (_, size) ← expectInt (← evalValue fuel config environment expression)
          let value ← match fill with
            | none => pure none
            | some expression => do pure (some (← evalValue fuel config environment expression))
          let (length, _) ← arrayLength (← readLoc fuel config.module location)
          let size := Core.wrap .i64 size
          if size < 0 then abortAt .resizeNegative origin
          if size.toNat ≤ length then truncateOwner fuel config location size.toNat origin
          else
            match value with
            | none => abortAt .resizeFill origin
            | some value => appendFixedValues fuel config location (List.replicate (size.toNat - length) value) origin
          pure (.normal .unit)
      | .clear owner origin =>
          truncateOwner fuel config (← evalPlace fuel config environment owner) 0 origin
          pure (.normal .unit)
      | .assignWhole owner expression origin =>
          let location ← evalPlace fuel config environment owner
          truncateOwner fuel config location 0 origin
          let .stored stored ← readLoc fuel config.module location | fault .shape
          let destination ← ownerDestination config.module stored .value (literalCount expression) origin
          buildExpr fuel config environment destination expression
          publishOwner fuel config location stored (← completedDestination destination) origin
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
          let channels ← localVars.mapM fun localVar => do
            let some descriptor := environment.vars[localVar]? | fault .unbound
            if descriptor.ty.nonfixed then
              pure (Channel.construct (← newDestination config.module environment.act descriptor.ty .value origin))
            else pure (.register descriptor.ty)
          let carriers ← evalProduce fuel config environment channels producer
          if carriers.length != localVars.length then fault .arity
          publishCarriers origin carriers
          for (localVar, carrier) in localVars.zip carriers do
            bindRoot (← rootOf environment localVar) (← carrierValue carrier)
          pure (.normal .unit)
      | .appendValue owner producer origin =>
          let location ← evalPlace fuel config environment owner
          let .fixed values ← evalValue fuel config environment producer | fault .shape
          appendFixedValues fuel config location values.toList origin
          pure (.normal .unit)
      | .appendConstruct owner producer origin =>
          let location ← evalPlace fuel config environment owner
          let .stored stored ← readLoc fuel config.module location | fault .shape
          let destination ← ownerDestination config.module stored .elementRun (literalCount producer) origin
          buildExpr fuel config environment destination producer
          publishOwner fuel config location stored (← completedDestination destination) origin
          pure (.normal .unit)
      | .retValues operands origin =>
          let activation ← enclosingActivation environment
          let channels ← exitChannels activation operands origin
          let carriers ← evalOperands fuel config environment channels operands
          returned activation.act carriers
      | .retForward producer origin =>
          let activation ← enclosingActivation environment
          let channels ← exitChannels activation (List.replicate activation.channels.length producer) origin
          returned activation.act (← evalProduce fuel config environment channels producer)
      | .returnFrom target operands origin =>
          let activation ← targetActivation config target
          let channels ← exitChannels activation operands origin
          returned activation.act (← evalOperands fuel config environment channels operands)
      | .returnFromForward target producer origin =>
          let activation ← targetActivation config target
          let channels ← exitChannels activation (List.replicate activation.channels.length producer) origin
          returned activation.act (← evalProduce fuel config environment channels producer)
      | .breakValue expression origin =>
          let target ← currentBreak environment.act
          let activation := { environment with channels := target.channels }
          let channels ← exitChannels activation [expression] origin
          jump target.id (.breakValue (← evalProduce fuel config environment channels expression))
      | .ret expression origin =>
          let activation ← enclosingActivation environment
          match expression with
          | some expression =>
              let channels ← exitChannels activation [expression] origin
              returned activation.act (← evalProduce fuel config environment channels expression)
          | none =>
              if activation.channels.isEmpty then returned activation.act []
              else if activation.channels.length == 1 then returned activation.act [.register .unit]
              else fault .arity
      | .brk _ => jump (← currentBreak environment.act).id (.breakValue [])
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

private def evalPrintArg : Nat → EvalConfig → RuntimeActivation → PrintArg → EvalM ByteArray
  | 0, _, _, _ => timeout
  | fuel + 1, config, environment, argument => do
      match argument with
      | .text text => pure text.toUTF8
      | .expr expression => renderAny fuel config .topLevel (← evalValue fuel config environment expression)
      | .view view => renderView fuel config .topLevel (← evalView fuel config environment view)

private def execWhile : Nat → EvalConfig → RuntimeActivation → Expr → Block → EvalM Flow
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, condition, body => do
      if (← expectBool (← evalValue fuel config environment condition)) then
        match (← loopBody fuel config environment [] body) with
        | .normal _ | .continuing => execWhile fuel config environment condition body
        | .breaking value => pure (.normal (value.getD .unit))
      else pure (.normal .unit)

private def execRange : Nat → EvalConfig → RuntimeActivation → VarId → IntTy → Int → Int → Block → EvalM Flow
  | 0, _, _, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, localVar, ty, first, last, body => do
      if first < last then
        match (← loopBody fuel config environment [(localVar, .int ty first)] body) with
        | .normal _ | .continuing => execRange fuel config environment localVar ty (first + 1) last body
        | .breaking value => pure (.normal (value.getD .unit))
      else pure (.normal .unit)

private def execEach : Nat → EvalConfig → RuntimeActivation → VarId → Option VarId → Bool → Block → RuntimeView → Nat → EvalM Flow
  | 0, _, _, _, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, localVar, index, byRef, body, view, current => do
      let count ← if view.dynamic then do pure (← arrayLength (← readLoc fuel config.module view.location)).1 else pure view.count
      if current < count then
        let location : Loc := ⟨view.location.root, view.location.path ++ [view.start + current]⟩
        let value ← if byRef then pure (.ref location) else readLoc fuel config.module location
        let pre := (localVar, value) :: (index.toList.map fun index => (index, Value.int .i64 current))
        match (← loopBody fuel config environment pre body) with
        | .normal _ | .continuing => execEach fuel config environment localVar index byRef body view (current + 1)
        | .breaking value => pure (.normal (value.getD .unit))
      else pure (.normal .unit)

private def loopBody : Nat → EvalConfig → RuntimeActivation → List (VarId × Value) → Block → EvalM Flow
  | 0, _, _, _, _ => timeout
  | fuel + 1, config, environment, pre, body =>
      withBreakTarget environment.act .loop []
        (execBlock fuel config environment pre [] body)
        (fun kind => do
          match kind with
          | .continueLoop => pure .continuing
          | .breakValue [] => pure (.breaking none)
          | .breakValue carriers => pure (.breaking (some (← carrierValue (← singleCarrier carriers)))))

private def pushValue : Nat → EvalConfig → RuntimeActivation → Place → Expr → OriginId → EvalM Value
  | 0, _, _, _, _, _ => timeout
  | fuel + 1, config, environment, owner, expression, origin => do
      let location ← evalPlace fuel config environment owner
      let .stored stored ← readLoc fuel config.module location | fault .shape
      let (_, run) ← sampledStored stored
      let result : Loc := ⟨location.root, location.path ++ [run.count]⟩
      if run.element.nonfixed then
        let destination ← ownerDestination config.module stored .elementRun (some 1) origin
        buildElement fuel config environment destination run.element expression
        liftConstruction origin (finishDestination destination)
        publishOwner fuel config location stored (← completedDestination destination) origin
      else
        let value ← evalValue fuel config environment expression
        appendFixedValues fuel config location [value] origin
      pure (.ref result)
end

private def initGlobals (fuel : Nat) (config : EvalConfig) : List GlobalId → EvalM Unit
  | [] => pure ()
  | global :: globals => do
      let some descriptor := config.module.globals[global]? | fault .unbound
      let act ← freshAct
      let environment : RuntimeActivation := ⟨0, act, #[], [], []⟩
      let value ← if descriptor.ty.nonfixed then
        carrierValue (← constructLocal config.module act descriptor.ty descriptor.org descriptor.init
          (fun destination => buildExpr fuel config environment destination descriptor.init))
      else evalValue fuel config environment descriptor.init
      bindRoot (.global global) value
      initGlobals fuel config globals

private def runModule (fuel : Nat) (config : EvalConfig) : EvalM Unit := do
  initGlobals fuel config (List.range config.module.globals.size)
  let (_, implementation) ← getImplementation config config.module.entry
  let channels ← channelsFor config.module 0 implementation.results.toList 0
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
