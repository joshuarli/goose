import Goose.Proofs.ConstructionExecutionProtocolRuntime
import Lean.Elab.Tactic.Basic

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

structure EvaluationPreservesConstructionInvariant (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, (PreservesConstructionInvariant predicate) (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, (PreservesConstructionInvariant predicate) (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, (PreservesConstructionInvariant predicate) (evalPlace fuel config environment operand)
  view : ∀ environment operand, (PreservesConstructionInvariant predicate) (evalView fuel config environment operand)
  produce : ∀ environment channels operand, (PreservesConstructionInvariant predicate) (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, (PreservesConstructionInvariant predicate) (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, (PreservesConstructionInvariant predicate) (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, (PreservesConstructionInvariant predicate) (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, (PreservesConstructionInvariant predicate) (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, (PreservesConstructionInvariant predicate) (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, (PreservesConstructionInvariant predicate) (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, (PreservesConstructionInvariant predicate) (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, (PreservesConstructionInvariant predicate) (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, (PreservesConstructionInvariant predicate) (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, (PreservesConstructionInvariant predicate) (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, (PreservesConstructionInvariant predicate) (execStmts fuel config environment statements)
  statement : ∀ environment statement, (PreservesConstructionInvariant predicate) (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, (PreservesConstructionInvariant predicate) (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, (PreservesConstructionInvariant predicate) (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, (PreservesConstructionInvariant predicate) (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, (PreservesConstructionInvariant predicate) (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, (PreservesConstructionInvariant predicate) (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, (PreservesConstructionInvariant predicate) (pushValue fuel config environment owner expression origin)

theorem evaluationPreservesConstructionInvariant_zero (config : EvalConfig) : (EvaluationPreservesConstructionInvariant (predicate := predicate)) 0 config := by
  constructor
  all_goals intros
  all_goals simp [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
    buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
    execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
    execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
    PreservesConstructionInvariant, Goose.Proofs.Exit.stepState, bind]

theorem evalBound_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) :
    (PreservesConstructionInvariant predicate) (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases operand with
  | omitted => simpa only [evalBound] using preservesConstructionInvariant_pure defaultValue
  | expr expression | fromEnd expression =>
      simp only [evalBound]
      apply preservesConstructionInvariant_bind
      · exact previous.value _ _
      · intro value
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_expectInt value)
        · intro pair; exact preservesConstructionInvariant_pure _

theorem evalPlace_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation) (operand : Place) :
    (PreservesConstructionInvariant predicate) (evalPlace (fuel + 1) config environment operand) := by
  cases operand with
  | var localVar =>
      simp only [evalPlace]
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_rootOf _ _)
      · intro _; exact preservesConstructionInvariant_pure _
  | global global => simpa only [evalPlace] using preservesConstructionInvariant_pure (Goose.Core.Loc.mk (.global global) [])
  | deref expression =>
      simp only [evalPlace]
      apply preservesConstructionInvariant_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_preservesConstructionInvariant _ (stateQuery_expectRef value)
  | elem view expression origin =>
      simp only [evalPlace]
      apply preservesConstructionInvariant_bind
      · exact previous.view _ _
      · intro view
        apply preservesConstructionInvariant_bind
        · exact previous.value _ _
        · intro value
          apply preservesConstructionInvariant_bind
          · exact stateQuery_preservesConstructionInvariant _ (stateQuery_expectInt value)
          · intro pair
            rcases pair with ⟨ty, index⟩
            split
            · exact preservesConstructionInvariant_pure _
            · exact preservesConstructionInvariant_stop _
  | field place index =>
      simp only [evalPlace]
      apply preservesConstructionInvariant_bind
      · exact previous.place _ _
      · intro _; exact preservesConstructionInvariant_pure _

theorem evalView_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation) (operand : View) :
    (PreservesConstructionInvariant predicate) (evalView (fuel + 1) config environment operand) := by
  cases operand with
  | of place =>
      simp only [evalView]
      apply preservesConstructionInvariant_bind
      · exact previous.place _ _
      · intro location
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_readLoc _ _ _)
        · intro value
          apply preservesConstructionInvariant_bind
          · exact stateQuery_preservesConstructionInvariant _ (stateQuery_arrayLength value)
          · intro pair
            rcases pair with ⟨count, dynamic⟩
            exact preservesConstructionInvariant_pure _
  | val expression =>
      simp only [evalView]
      apply preservesConstructionInvariant_bind
      · exact previous.value _ _
      · intro value
        cases value <;> first
          | exact preservesConstructionInvariant_pure _
          | (apply preservesConstructionInvariant_bind
             · exact stateQuery_preservesConstructionInvariant _ (stateQuery_arrayLength _)
             · intro pair
               rcases pair with ⟨count, dynamic⟩
               apply preservesConstructionInvariant_bind
               · exact preservesConstructionInvariant_freshScope
               · intro index
                 apply preservesConstructionInvariant_bind
                 · exact preservesConstructionInvariant_bindRoot _ _
                 · intro _; exact preservesConstructionInvariant_pure _)

theorem evalOperands_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    (PreservesConstructionInvariant predicate) (evalOperands (fuel + 1) config environment channels operands) := by
  cases channels <;> cases operands <;> simp only [evalOperands]
  all_goals first
    | exact preservesConstructionInvariant_pure _
    | exact preservesConstructionInvariant_stop _
    | (apply preservesConstructionInvariant_bind
       · exact previous.produce _ _ _
       · intro carriers
         apply preservesConstructionInvariant_bind
         · exact stateQuery_preservesConstructionInvariant _ (stateQuery_singleCarrier carriers)
         · intro carrier
           apply preservesConstructionInvariant_bind
           · exact previous.operands _ _ _
           · intro _; exact preservesConstructionInvariant_pure _)

theorem evalPrintArg_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation) (argument : PrintArg) :
    (PreservesConstructionInvariant predicate) (evalPrintArg (fuel + 1) config environment argument) := by
  cases argument with
  | text text => simpa only [evalPrintArg] using preservesConstructionInvariant_pure text.toUTF8
  | expr expression =>
      simp only [evalPrintArg]
      apply preservesConstructionInvariant_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_preservesConstructionInvariant _ ((rendering_stateQueries fuel config.layout).1 _ _)
  | view view =>
      simp only [evalPrintArg]
      apply preservesConstructionInvariant_bind
      · exact previous.view _ _
      · intro view; exact stateQuery_preservesConstructionInvariant _ ((rendering_stateQueries fuel config.layout).2.2.2 _ _)

theorem evalArguments_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) :
    (PreservesConstructionInvariant predicate) (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases parameters with
  | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact preservesConstructionInvariant_pure _
      · exact preservesConstructionInvariant_stop _
  | cons parameter parameters =>
      cases arguments with
      | nil => simpa only [evalArguments, fault] using preservesConstructionInvariant_stop (Goose.Core.Stop.fault .arity)
      | cons argument arguments =>
          have finish (value : Value) : (PreservesConstructionInvariant predicate) (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
            apply preservesConstructionInvariant_bind
            · exact previous.arguments _ _ _ _
            · intro _; exact preservesConstructionInvariant_pure _
          cases argument with
          | byVal expression =>
              simp only [evalArguments]
              apply preservesConstructionInvariant_bind
              · exact previous.value _ _
              · intro value; exact finish value
          | byRef mutability place =>
              simp only [evalArguments]
              apply preservesConstructionInvariant_bind
              · exact previous.place _ _
              · intro location
                apply preservesConstructionInvariant_bind
                · exact preservesConstructionInvariant_pure _
                · intro value; exact finish value
          | construct expression =>
              simp only [evalArguments]
              split
              · apply preservesConstructionInvariant_bind
                · apply preservesConstructionInvariant_materializeProducer
                  exact previous.value _ _
                · intro materialized
                  have finishCarrier (carrier : Carrier) : PreservesConstructionInvariant predicate (do
                      let value ← carrierValue carrier
                      let values ← evalArguments fuel config environment vars parameters arguments
                      pure (value :: values)) := by
                    apply preservesConstructionInvariant_bind
                    · exact stateQuery_preservesConstructionInvariant _ (stateQuery_carrierValue carrier)
                    · intro value; exact finish value
                  cases materialized with
                  | none =>
                      apply preservesConstructionInvariant_bind
                      · apply preservesConstructionInvariant_constructLocal
                        intro destination; exact previous.build _ _ _
                      · intro carrier; exact finishCarrier carrier
                  | some source =>
                      apply preservesConstructionInvariant_bind
                      · exact preservesConstructionInvariant_materializedDestination _ _ _ _ _ _ _
                      · intro destination
                        apply preservesConstructionInvariant_bind
                        · exact preservesConstructionInvariant_publishCarriers _ _
                        · intro ignored
                          apply preservesConstructionInvariant_bind
                          · exact preservesConstructionInvariant_pure _
                          · intro carrier; exact finishCarrier carrier
              · apply preservesConstructionInvariant_bind
                · exact preservesConstructionInvariant_stop _
                · intro value; exact finish value

theorem execStmts_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) : (PreservesConstructionInvariant predicate) (execStmts (fuel + 1) config environment statements) := by
  cases statements with
  | nil => simpa only [execStmts] using preservesConstructionInvariant_pure (Flow.normal .unit)
  | cons statement statements =>
      simp only [execStmts]
      apply preservesConstructionInvariant_bind
      · exact previous.statement _ _
      · intro flow
        cases flow with
        | normal value => exact previous.statements _ _
        | breaking value | continuing => exact preservesConstructionInvariant_pure _

theorem execResultBlock_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    (PreservesConstructionInvariant predicate) (execResultBlock (fuel + 1) config environment channels body) := by
  simpa only [execResultBlock] using previous.resultBlockWith environment [] channels body

theorem enterActivation_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  split
  · apply preservesConstructionInvariant_finishActivation
    exact previous.activationBody _ _ _
  · exact preservesConstructionInvariant_stop _

theorem preservesConstructionInvariant_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (action : EvalM α) (preserved : (PreservesConstructionInvariant predicate) action) :
    (PreservesConstructionInvariant predicate) (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state valid
  simpa [EvalM.get, EvalM.set, bind, pure] using
    preserved { state with activations := state.activations.map change } valid

theorem preservesConstructionInvariant_fault (kind : Goose.Core.FaultKind) :
    (PreservesConstructionInvariant predicate) (fault (α := α) kind) := preservesConstructionInvariant_stop _

theorem preservesConstructionInvariant_timeout :
    (PreservesConstructionInvariant predicate) (timeout (α := α)) := preservesConstructionInvariant_stop _

theorem preservesConstructionInvariant_abortAt (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (abortAt (α := α) kind origin) := preservesConstructionInvariant_stop _

theorem preservesConstructionInvariant_fault_bind (kind : Goose.Core.FaultKind) (next : α → EvalM β) :
    (PreservesConstructionInvariant predicate) (fault kind >>= next) := fun _ valid => valid

theorem preservesConstructionInvariant_timeout_bind (next : α → EvalM β) :
    (PreservesConstructionInvariant predicate) (timeout >>= next) := fun _ valid => valid

theorem preservesConstructionInvariant_abortAt_bind (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId)
    (next : α → EvalM β) : (PreservesConstructionInvariant predicate) (abortAt kind origin >>= next) := fun _ valid => valid

elab "protocol_materialize" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesConstructionInvariant do
    throwError "expected construction invariant"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``materializeProducer do
    throwError "expected materializeProducer"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesConstructionInvariant_materializeProducer))

elab "protocol_materialized" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesConstructionInvariant do
    throwError "expected construction invariant"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``materializedDestination do
    throwError "expected materializedDestination"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesConstructionInvariant_materializedDestination _ _ _ _ _ _ _))

syntax "protocol_eval" ident : tactic
macro_rules
  | `(tactic| protocol_eval $previous:ident) => `(tactic|
  repeat' first
    | with_reducible assumption
    | with_reducible exact preservesConstructionInvariant_pure _
    | with_reducible exact preservesConstructionInvariant_stop _
    | with_reducible exact preservesConstructionInvariant_fault _
    | with_reducible exact preservesConstructionInvariant_timeout
    | with_reducible exact preservesConstructionInvariant_abortAt _ _
    | with_reducible exact preservesConstructionInvariant_fault_bind _ _
    | with_reducible exact preservesConstructionInvariant_timeout_bind _
    | with_reducible exact preservesConstructionInvariant_abortAt_bind _ _ _
    | with_reducible exact preservesConstructionInvariant_get
    | kernel_protocol
    | reservation_protocol
    | with_reducible exact preservesConstructionInvariant_bindRoot _ _
    | with_reducible exact preservesConstructionInvariant_bindStaticRoot _ _
    | with_reducible exact preservesConstructionInvariant_reserveRootObject _
    | with_reducible exact preservesConstructionInvariant_setObjectOrdinal _ _
    | with_reducible exact preservesConstructionInvariant_newDestination _ _ _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_channelsFor _ _ _ _
    | with_reducible exact preservesConstructionInvariant_freshAct
    | with_reducible exact preservesConstructionInvariant_freshScope
    | with_reducible exact preservesConstructionInvariant_returned _ _
    | with_reducible exact preservesConstructionInvariant_escaped _ _
    | with_reducible exact preservesConstructionInvariant_jump _ _
    | with_reducible exact preservesConstructionInvariant_emitStdout _
    | with_reducible exact preservesConstructionInvariant_publishCarriers _ _
    | protocol_materialized
    | with_reducible exact preservesConstructionInvariant_copyValue _ _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_deliverCarriers _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_ownerDestination _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_publishOwner _ _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_openElementReceiving _ _ _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_publishElementReceiving _ _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_repeatElement _ _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_truncateOwner _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_appendFixedValues _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_appendRun _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_writeLoc _ _ _ _
    | with_reducible exact preservesConstructionInvariant_landCarriers _ _
    | with_reducible exact preservesConstructionInvariant_landCarriersInto _ _ _
    | with_reducible exact preservesConstructionInvariant_bindAll _ _ _
    | with_reducible exact preservesConstructionInvariant_prepareNamedCarrierAt _ _ _ _
    | with_reducible exact preservesConstructionInvariant_selectCompletionChannel _ _ _
    | with_reducible exact preservesConstructionInvariant_exitSource _ _ _
    | with_reducible exact preservesConstructionInvariant_materializeOwnedCarriers _ _ _
    | with_reducible exact preservesConstructionInvariant_prepareNamedCarrier _ _ _
    | with_reducible exact preservesConstructionInvariant_materializeNamedCarriers _ _
    | with_reducible exact preservesConstructionInvariant_exitChannels _ _ _ _
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_rootOf _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_expectInt _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_expectBool _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_expectRef _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_sameIntType _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_comparable _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_readLoc _ _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_arrayLength _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_getStorage _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_sampledStored _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_readStoredElement _ _ _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_carrierValue _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_singleCarrier _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedDestination _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedReceivingDestination _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_receivingDestination _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedDestination _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_receivingLayout _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_getImplementation _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_enclosingActivation _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_targetActivation _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_currentBreak _ _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftExcept _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftLayout _)
    | with_reducible exact ($previous).value _ _
    | with_reducible exact ($previous).bound _ _ _ _
    | with_reducible exact ($previous).place _ _
    | with_reducible exact ($previous).view _ _
    | with_reducible exact ($previous).produce _ _ _
    | with_reducible exact ($previous).operands _ _ _
    | with_reducible exact ($previous).build _ _ _
    | with_reducible exact ($previous).element _ _ _ _
    | with_reducible exact ($previous).arguments _ _ _ _
    | with_reducible exact ($previous).call _ _ _ _ _
    | with_reducible exact ($previous).activation _ _ _ _
    | with_reducible exact ($previous).activationBody _ _ _
    | with_reducible exact ($previous).resultBlock _ _ _
    | with_reducible exact ($previous).resultBlockWith _ _ _ _
    | with_reducible exact ($previous).block _ _ _ _
    | with_reducible exact ($previous).statements _ _
    | with_reducible exact ($previous).statement _ _
    | with_reducible exact ($previous).printArgument _ _
    | with_reducible exact ($previous).whileLoop _ _ _
    | with_reducible exact ($previous).rangeLoop _ _ _ _ _ _
    | with_reducible exact ($previous).eachLoop _ _ _ _ _ _ _
    | with_reducible exact ($previous).loop _ _ _
    | with_reducible exact ($previous).push _ _ _ _
    | with_reducible apply preservesConstructionInvariant_allocateActivation
    | with_reducible apply preservesConstructionInvariant_mapActivations
    | with_reducible apply preservesConstructionInvariant_withOwnerExtension
    | with_reducible apply preservesConstructionInvariant_withCompletionChannels
    | with_reducible apply preservesConstructionInvariant_withExitChannels
    | with_reducible apply preservesConstructionInvariant_protectDestination
    | with_reducible apply preservesConstructionInvariant_withScope
    | with_reducible apply preservesConstructionInvariant_finishActivation
    | with_reducible apply preservesConstructionInvariant_withBreakTarget
    | protocol_materialize
    | with_reducible apply preservesConstructionInvariant_constructLocal
    | with_reducible apply preservesConstructionInvariant_bind
    | with_reducible apply preservesConstructionInvariant_listMapM
    | with_reducible apply preservesConstructionInvariant_listForIn
    | with_reducible apply preservesConstructionInvariant_arrayForIn
    | with_reducible apply preservesConstructionInvariant_rangeForIn
    | with_reducible split
    | with_reducible rfl
    | with_reducible intro)


end Goose.Proofs.ConstructionExecutionProtocol
