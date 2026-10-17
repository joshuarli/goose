import Goose.Proofs.ConstructionExecutionProtocolRuntime

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
include primitives

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

private theorem evalBound_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
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

private theorem evalPlace_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
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

private theorem evalView_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
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

private theorem evalOperands_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
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

private theorem evalPrintArg_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
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

private theorem evalArguments_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
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
                · apply preservesConstructionInvariant_constructLocal
                  intro destination; exact previous.build _ _ _
                · intro carrier
                  apply preservesConstructionInvariant_bind
                  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_carrierValue carrier)
                  · intro value; exact finish value
              · apply preservesConstructionInvariant_bind
                · exact preservesConstructionInvariant_stop _
                · intro value; exact finish value

private theorem execStmts_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
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

private theorem execResultBlock_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    (PreservesConstructionInvariant predicate) (execResultBlock (fuel + 1) config environment channels body) := by
  simpa only [execResultBlock] using previous.resultBlockWith environment [] channels body

private theorem execActivationBody_preservesConstructionInvariant (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (preserved : (PreservesConstructionInvariant predicate) (execResultBlockWith fuel config environment pre environment.channels body)) :
    (PreservesConstructionInvariant predicate) (execActivationBody fuel config environment pre body) := by
  unfold execActivationBody
  apply preservesConstructionInvariant_bind
  · exact preserved
  · intro result
    rcases result with ⟨flow, carriers⟩
    cases flow <;> first | exact preservesConstructionInvariant_pure _ | exact preservesConstructionInvariant_stop _

private theorem enterActivation_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  split
  · apply preservesConstructionInvariant_finishActivation
    exact previous.activationBody _ _ _
  · exact preservesConstructionInvariant_stop _

private theorem preservesConstructionInvariant_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (action : EvalM α) (preserved : (PreservesConstructionInvariant predicate) action) :
    (PreservesConstructionInvariant predicate) (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state valid
  simpa [EvalM.get, EvalM.set, bind, pure] using
    preserved { state with activations := state.activations.map change } valid

private theorem preservesConstructionInvariant_fault (kind : Goose.Core.FaultKind) :
    (PreservesConstructionInvariant predicate) (fault (α := α) kind) := preservesConstructionInvariant_stop _

private theorem preservesConstructionInvariant_timeout :
    (PreservesConstructionInvariant predicate) (timeout (α := α)) := preservesConstructionInvariant_stop _

private theorem preservesConstructionInvariant_abortAt (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (abortAt (α := α) kind origin) := preservesConstructionInvariant_stop _

private theorem preservesConstructionInvariant_fault_bind (kind : Goose.Core.FaultKind) (next : α → EvalM β) :
    (PreservesConstructionInvariant predicate) (fault kind >>= next) := fun _ valid => valid

private theorem preservesConstructionInvariant_timeout_bind (next : α → EvalM β) :
    (PreservesConstructionInvariant predicate) (timeout >>= next) := fun _ valid => valid

private theorem preservesConstructionInvariant_abortAt_bind (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId)
    (next : α → EvalM β) : (PreservesConstructionInvariant predicate) (abortAt kind origin >>= next) := fun _ valid => valid

local syntax "protocol_eval" ident : tactic
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
    | with_reducible exact preservesConstructionInvariant_bindAll _ _ _
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
    | with_reducible apply preservesConstructionInvariant_protectDestination
    | with_reducible apply preservesConstructionInvariant_withScope
    | with_reducible apply preservesConstructionInvariant_finishActivation
    | with_reducible apply preservesConstructionInvariant_withBreakTarget
    | with_reducible apply preservesConstructionInvariant_constructLocal
    | with_reducible apply preservesConstructionInvariant_bind
    | with_reducible apply preservesConstructionInvariant_listMapM
    | with_reducible apply preservesConstructionInvariant_listForIn
    | with_reducible apply preservesConstructionInvariant_arrayForIn
    | with_reducible apply preservesConstructionInvariant_rangeForIn
    | with_reducible split
    | with_reducible rfl
    | with_reducible intro)

private theorem evalValue_lit_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (_previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Goose.Core.IntTy) (value : Int) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.lit ty value)) := by
  simp only [evalValue]
  protocol_eval _previous

private theorem evalValue_bool_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (_previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (value : Bool) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.bool value)) := by
  simp only [evalValue]
  protocol_eval _previous

private theorem evalValue_read_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (place : Place) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.read place)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_ref_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (place : Place) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.ref mutability place)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_slice_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (view : View) (lo hi : Bound) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.slice mutability view lo hi origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_len_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (view : View) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.len view)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_un_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.un operation expression origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_bin_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.bin operation first second origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_cmp_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.cmp operation first second)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_and_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.and first second)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_or_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.or first second)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_not_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (expression : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.not expression)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_conv_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.conv kind target expression origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_call_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.call context arguments origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_push_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Option Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.push owner expression origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_pop_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (owner : Place) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.pop owner origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_ifE_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.ifE condition yes no origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_blockE_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (body : Block) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.blockE body origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_arrLit_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.arrLit ty operands origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_fill_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.fill ty expression origin)) := by
  cases ty <;> simp only [evalValue]
  all_goals protocol_eval previous

private theorem evalValue_structLit_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.structLit ty operands)) := by
  cases ty <;> simp only [evalValue]
  all_goals protocol_eval previous

private theorem evalValue_bytes_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.bytes ty bytes origin)) := by
  cases ty <;> try simp only [evalValue]
  all_goals protocol_eval previous
  case slice mutability element =>
    cases element <;> try simp only [evalValue]
    all_goals protocol_eval previous
    case int ty =>
      cases ty <;> simp only [evalValue]
      all_goals protocol_eval previous

private theorem evalValue_str_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.str ty arguments origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_copy_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.copy ty source origin)) := by
  simp only [evalValue]
  protocol_eval previous

private theorem evalValue_resultLocal_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (_previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.resultLocal localVar origin)) := by
  simp only [evalValue]
  protocol_eval _previous

private theorem evalValue_values_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (operands : List Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment (Expr.values operands)) := by
  cases operands with
  | nil => simpa only [evalValue] using preservesConstructionInvariant_pure Value.unit
  | cons expression operands =>
      cases operands <;> simp only [evalValue]
      all_goals protocol_eval previous

private theorem evalValue_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation) (expression : Expr) :
    (PreservesConstructionInvariant predicate) (evalValue (fuel + 1) config environment expression) := by
  cases expression with
  | lit ty value => exact evalValue_lit_preservesConstructionInvariant_succ fuel config previous environment ty value
  | bool value => exact evalValue_bool_preservesConstructionInvariant_succ fuel config previous environment value
  | read place => exact evalValue_read_preservesConstructionInvariant_succ fuel config previous environment place
  | ref mutability place => exact evalValue_ref_preservesConstructionInvariant_succ fuel config previous environment mutability place
  | slice mutability view lo hi origin => exact evalValue_slice_preservesConstructionInvariant_succ fuel config previous environment mutability view lo hi origin
  | len view => exact evalValue_len_preservesConstructionInvariant_succ fuel config previous environment view
  | un operation expression origin => exact evalValue_un_preservesConstructionInvariant_succ fuel config previous environment operation expression origin
  | bin operation first second origin => exact evalValue_bin_preservesConstructionInvariant_succ fuel config previous environment operation first second origin
  | cmp operation first second => exact evalValue_cmp_preservesConstructionInvariant_succ fuel config previous environment operation first second
  | and first second => exact evalValue_and_preservesConstructionInvariant_succ fuel config previous environment first second
  | or first second => exact evalValue_or_preservesConstructionInvariant_succ fuel config previous environment first second
  | not expression => exact evalValue_not_preservesConstructionInvariant_succ fuel config previous environment expression
  | conv kind target expression origin => exact evalValue_conv_preservesConstructionInvariant_succ fuel config previous environment kind target expression origin
  | call context arguments origin => exact evalValue_call_preservesConstructionInvariant_succ fuel config previous environment context arguments origin
  | push owner expression origin => exact evalValue_push_preservesConstructionInvariant_succ fuel config previous environment owner expression origin
  | pop owner origin => exact evalValue_pop_preservesConstructionInvariant_succ fuel config previous environment owner origin
  | ifE condition yes no origin => exact evalValue_ifE_preservesConstructionInvariant_succ fuel config previous environment condition yes no origin
  | blockE body origin => exact evalValue_blockE_preservesConstructionInvariant_succ fuel config previous environment body origin
  | arrLit ty operands origin => exact evalValue_arrLit_preservesConstructionInvariant_succ fuel config previous environment ty operands origin
  | fill ty expression origin => exact evalValue_fill_preservesConstructionInvariant_succ fuel config previous environment ty expression origin
  | structLit ty operands => exact evalValue_structLit_preservesConstructionInvariant_succ fuel config previous environment ty operands
  | bytes ty bytes origin => exact evalValue_bytes_preservesConstructionInvariant_succ fuel config previous environment ty bytes origin
  | str ty arguments origin => exact evalValue_str_preservesConstructionInvariant_succ fuel config previous environment ty arguments origin
  | copy ty source origin => exact evalValue_copy_preservesConstructionInvariant_succ fuel config previous environment ty source origin
  | resultLocal localVar origin => exact evalValue_resultLocal_preservesConstructionInvariant_succ fuel config previous environment localVar origin
  | values operands => exact evalValue_values_preservesConstructionInvariant_succ fuel config previous environment operands

private theorem buildElement_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    (PreservesConstructionInvariant predicate) (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  protocol_eval previous

private theorem execWhile_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    (PreservesConstructionInvariant predicate) (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  protocol_eval previous

private theorem execRange_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    (PreservesConstructionInvariant predicate) (execRange (fuel + 1) config environment var ty first last body) := by
  simp only [execRange]
  protocol_eval previous

private theorem execEach_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) :
    (PreservesConstructionInvariant predicate) (execEach (fuel + 1) config environment var index byRef body view current) := by
  simp only [execEach]
  protocol_eval previous

private theorem loopBody_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    (PreservesConstructionInvariant predicate) (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  protocol_eval previous

private theorem pushValue_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  protocol_eval previous

set_option maxHeartbeats 2000000 in
private theorem evalProduce_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) :
    (PreservesConstructionInvariant predicate) (evalProduce (fuel + 1) config environment channels expression) := by
  cases channels with
  | nil =>
      cases expression <;> simp only [evalProduce]
      all_goals protocol_eval previous
  | cons channel channels =>
      cases channels with
      | nil =>
          cases channel <;> cases expression <;> simp only [evalProduce]
          all_goals protocol_eval previous
      | cons second channels =>
          cases expression <;> simp only [evalProduce]
          all_goals protocol_eval previous

set_option maxHeartbeats 2000000 in
private theorem buildExpr_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) :
    (PreservesConstructionInvariant predicate) (buildExpr (fuel + 1) config environment destination expression) := by
  cases expression <;> try simp only [buildExpr]
  all_goals protocol_eval previous
  case fill ty expression origin =>
    cases ty <;> simp only [buildExpr]
    all_goals protocol_eval previous
  case values operands =>
    cases operands with
    | nil =>
        simp only [buildExpr]
        protocol_eval previous
    | cons expression operands =>
        cases operands <;> simp only [buildExpr]
        all_goals protocol_eval previous

set_option maxHeartbeats 2000000 in
private theorem execStmt_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation) (statement : Stmt) :
    (PreservesConstructionInvariant predicate) (execStmt (fuel + 1) config environment statement) := by
  cases statement <;> try simp only [execStmt]
  all_goals protocol_eval previous
  case ifS condition yes no origin =>
    cases no <;> simp only [execStmt]
    all_goals protocol_eval previous

private theorem execBlock_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    (PreservesConstructionInvariant predicate) (execBlock (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execBlock]
  protocol_eval previous

private theorem execResultBlockWith_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    (PreservesConstructionInvariant predicate) (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execResultBlockWith]
  protocol_eval previous

private theorem invokeCall_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply preservesConstructionInvariant_bind
  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getImplementation config context)
  · intro implementation
    rcases implementation with ⟨id, implementation⟩
    split
    · protocol_eval previous
    · apply preservesConstructionInvariant_bind
      · protocol_eval previous
      · intro callableChannels
        apply preservesConstructionInvariant_bind
        · exact previous.arguments _ _ _ _
        · intro values
          apply preservesConstructionInvariant_bind
          · exact preservesConstructionInvariant_get
          · intro state
            split
            · protocol_eval previous
            · apply preservesConstructionInvariant_allocateActivation
                (make := fun act => ⟨id, act, implementation.vars, [], callableChannels⟩)
                (action := fun activation => do
                  let carriers ← enterActivation fuel config activation
                    ((implementation.params.toList.zip values).map fun item => (item.1.var, item.2))
                    implementation.body origin
                  deliverCarriers fuel config.layout channels carriers origin)
              intro activation
              protocol_eval previous

theorem evaluation_preservesConstructionInvariant (fuel : Nat) (config : EvalConfig) :
    (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config := by
  induction fuel with
  | zero => exact evaluationPreservesConstructionInvariant_zero config
  | succ fuel previous =>
      refine {
        value := evalValue_preservesConstructionInvariant_succ fuel config previous
        bound := evalBound_preservesConstructionInvariant_succ fuel config previous
        place := evalPlace_preservesConstructionInvariant_succ fuel config previous
        view := evalView_preservesConstructionInvariant_succ fuel config previous
        produce := evalProduce_preservesConstructionInvariant_succ fuel config previous
        operands := evalOperands_preservesConstructionInvariant_succ fuel config previous
        build := buildExpr_preservesConstructionInvariant_succ fuel config previous
        element := buildElement_preservesConstructionInvariant_succ fuel config previous
        arguments := evalArguments_preservesConstructionInvariant_succ fuel config previous
        call := invokeCall_preservesConstructionInvariant_succ fuel config previous
        activation := enterActivation_preservesConstructionInvariant_succ fuel config previous
        activationBody := ?_
        resultBlock := execResultBlock_preservesConstructionInvariant_succ fuel config previous
        resultBlockWith := execResultBlockWith_preservesConstructionInvariant_succ fuel config previous
        block := execBlock_preservesConstructionInvariant_succ fuel config previous
        statements := execStmts_preservesConstructionInvariant_succ fuel config previous
        statement := execStmt_preservesConstructionInvariant_succ fuel config previous
        printArgument := evalPrintArg_preservesConstructionInvariant_succ fuel config previous
        whileLoop := execWhile_preservesConstructionInvariant_succ fuel config previous
        rangeLoop := execRange_preservesConstructionInvariant_succ fuel config previous
        eachLoop := execEach_preservesConstructionInvariant_succ fuel config previous
        loop := loopBody_preservesConstructionInvariant_succ fuel config previous
        push := pushValue_preservesConstructionInvariant_succ fuel config previous }
      intro environment pre body
      apply execActivationBody_preservesConstructionInvariant
      exact execResultBlockWith_preservesConstructionInvariant_succ fuel config previous environment pre environment.channels body

theorem initGlobals_preservesConstructionInvariant (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    (PreservesConstructionInvariant predicate) (initGlobals fuel config globals) := by
  have previous := evaluation_preservesConstructionInvariant (predicate := predicate) fuel config
  induction globals with
  | nil => simpa only [initGlobals] using preservesConstructionInvariant_pure ()
  | cons global globals preserved =>
      simp only [initGlobals]
      protocol_eval previous

theorem runModule_preservesConstructionInvariant (fuel : Nat) (config : EvalConfig) :
    (PreservesConstructionInvariant predicate) (runModule fuel config) := by
  have previous := evaluation_preservesConstructionInvariant (predicate := predicate) fuel config
  unfold runModule
  apply preservesConstructionInvariant_bind
  · exact initGlobals_preservesConstructionInvariant _ _ _
  · intro _
    protocol_eval previous

end Goose.Proofs.ConstructionExecutionProtocol
