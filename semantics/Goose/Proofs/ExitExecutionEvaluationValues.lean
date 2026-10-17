import Goose.Proofs.ExitExecutionProducerChannels
import Lean.Elab.Tactic

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem evaluationPreservesFresh_zero (config : EvalConfig) : EvaluationPreservesFresh 0 config := by
  constructor
  all_goals intros
  all_goals simp [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
    buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
    execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
    execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
    PreservesFresh, Goose.Proofs.Exit.stepState, bind]

theorem evalBound_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) :
    PreservesFresh (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases operand with
  | omitted => simpa only [evalBound] using preservesFresh_pure defaultValue
  | expr expression | fromEnd expression =>
      simp only [evalBound]
      apply preservesFresh_bind
      · exact previous.value _ _
      · intro value
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_expectInt value)
        · intro pair; exact preservesFresh_pure _

theorem evalPlace_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (operand : Place) :
    PreservesFresh (evalPlace (fuel + 1) config environment operand) := by
  cases operand with
  | var localVar =>
      simp only [evalPlace]
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_rootOf _ _)
      · intro _; exact preservesFresh_pure _
  | global global => simpa only [evalPlace] using preservesFresh_pure (Goose.Core.Loc.mk (.global global) [])
  | deref expression =>
      simp only [evalPlace]
      apply preservesFresh_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_preservesFresh _ (stateQuery_expectRef value)
  | elem view expression origin =>
      simp only [evalPlace]
      apply preservesFresh_bind
      · exact previous.view _ _
      · intro view
        apply preservesFresh_bind
        · exact previous.value _ _
        · intro value
          apply preservesFresh_bind
          · exact stateQuery_preservesFresh _ (stateQuery_expectInt value)
          · intro pair
            rcases pair with ⟨ty, index⟩
            split
            · exact preservesFresh_pure _
            · exact preservesFresh_stop _
  | field place index =>
      simp only [evalPlace]
      apply preservesFresh_bind
      · exact previous.place _ _
      · intro _; exact preservesFresh_pure _

theorem evalView_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (operand : View) :
    PreservesFresh (evalView (fuel + 1) config environment operand) := by
  cases operand with
  | of place =>
      simp only [evalView]
      apply preservesFresh_bind
      · exact previous.place _ _
      · intro location
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_readLoc _ _ _)
        · intro value
          apply preservesFresh_bind
          · exact stateQuery_preservesFresh _ (stateQuery_arrayLength value)
          · intro pair
            rcases pair with ⟨count, dynamic⟩
            exact preservesFresh_pure _
  | val expression =>
      simp only [evalView]
      apply preservesFresh_bind
      · exact previous.value _ _
      · intro value
        cases value <;> first
          | exact preservesFresh_pure _
          | (apply preservesFresh_bind
             · exact stateQuery_preservesFresh _ (stateQuery_arrayLength _)
             · intro pair
               rcases pair with ⟨count, dynamic⟩
               apply preservesFresh_bind
               · exact preservesFresh_freshScope
               · intro index
                 apply preservesFresh_bind
                 · exact preservesFresh_bindRoot _ _
                 · intro _; exact preservesFresh_pure _)

theorem evalOperands_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    PreservesFresh (evalOperands (fuel + 1) config environment channels operands) := by
  cases channels <;> cases operands <;> simp only [evalOperands]
  all_goals first
    | exact preservesFresh_pure _
    | exact preservesFresh_stop _
    | (apply preservesFresh_bind
       · exact previous.produce _ _ _
       · intro carriers
         apply preservesFresh_bind
         · exact stateQuery_preservesFresh _ (stateQuery_singleCarrier carriers)
         · intro carrier
           apply preservesFresh_bind
           · exact previous.operands _ _ _
           · intro _; exact preservesFresh_pure _)

theorem evalPrintArg_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (argument : PrintArg) :
    PreservesFresh (evalPrintArg (fuel + 1) config environment argument) := by
  cases argument with
  | text text => simpa only [evalPrintArg] using preservesFresh_pure text.toUTF8
  | expr expression =>
      simp only [evalPrintArg]
      apply preservesFresh_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_preservesFresh _ ((rendering_stateQueries fuel config.layout).1 _ _)
  | view view =>
      simp only [evalPrintArg]
      apply preservesFresh_bind
      · exact previous.view _ _
      · intro view; exact stateQuery_preservesFresh _ ((rendering_stateQueries fuel config.layout).2.2.2 _ _)

theorem evalArguments_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) :
    PreservesFresh (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases parameters with
  | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact preservesFresh_pure _
      · exact preservesFresh_stop _
  | cons parameter parameters =>
      cases arguments with
      | nil => simpa only [evalArguments, fault] using preservesFresh_stop (Goose.Core.Stop.fault .arity)
      | cons argument arguments =>
          have finish (value : Value) : PreservesFresh (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
            apply preservesFresh_bind
            · exact previous.arguments _ _ _ _
            · intro _; exact preservesFresh_pure _
          cases argument with
          | byVal expression =>
              simp only [evalArguments]
              apply preservesFresh_bind
              · exact previous.value _ _
              · intro value; exact finish value
          | byRef mutability place =>
              simp only [evalArguments]
              apply preservesFresh_bind
              · exact previous.place _ _
              · intro location
                apply preservesFresh_bind
                · exact preservesFresh_pure _
                · intro value; exact finish value
          | construct expression =>
              simp only [evalArguments]
              split
              · apply preservesFresh_bind
                · apply preservesFresh_materializeProducer
                  exact previous.value _ _
                · intro materialized
                  have finishCarrier (carrier : Carrier) : PreservesFresh (do
                      let value ← carrierValue carrier
                      let values ← evalArguments fuel config environment vars parameters arguments
                      pure (value :: values)) := by
                    apply preservesFresh_bind
                    · exact stateQuery_preservesFresh _ (stateQuery_carrierValue carrier)
                    · intro value; exact finish value
                  cases materialized with
                  | none =>
                      apply preservesFresh_bind
                      · apply preservesFresh_constructLocal
                        intro destination; exact previous.build _ _ _
                      · exact finishCarrier
                  | some source =>
                      apply preservesFresh_bind
                      · exact preservesFresh_materializedDestination _ _ _ _ _ _ _
                      · intro destination
                        apply preservesFresh_bind
                        · exact preservesFresh_publishCarriers _ _
                        · intro ignored
                          apply preservesFresh_bind
                          · exact preservesFresh_pure _
                          · exact finishCarrier
              · apply preservesFresh_bind
                · exact preservesFresh_stop _
                · intro value; exact finish value

theorem execStmts_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) : PreservesFresh (execStmts (fuel + 1) config environment statements) := by
  cases statements with
  | nil => simpa only [execStmts] using preservesFresh_pure (Flow.normal .unit)
  | cons statement statements =>
      simp only [execStmts]
      apply preservesFresh_bind
      · exact previous.statement _ _
      · intro flow
        cases flow with
        | normal value => exact previous.statements _ _
        | breaking value | continuing => exact preservesFresh_pure _

theorem execResultBlock_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    PreservesFresh (execResultBlock (fuel + 1) config environment channels body) := by
  simpa only [execResultBlock] using previous.resultBlockWith environment [] channels body

theorem enterActivation_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    PreservesFresh (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  split
  · apply preservesFresh_finishActivation
    exact previous.activationBody _ _ _
  · exact preservesFresh_stop _

private theorem preservesFresh_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (identifier : ∀ activation, (change activation).act = activation.act)
    (action : EvalM α) (preserved : PreservesFresh action) :
    PreservesFresh (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state fresh
  have updated := fresh_activations_map state change identifier fresh
  simpa [EvalM.get, EvalM.set, bind, pure] using preserved _ updated

private theorem preservesFresh_fault (kind : Goose.Core.FaultKind) : PreservesFresh (fault (α := α) kind) :=
  preservesFresh_stop _

private theorem preservesFresh_timeout : PreservesFresh (timeout (α := α)) := preservesFresh_stop _

private theorem preservesFresh_abortAt (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    PreservesFresh (abortAt (α := α) kind origin) := preservesFresh_stop _

private theorem preservesFresh_fault_bind (kind : Goose.Core.FaultKind) (next : α → EvalM β) :
    PreservesFresh (fault kind >>= next) := by
  intro state fresh
  exact fresh

private theorem preservesFresh_timeout_bind (next : α → EvalM β) :
    PreservesFresh (timeout >>= next) := by
  intro state fresh
  exact fresh

private theorem preservesFresh_abortAt_bind (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId)
    (next : α → EvalM β) : PreservesFresh (abortAt kind origin >>= next) := by
  intro state fresh
  exact fresh

private theorem preservesFresh_conditional (condition : Prop) [Decidable condition]
    (yes no : EvalM α) (left : PreservesFresh yes) (right : PreservesFresh no) :
    PreservesFresh (if condition then yes else no) := by
  split <;> assumption

elab "fresh_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesFresh do throwError "expected freshness action"
  let args := target.getAppArgs
  let some action := args[args.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do throwError "expected conditional"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesFresh_conditional))

syntax "fresh_eval" ident : tactic
macro_rules
  | `(tactic| fresh_eval $previous:ident) => `(tactic|
  repeat' first
    | with_reducible assumption
    | fresh_conditional
    | with_reducible exact preservesFresh_pure _
    | with_reducible exact preservesFresh_stop _
    | with_reducible exact preservesFresh_fault _
    | with_reducible exact preservesFresh_timeout
    | with_reducible exact preservesFresh_abortAt _ _
    | with_reducible exact preservesFresh_fault_bind _ _
    | with_reducible exact preservesFresh_timeout_bind _
    | with_reducible exact preservesFresh_abortAt_bind _ _ _
    | with_reducible exact preservesFresh_get
    | with_reducible exact preservesFresh_materializeNamedCarriers _ _
    | with_reducible exact preservesFresh_materializeOwnedCarriers _ _ _
    | with_reducible exact preservesFresh_landCarriersInto _ _ _
    | with_reducible exact preservesFresh_selectCompletionChannel _ _ _
    | with_reducible exact preservesFresh_prepareNamedCarrier _ _ _
    | with_reducible exact preservesFresh_prepareNamedCarrierAt _ _ _ _
    | with_reducible exact preservesFresh_receivingAction _ _ _
    | with_reducible exact preservesFresh_receivingDestination _
    | with_reducible exact preservesFresh_completedReceivingDestination _
    | with_reducible exact preservesFresh_materializedDestination _ _ _ _ _ _ _
    | with_reducible exact preservesFresh_lift _ _
    | with_reducible exact preservesFresh_bindRoot _ _
    | with_reducible exact preservesFresh_bindStaticRoot _ _
    | with_reducible exact preservesFresh_reserveRootObject _
    | with_reducible exact preservesFresh_setObjectOrdinal _ _
    | with_reducible exact preservesFresh_newDestination _ _ _ _ _ _ _
    | with_reducible exact preservesFresh_channelsFor _ _ _ _
    | with_reducible exact preservesFresh_freshAct
    | with_reducible exact preservesFresh_freshScope
    | with_reducible exact preservesFresh_returned _ _
    | with_reducible exact preservesFresh_escaped _ _
    | with_reducible exact preservesFresh_jump _ _
    | with_reducible exact preservesFresh_emitStdout _
    | with_reducible exact preservesFresh_publishCarriers _ _
    | with_reducible exact preservesFresh_copyValue _ _ _ _ _ _
    | with_reducible exact preservesFresh_deliverCarriers _ _ _ _ _
    | with_reducible exact preservesFresh_ownerDestination _ _ _ _ _
    | with_reducible exact preservesFresh_publishOwner _ _ _ _ _ _
    | with_reducible exact preservesFresh_openElementReceiving _ _ _ _ _ _ _
    | with_reducible exact preservesFresh_publishElementReceiving _ _ _ _ _ _
    | with_reducible exact preservesFresh_repeatElement _ _ _ _ _ _
    | with_reducible exact preservesFresh_truncateOwner _ _ _ _ _
    | with_reducible exact preservesFresh_appendFixedValues _ _ _ _ _
    | with_reducible exact preservesFresh_appendRun _ _ _ _ _
    | with_reducible exact preservesFresh_writeLoc _ _ _ _
    | with_reducible exact preservesFresh_landCarriers _ _
    | with_reducible exact preservesFresh_bindAll _ _ _
    | with_reducible exact preservesFresh_exitChannels _ _ _ _
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_rootOf _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_expectInt _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_expectBool _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_expectRef _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_sameIntType _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_comparable _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_readLoc _ _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_arrayLength _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_getDestination _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_getStorage _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_sampledStored _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_readStoredElement _ _ _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_carrierValue _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_singleCarrier _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_completedDestination _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_storedDestination _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_receivingLayout _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_getImplementation _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_enclosingActivation _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_targetActivation _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_currentBreak _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_liftExcept _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
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
    | with_reducible apply preservesFresh_allocateActivation
    | with_reducible apply preservesFresh_mapActivations
    | with_reducible apply preservesFresh_withOwnerExtension
    | with_reducible apply preservesFresh_protectDestination
    | with_reducible apply preservesFresh_withScope
    | with_reducible apply preservesFresh_finishActivation
    | with_reducible apply preservesFresh_withBreakTarget
    | with_reducible apply preservesFresh_constructLocal
    | with_reducible apply preservesFresh_materializeProducer
    | with_reducible apply preservesFresh_withExitChannels
    | with_reducible apply preservesFresh_withCompletionChannels
    | with_reducible apply preservesFresh_bind
    | with_reducible apply preservesFresh_listMapM
    | with_reducible apply preservesFresh_listForIn
    | with_reducible apply preservesFresh_arrayForIn
    | with_reducible apply preservesFresh_rangeForIn
    | with_reducible split
    | with_reducible rfl
    | with_reducible intro)

private theorem evalValue_lit_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Goose.Core.IntTy) (value : Int) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.lit ty value)) := by
  simp only [evalValue]
  fresh_eval _previous

private theorem evalValue_bool_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (value : Bool) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.bool value)) := by
  simp only [evalValue]
  fresh_eval _previous

private theorem evalValue_read_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (place : Place) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.read place)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_ref_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (place : Place) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.ref mutability place)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_slice_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (view : View) (lo hi : Bound) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.slice mutability view lo hi origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_len_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (view : View) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.len view)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_un_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.un operation expression origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_bin_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.bin operation first second origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_cmp_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.cmp operation first second)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_and_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.and first second)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_or_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.or first second)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_not_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (expression : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.not expression)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_conv_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.conv kind target expression origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_call_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.call context arguments origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_push_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Option Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.push owner expression origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_pop_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (owner : Place) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.pop owner origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_ifE_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.ifE condition yes no origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_blockE_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (body : Block) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.blockE body origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_arrLit_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.arrLit ty operands origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_fill_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.fill ty expression origin)) := by
  cases ty <;> simp only [evalValue]
  all_goals fresh_eval previous

private theorem evalValue_structLit_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.structLit ty operands)) := by
  cases ty <;> simp only [evalValue]
  all_goals fresh_eval previous

private theorem evalValue_bytes_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.bytes ty bytes origin)) := by
  cases ty <;> try simp only [evalValue]
  all_goals fresh_eval previous
  case slice mutability element =>
    cases element <;> try simp only [evalValue]
    all_goals fresh_eval previous
    case int ty =>
      cases ty <;> simp only [evalValue]
      all_goals fresh_eval previous

private theorem evalValue_str_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.str ty arguments origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_copy_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.copy ty source origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_resultLocal_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.resultLocal localVar origin)) := by
  simp only [evalValue]
  fresh_eval _previous

private theorem evalValue_values_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (operands : List Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.values operands)) := by
  cases operands with
  | nil => simpa only [evalValue] using preservesFresh_pure Value.unit
  | cons expression operands =>
      cases operands <;> simp only [evalValue]
      all_goals fresh_eval previous

theorem evalValue_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (expression : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment expression) := by
  cases expression with
  | lit ty value => exact evalValue_lit_preservesFresh_succ fuel config previous environment ty value
  | bool value => exact evalValue_bool_preservesFresh_succ fuel config previous environment value
  | read place => exact evalValue_read_preservesFresh_succ fuel config previous environment place
  | ref mutability place => exact evalValue_ref_preservesFresh_succ fuel config previous environment mutability place
  | slice mutability view lo hi origin => exact evalValue_slice_preservesFresh_succ fuel config previous environment mutability view lo hi origin
  | len view => exact evalValue_len_preservesFresh_succ fuel config previous environment view
  | un operation expression origin => exact evalValue_un_preservesFresh_succ fuel config previous environment operation expression origin
  | bin operation first second origin => exact evalValue_bin_preservesFresh_succ fuel config previous environment operation first second origin
  | cmp operation first second => exact evalValue_cmp_preservesFresh_succ fuel config previous environment operation first second
  | and first second => exact evalValue_and_preservesFresh_succ fuel config previous environment first second
  | or first second => exact evalValue_or_preservesFresh_succ fuel config previous environment first second
  | not expression => exact evalValue_not_preservesFresh_succ fuel config previous environment expression
  | conv kind target expression origin => exact evalValue_conv_preservesFresh_succ fuel config previous environment kind target expression origin
  | call context arguments origin => exact evalValue_call_preservesFresh_succ fuel config previous environment context arguments origin
  | push owner expression origin => exact evalValue_push_preservesFresh_succ fuel config previous environment owner expression origin
  | pop owner origin => exact evalValue_pop_preservesFresh_succ fuel config previous environment owner origin
  | ifE condition yes no origin => exact evalValue_ifE_preservesFresh_succ fuel config previous environment condition yes no origin
  | blockE body origin => exact evalValue_blockE_preservesFresh_succ fuel config previous environment body origin
  | arrLit ty operands origin => exact evalValue_arrLit_preservesFresh_succ fuel config previous environment ty operands origin
  | fill ty expression origin => exact evalValue_fill_preservesFresh_succ fuel config previous environment ty expression origin
  | structLit ty operands => exact evalValue_structLit_preservesFresh_succ fuel config previous environment ty operands
  | bytes ty bytes origin => exact evalValue_bytes_preservesFresh_succ fuel config previous environment ty bytes origin
  | str ty arguments origin => exact evalValue_str_preservesFresh_succ fuel config previous environment ty arguments origin
  | copy ty source origin => exact evalValue_copy_preservesFresh_succ fuel config previous environment ty source origin
  | resultLocal localVar origin => exact evalValue_resultLocal_preservesFresh_succ fuel config previous environment localVar origin
  | values operands => exact evalValue_values_preservesFresh_succ fuel config previous environment operands

theorem buildElement_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    PreservesFresh (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  fresh_eval previous

theorem execWhile_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    PreservesFresh (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  fresh_eval previous

theorem execRange_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    PreservesFresh (execRange (fuel + 1) config environment var ty first last body) := by
  simp only [execRange]
  fresh_eval previous

theorem execEach_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) :
    PreservesFresh (execEach (fuel + 1) config environment var index byRef body view current) := by
  simp only [execEach]
  fresh_eval previous

theorem loopBody_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesFresh (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  fresh_eval previous

theorem pushValue_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  fresh_eval previous


end Goose.Proofs.ExitExecution
