import Goose.Proofs.ExitExecutionActivationChannelsBase
import Lean.Elab.Tactic

namespace Goose.Proofs.ExitExecution
open Goose.Construct

structure EvaluationActivationChannels (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, PreservesActivationChannels (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, PreservesActivationChannels (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, PreservesActivationChannels (evalPlace fuel config environment operand)
  view : ∀ environment operand, PreservesActivationChannels (evalView fuel config environment operand)
  produce : ∀ environment channels operand, PreservesActivationChannels (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, PreservesActivationChannels (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, PreservesActivationChannels (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, PreservesActivationChannels (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, PreservesActivationChannels (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, PreservesActivationChannels (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, FiltersActivationChannels environment (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, PreservesActivationChannels (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, PreservesActivationChannels (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, PreservesActivationChannels (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, PreservesActivationChannels (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, PreservesActivationChannels (execStmts fuel config environment statements)
  statement : ∀ environment statement, PreservesActivationChannels (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, PreservesActivationChannels (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, PreservesActivationChannels (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, PreservesActivationChannels (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, PreservesActivationChannels (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, PreservesActivationChannels (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, PreservesActivationChannels (pushValue fuel config environment owner expression origin)

theorem evaluationActivationChannels_zero (config : EvalConfig) : EvaluationActivationChannels 0 config := by
  constructor
  all_goals intros
  all_goals simp only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
    buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
    execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
    execWhile, execRange, execEach, loopBody, pushValue]
  all_goals first
    | exact preservesActivationChannels_stop _
    | (intro state fresh; exact True.intro)

elab "activation_channels_fresh " previous:ident : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesFresh do
    throwError "expected fresh-preservation action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| fresh_eval $previous))

elab "activation_channels_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesActivationChannels do
    throwError "expected activation-channel action"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do
    throwError "expected conditional action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesActivationChannels_conditional))

elab "activation_channels_intro" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

elab "activation_channels_zeta" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesActivationChannels do
    throwError "expected activation-channel action"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.isLet || (action.isApp && (action.getAppFn.isLambda || action.getAppFn.isLet)) do
    throwError "expected local action binding"
  Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))

macro "activation_channels_step " fresh:ident channels:ident : tactic => `(tactic|
  first
    | assumption
    | (solve | activation_channels_fresh $fresh)
    | activation_channels_conditional
    | with_reducible exact preservesActivationChannels_pure _
    | with_reducible exact preservesActivationChannels_stop _
    | with_reducible exact preservesActivationChannels_get
    | with_reducible exact preservesActivationChannels_freshAct
    | with_reducible exact preservesActivationChannels_freshScope
    | with_reducible exact preservesActivationChannels_fault _
    | with_reducible exact preservesActivationChannels_timeout
    | with_reducible exact preservesActivationChannels_abortAt _ _
    | with_reducible exact preservesActivationChannels_bindStaticRoot _ _
    | with_reducible exact preservesActivationChannels_setObjectOrdinal _ _
    | exact preservesActivationChannels_bindRoot _ _
    | with_reducible apply preservesActivationChannels_liftConstruction
    | with_reducible exact preservesActivationChannels_liftLayout _
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_rootOf _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectInt _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectBool _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectRef _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_sameIntType _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_comparable _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc _ _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_arrayLength _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_getStorage _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_readStoredElement _ _ _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_carrierValue _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_singleCarrier _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_completedDestination _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedDestination _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_receivingLayout _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_getImplementation _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_enclosingActivation _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_targetActivation _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_currentBreak _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_liftExcept _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ ((rendering_stateQueries _ _).1 _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ ((rendering_stateQueries _ _).2.2.2 _ _)
    | with_reducible apply preservesActivationChannels_bind
    | with_reducible apply preservesActivationChannels_listMapM
    | with_reducible apply preservesActivationChannels_listForIn
    | with_reducible apply preservesActivationChannels_arrayForIn
    | with_reducible apply preservesActivationChannels_rangeForIn
    | with_reducible apply preservesActivationChannels_withScope
    | with_reducible apply preservesActivationChannels_mapActivations
    | with_reducible exact ($channels).value _ _
    | with_reducible exact ($channels).bound _ _ _ _
    | with_reducible exact ($channels).place _ _
    | with_reducible exact ($channels).view _ _
    | with_reducible exact ($channels).produce _ _ _
    | with_reducible exact ($channels).operands _ _ _
    | with_reducible exact ($channels).build _ _ _
    | with_reducible exact ($channels).element _ _ _ _
    | with_reducible exact ($channels).arguments _ _ _ _
    | with_reducible exact ($channels).call _ _ _ _ _
    | with_reducible exact ($channels).activationBody _ _ _
    | with_reducible exact ($channels).resultBlock _ _ _
    | with_reducible exact ($channels).resultBlockWith _ _ _ _
    | with_reducible exact ($channels).block _ _ _ _
    | with_reducible exact ($channels).statements _ _
    | with_reducible exact ($channels).statement _ _
    | with_reducible exact ($channels).printArgument _ _
    | with_reducible exact ($channels).whileLoop _ _ _
    | with_reducible exact ($channels).rangeLoop _ _ _ _ _ _
    | with_reducible exact ($channels).eachLoop _ _ _ _ _ _ _
    | with_reducible exact ($channels).loop _ _ _
    | with_reducible exact ($channels).push _ _ _ _
    | activation_channels_zeta
    | with_reducible rfl
    | with_reducible activation_channels_intro
    | split)

macro "activation_channels_eval " fresh:ident channels:ident : tactic => `(tactic|
  repeat' activation_channels_step $fresh $channels)

end Goose.Proofs.ExitExecution
