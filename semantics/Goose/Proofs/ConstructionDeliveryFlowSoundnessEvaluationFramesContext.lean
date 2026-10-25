import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesHelpers

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

structure EvaluationBreakFrames (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, BreakFrameAction (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, BreakFrameAction (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, BreakFrameAction (evalPlace fuel config environment operand)
  view : ∀ environment operand, BreakFrameAction (evalView fuel config environment operand)
  produce : ∀ environment channels operand, BreakFrameAction (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, BreakFrameAction (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, BreakFrameAction (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, BreakFrameAction (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, BreakFrameAction (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, BreakFrameAction (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, BreakFrameAction (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, BreakFrameAction (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, BreakFrameAction (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, BreakFrameAction (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, BreakFrameAction (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, BreakFrameAction (execStmts fuel config environment statements)
  statement : ∀ environment statement, BreakFrameAction (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, BreakFrameAction (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, BreakFrameAction (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, BreakFrameAction (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, BreakFrameAction (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, BreakFrameAction (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, BreakFrameAction (pushValue fuel config environment owner expression origin)

syntax "evaluation_frame_rec " ident : tactic
macro_rules
  | `(tactic| evaluation_frame_rec $previous:ident) => `(tactic|
  repeat' first
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
    | with_reducible exact breakFrame_expectInt _
    | with_reducible exact breakFrame_expectBool _
    | with_reducible exact breakFrame_expectRef _
    | with_reducible exact breakFrame_sameIntType _ _
    | with_reducible exact breakFrame_comparable _ _
    | with_reducible exact breakFrame_readLoc _ _ _
    | with_reducible exact breakFrame_bindRoot _ _
    | with_reducible exact breakFrame_bindStaticRoot _ _
    | with_reducible exact breakFrame_singleCarrier _
    | with_reducible exact breakFrame_carrierValue _
    | with_reducible exact breakFrame_publishCarriers _ _
    | with_reducible exact breakFrame_newDestination _ _ _ _ _ _ _
    | with_reducible exact breakFrame_channelsFor _ _ _ _
    | with_reducible exact breakFrame_bindAll _ _ _
    | with_reducible exact breakFrame_emitStdout _
    | with_reducible exact breakFrame_getImplementation _ _
    | with_reducible exact breakFrame_enclosingActivation _
    | with_reducible exact breakFrame_targetActivation _ _
    | with_reducible exact breakFrame_selectCompletionChannel _ _ _
    | with_reducible exact breakFrame_exitSource _ _ _
    | with_reducible exact breakFrame_exitChannels _ _ _ _
    | with_reducible exact breakFrame_materializeOwnedCarriers _ _ _
    | (with_reducible apply breakFrame_mapActivations)
    | (with_reducible apply breakFrame_allocateActivation)
    | (with_reducible apply breakFrame_execResultScope)
    | (with_reducible apply breakFrame_withScope)
    | (with_reducible apply breakFrame_withBreakTarget)
    | (with_reducible apply breakFrame_withCompletionChannels)
    | (with_reducible apply breakFrame_withExitChannels)
    | (with_reducible apply breakFrame_materializeProducer)
    | (with_reducible apply breakFrame_arrayForIn)
    | (with_reducible apply breakFrame_rangeForIn)
    | (with_reducible apply breakFrame_bind)
    | (with_reducible apply breakFrame_listForIn)
    | (with_reducible apply breakFrame_listMapM)
    | (solve | evaluation_frame_basic)
    | evaluation_frame_conditional
    | evaluation_frame_zeta
    | evaluation_frame_intro
    | split)

theorem evaluationBreakFrames_zero (config : EvalConfig) : EvaluationBreakFrames 0 config := by
  constructor
  all_goals intros
  all_goals simp only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
    buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
    execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
    execWhile, execRange, execEach, loopBody, pushValue]
  all_goals exact breakFrame_stop _

theorem evalBound_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) :
    BreakFrameAction (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases operand <;> simp only [evalBound] <;> evaluation_frame_rec previous

theorem evalPlace_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (operand : Place) :
    BreakFrameAction (evalPlace (fuel + 1) config environment operand) := by
  cases operand <;> simp only [evalPlace] <;> evaluation_frame_rec previous

theorem evalView_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (operand : View) :
    BreakFrameAction (evalView (fuel + 1) config environment operand) := by
  cases operand <;> simp only [evalView] <;> evaluation_frame_rec previous

theorem evalOperands_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    BreakFrameAction (evalOperands (fuel + 1) config environment channels operands) := by
  cases channels <;> cases operands <;> simp only [evalOperands] <;> evaluation_frame_rec previous

theorem execActivationBody_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    BreakFrameAction (execActivationBody (fuel + 1) config environment pre body) := by
  simp only [execActivationBody]
  evaluation_frame_rec previous

theorem execResultBlock_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    BreakFrameAction (execResultBlock (fuel + 1) config environment channels body) := by
  simp only [execResultBlock]
  evaluation_frame_rec previous

theorem execResultBlockWith_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    BreakFrameAction (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  simp only [execResultBlockWith]
  evaluation_frame_rec previous

theorem execBlock_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    BreakFrameAction (execBlock (fuel + 1) config environment pre channels body) := by
  cases body <;> simp only [execBlock] <;> evaluation_frame_rec previous

theorem execStmts_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) :
    BreakFrameAction (execStmts (fuel + 1) config environment statements) := by
  cases statements <;> simp only [execStmts] <;> evaluation_frame_rec previous

theorem execWhile_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    BreakFrameAction (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  evaluation_frame_rec previous

theorem execRange_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    BreakFrameAction (execRange (fuel + 1) config environment localVar ty first last body) := by
  simp only [execRange]
  evaluation_frame_rec previous

theorem execEach_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block) (view : RuntimeView) (current : Nat) :
    BreakFrameAction (execEach (fuel + 1) config environment localVar index byRef body view current) := by
  simp only [execEach]
  evaluation_frame_rec previous

theorem loopBody_breakFrame_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationBreakFrames fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    BreakFrameAction (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  evaluation_frame_rec previous

end Goose.Proofs.ConstructionDelivery
