import Goose.Lower.DemandGeneratedScalarSteps
import Goose.Lower.DemandExpressionSuffix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive ScalarChildren where
  | leaf
  | unary
  | binary

def ScalarExpression.children {expression : Expr} : ScalarExpression expression → ScalarChildren
  | .literal .. | .boolean .. => .leaf
  | .negate .. | .unary .. | .convert .. => .unary
  | .binary .. | .compare .. => .binary

inductive ScalarChildTraversals {cfg : Cfg} {env : Env} (map : RetainedSsaMap) (cx : FnCtx) :
    {expression : Expr} → {state : St} → (source : ExprSource cfg env expression state) →
      ScalarExpression expression → Nat → Nat → DemandRuntimePoint → DemandRuntimePoint → Prop where
  | leaf {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
      {form : ScalarExpression expression} {point : Pt} {frame : GIR.Frame}
      (shape : form.children = .leaf)
      (demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
        source.context.inputFuture map.values map.runs ⟨point, frame, state⟩) (fuel : Nat) :
      ScalarChildTraversals map cx source form 0 fuel ⟨point, frame, state⟩ ⟨point, frame, state⟩
  | unary {expression childExpression : Expr} {state after : St} {source : ExprSource cfg env expression state}
      {form : ScalarExpression expression} {child : ExprSource cfg env childExpression state}
      {found : DemandNode.child? (.expression expression) 0 = some (.expression childExpression)}
      (shape : form.children = .unary) (metadata : source.ChildAt child 0 found)
      {length fuel : Nat} {start point : Pt} {initial frame : GIR.Frame}
      (traversal : DemandTraversal cx (CanonicalExpressionDemand map cx child) length fuel
        ⟨start, initial, state⟩ ⟨point, frame, after⟩) :
      ScalarChildTraversals map cx source form length fuel ⟨start, initial, state⟩ ⟨point, frame, after⟩
  | binary {expression leftExpression rightExpression : Expr} {state afterLeft afterRight : St}
      {source : ExprSource cfg env expression state} {form : ScalarExpression expression}
      {left : ExprSource cfg env leftExpression state} {right : ExprSource cfg env rightExpression afterLeft}
      {leftFound : DemandNode.child? (.expression expression) 0 = some (.expression leftExpression)}
      {rightFound : DemandNode.child? (.expression expression) 1 = some (.expression rightExpression)}
      (shape : form.children = .binary) (leftMetadata : source.ChildAt left 0 leftFound)
      (rightMetadata : source.ChildAt right 1 rightFound)
      {leftLength rightLength fuel : Nat} {start middle point : Pt} {initial middleFrame frame : GIR.Frame}
      (leftTraversal : DemandTraversal cx (CanonicalExpressionDemand map cx left) leftLength fuel
        ⟨start, initial, state⟩ ⟨middle, middleFrame, afterLeft⟩)
      (rightTraversal : DemandTraversal cx (CanonicalExpressionDemand map cx right) rightLength (fuel - leftLength)
        ⟨middle, middleFrame, afterLeft⟩ ⟨point, frame, afterRight⟩) :
      ScalarChildTraversals map cx source form (leftLength + rightLength) fuel
        ⟨start, initial, state⟩ ⟨point, frame, afterRight⟩

theorem ScalarChildTraversals.lift {cfg : Cfg} {env : Env} {map : RetainedSsaMap} {cx : FnCtx}
    {expression : Expr} {state : St} {source : ExprSource cfg env expression state} {form : ScalarExpression expression}
    {length fuel : Nat} {before after : DemandRuntimePoint}
    (childTrace : ScalarChildTraversals map cx source form length fuel before after) :
    DemandTraversal cx (CanonicalExpressionDemand map cx source) length fuel before after := by
  cases childTrace with
  | leaf shape demanded fuel => exact .done fuel (.entry demanded)
  | unary shape metadata traversal => exact traversal.mono (fun _ cursor => .child metadata cursor)
  | binary shape leftMetadata rightMetadata left right =>
    exact (left.mono (fun _ cursor => .child leftMetadata cursor)).append
      (right.mono (fun _ cursor => .child rightMetadata cursor))

theorem ScalarExpression.operation_not_call {expression : Expr} (form : ScalarExpression expression)
    (le : LEnv) (before : LS) (context : ContextId) (arguments : List ValueId) (origin : Option OriginId) :
    form.operation le before ≠ .call context arguments origin := by
  cases form <;> simp only [operation]
  all_goals try simp
  all_goals split <;> simp

theorem ScalarExpression.operation_pure {expression : Expr} (form : ScalarExpression expression)
    (le : LEnv) (before : LS) (cx : FnCtx) (frame : GIR.Frame) (fuel : Nat) :
    execOp fuel cx frame (form.operation le before) = execPure cx frame (form.operation le before) := by
  cases operationEq : form.operation le before with
  | call context arguments origin => exact (form.operation_not_call le before context arguments origin operationEq).elim
  | _ => unfold execOp; rfl

theorem accepted_generated_scalar_child_traversal {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) {cfg : Cfg} {env : Env} {state intermediate after : St}
    (source : ExprSource cfg env expression state) {sourceFuel : Nat}
    (evaluated : form.PrefixEvaluated inputs sourceFuel cfg env state intermediate)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {required map : RetainedSsaMap} {point start : Pt}
    (site : GeneratedScalarSite form cfg.mod source.rootsEnv.access cx.fn le root source.path before required point)
    (coverage : map.Covers required) {initial frame : GIR.Frame}
    (post : Post cfg env cx before initial (form.prefix le before) frame point (form.cells le before inputs))
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame intermediate next nextFrame after)
    {length fuel : Nat} (room : length < fuel)
    (children : ScalarChildTraversals map cx source form length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    ∃ value, evalExpr (sourceFuel + 1) cfg env expression state = .ok value after ∧
      ExpressionDemandBoundary source map cx before initial (lowerExpr expression le before).2
        (lowerExpr expression le before).1 value after next nextFrame ∧
      DemandTraversal cx (CanonicalExpressionDemand map cx source) (length + 1) fuel
        ⟨start, initial, state⟩ ⟨next, nextFrame, after⟩ := by
  have childTrace := children.lift
  obtain ⟨_, _, _, _, _, _, value, computed, stateEq, pointEq, frameEq, done, boundary⟩ :=
    accepted_generated_scalar_runtime_step form inputs source evaluated site coverage post
      (bounded.mono post.mono) childTrace.last_valid.carried step
  subst after next nextFrame
  have emitted : emitDef (form.operation le before) le (form.prefix le before) =
      ((lowerExpr expression le before).1, (lowerExpr expression le before).2) := by rw [← form.lower]
  have execution : execPure cx frame (form.operation le before) intermediate = .ok (.val value) intermediate := by
    rw [← form.operation_pure le before cx frame 0, form.instruction_decompose inputs post.rel.prof post.has, computed]
  obtain ⟨result, traversal⟩ := expression_definition_demand_traversal source done admitted post bounded realized
    emitted site.extended (form.operation_not_call le before) execution room childTrace
  exact ⟨value, done, result, traversal⟩

theorem accepted_generated_scalar_child_abort {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) {cfg : Cfg} {env : Env} {state intermediate after : St}
    (source : ExprSource cfg env expression state) {sourceFuel : Nat}
    (evaluated : form.PrefixEvaluated inputs sourceFuel cfg env state intermediate)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {required map : RetainedSsaMap} {point start : Pt}
    (site : GeneratedScalarSite form cfg.mod source.rootsEnv.access cx.fn le root source.path before required point)
    (coverage : map.Covers required) {initial frame : GIR.Frame}
    (post : Post cfg env cx before initial (form.prefix le before) frame point (form.cells le before inputs))
    {targetFuel length fuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, intermediate⟩ stop after)
    (nonTimeout : stop ≠ .timeout) (room : length < fuel)
    (children : ScalarChildTraversals map cx source form length fuel
      ⟨start, initial, state⟩ ⟨point, frame, intermediate⟩) :
    evalExpr (sourceFuel + 1) cfg env expression state = .stop stop after ∧
      DemandStoppedTraversal cx (CanonicalExpressionDemand map cx source) length fuel
        ⟨start, initial, state⟩ stop after := by
  have childTrace := children.lift
  obtain ⟨_, _, computed, stateEq, done, _, _⟩ := accepted_generated_scalar_runtime_stop form inputs source evaluated
    site coverage post childTrace.last_valid.carried stopped nonTimeout
  subst after
  have emitted : emitDef (form.operation le before) le (form.prefix le before) =
      ((lowerExpr expression le before).1, (lowerExpr expression le before).2) := by rw [← form.lower]
  have execution : execPure cx frame (form.operation le before) intermediate = .stop stop intermediate := by
    rw [← form.operation_pure le before cx frame 0, form.instruction_decompose inputs post.rel.prof post.has, computed]
  exact ⟨done, expression_definition_demand_stopped source post emitted site.extended
    (form.operation_not_call le before) execution room childTrace⟩

end Goose.Lower
