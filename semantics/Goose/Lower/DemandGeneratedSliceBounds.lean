import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.DemandExpressionResult

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive SliceBoundOperand : Bound → Type where
  | omitted : SliceBoundOperand .omitted
  | expression (expr : Expr) (type : IntTy) (number : Int) : SliceBoundOperand (.expr expr)
  | fromEnd (expr : Expr) (type : IntTy) (number : Int) : SliceBoundOperand (.fromEnd expr)

def SliceBoundOperand.value {bound : Bound} (operand : SliceBoundOperand bound) (length : Nat) (default : Int) : Int :=
  match operand with
  | .omitted => default
  | .expression _ _ number => number
  | .fromEnd _ _ number => (length : Int) - number

def SliceBoundOperand.builder {bound : Bound} (operand : SliceBoundOperand bound) (le : LEnv) (before : LS) : LS :=
  match operand with
  | .omitted => before
  | .expression expr _ _ | .fromEnd expr _ _ => (lowerExpr expr le before).2

def SliceBoundOperand.target {bound : Bound} (operand : SliceBoundOperand bound) (le : LEnv) (before : LS) : Bnd :=
  match operand with
  | .omitted => .omitted
  | .expression expr _ _ => .val (lowerExpr expr le before).1
  | .fromEnd expr _ _ => .fromEnd (lowerExpr expr le before).1

def SliceBoundOperand.cells {bound : Bound} (operand : SliceBoundOperand bound) (le : LEnv) (before : LS) : List (ValueId × RVal) :=
  match operand with
  | .omitted => []
  | .expression expr type number | .fromEnd expr type number =>
      [((lowerExpr expr le before).1, .val (.int type number))]

def SliceBoundOperand.PrefixEvaluated {bound : Bound} (operand : SliceBoundOperand bound) (fuel : Nat)
    (cfg : Cfg) (env : Env) (state after : St) : Prop :=
  match operand with
  | .omitted => after = state
  | .expression expr type number | .fromEnd expr type number =>
      evalExpr fuel cfg env expr state = .ok (.int type number) after

theorem SliceBoundOperand.lower {bound : Bound} (operand : SliceBoundOperand bound) (le : LEnv) (before : LS) :
    lowerBound bound le before = (operand.target le before, operand.builder le before) := by
  cases operand <;> simp only [lowerBound, bind_run, pure_run, target, builder]

theorem SliceBoundOperand.source_evaluated {bound : Bound} (operand : SliceBoundOperand bound)
    {cfg : Cfg} {env : Env} {fuel length : Nat} {default : Int} {state after : St}
    (evaluated : operand.PrefixEvaluated fuel cfg env state after) :
    evalBound (fuel + 1) cfg env length default bound state = .ok (operand.value length default) after := by
  cases operand with
  | omitted => change after = state at evaluated; subst after; simp only [evalBound, value, pure_apply]
  | expression | fromEnd =>
    simp only [PrefixEvaluated] at evaluated
    simp only [evalBound, bind_apply, evaluated, expectInt, pure_apply, value]

theorem SliceBoundOperand.target_evaluated {bound : Bound} (operand : SliceBoundOperand bound)
    {le : LEnv} {before : LS} {frame : GIR.Frame}
    (has : ∀ cell ∈ operand.cells le before, frame.vals[cell.1]? = some cell.2)
    (length : Nat) (default : Int) (state : St) :
    evalBnd frame length default (lowerBound bound le before).1 state = .ok (operand.value length default) state := by
  rw [operand.lower]
  cases operand with
  | omitted => simp only [target, evalBnd, value, pure_apply]
  | expression expr type number =>
    have cell := has ((lowerExpr expr le before).1, .val (.int type number)) (by simp [cells])
    simp only [target, evalBnd, getVal_of cell, pure_bind, expectInt, pure_apply, value]
  | fromEnd expr type number =>
    have cell := has ((lowerExpr expr le before).1, .val (.int type number)) (by simp [cells])
    simp only [target, evalBnd, getVal_of cell, pure_bind, expectInt, pure_apply, value]

theorem generated_slice_bound_post {bound : Bound} (operand : SliceBoundOperand bound)
    {cfg : Cfg} {env : Env} {state after : St} (source : BoundSource cfg env bound state)
    {fuel length : Nat} {default : Int} (evaluated : operand.PrefixEvaluated fuel cfg env state after)
    {cx : FnCtx} {le : LEnv} {before : LS} {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial (operand.builder le before) frame point (operand.cells le before))
    {map : RetainedSsaMap} (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    evalBound (fuel + 1) cfg env length default bound state = .ok (operand.value length default) after ∧
    evalBnd frame length default (lowerBound bound le before).1 after = .ok (operand.value length default) after ∧
    Post cfg env cx before initial (lowerBound bound le before).2 frame point (operand.cells le before) ∧
    DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
      map.values map.runs ⟨point, frame, after⟩ := by
  have done := operand.source_evaluated evaluated (length := length) (default := default)
  have result := source.result (fuel + 1) length default (operand.value length default) done
  refine ⟨done, operand.target_evaluated post.has length default after, ?_, ?_⟩
  · simpa only [operand.lower] using post
  · exact ⟨⟨_, post.pp, post.rel⟩, result.frame, realized⟩

theorem accepted_generated_bound_expression {cfg : Cfg} {env : Env} {expression : Expr} {state after : St}
    (fromEnd : Bool) (source : BoundSource cfg env (if fromEnd then .fromEnd expression else .expr expression) state)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path
      (.bound (if fromEnd then .fromEnd expression else .expr expression)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {fuel length : Nat} {default : Int} {type : IntTy} {number : Int}
    (evaluated : evalExpr fuel cfg env expression state = .ok (.int type number) after)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial (lowerExpr expression le before).2 frame point
      [((lowerExpr expression le before).1, .val (.int type number))])
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    ∃ child : ExprSource cfg env expression state,
      source.ExpressionChildAt child (by cases fromEnd <;> rfl) ∧
      GeneratedDemandRows cfg.mod source.rootsEnv.access
        (.first occurrence (.bound (by cases fromEnd <;> rfl))) required ∧ map.Covers required ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, after⟩ ∧
      evalBound (fuel + 1) cfg env length default (if fromEnd then .fromEnd expression else .expr expression) state =
        .ok (if fromEnd then (length : Int) - number else number) after ∧
      evalBnd frame length default (lowerBound (if fromEnd then .fromEnd expression else .expr expression) le before).1 after =
        .ok (if fromEnd then (length : Int) - number else number) after ∧
      Post cfg env cx before initial (lowerBound (if fromEnd then .fromEnd expression else .expr expression) le before).2
        frame point [((lowerExpr expression le before).1, .val (.int type number))] ∧
      DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨point, frame, after⟩ := by
  obtain ⟨child, _, _, _, _, canonical⟩ := source.expressionChild fromEnd
  have childRealized : map.Realizes cfg.mod child.world env ⟨point, frame, after⟩ := by
    simpa only [canonical.world] using realized
  refine ⟨child, canonical, .first (first := .bound (by cases fromEnd <;> rfl)) rows, coverage,
    ⟨⟨_, post.pp, post.rel⟩, (child.result fuel (.int type number) evaluated).frame, childRealized⟩, ?_⟩
  cases fromEnd with
  | false => exact generated_slice_bound_post (.expression expression type number) source evaluated post realized
  | true => exact generated_slice_bound_post (.fromEnd expression type number) source evaluated post realized

end Goose.Lower
