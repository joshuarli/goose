import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.DemandGeneratedTransfer
import Goose.Lower.DemandExpressionResult
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem lowerView_val_run (expression : Expr) (le : LEnv) (before : LS) :
    lowerView (.val expression) le before = emitDef (.sliceView (lowerExpr expression le before).1) le
      (lowerExpr expression le before).2 := by
  simp only [lowerView, bind_run]

inductive GeneratedViewValueInstruction (m : Core.Module) (access : AccessEnv) :
    Func → RetainedSsaMap → DemandSourceLabel → Pt → Inst → Prop where
  | sliceView {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {expression : Expr} {required : RetainedSsaMap} {point : Pt}
      (occurrence : GeneratedDemandOccurrence m function le root path (.view (.val expression)) before)
      (rows : GeneratedDemandRows m access occurrence required)
      (atPoint : (lowerExpr expression le before).2.pp = some point)
      (extended : ExtT (lowerView (.val expression) le before).2 function.blocks) :
      GeneratedViewValueInstruction m access function required ⟨path ++ [0], .expression, .exit⟩ point
        (.def (lowerView (.val expression) le before).1 (.sliceView (lowerExpr expression le before).1))

theorem GeneratedViewValueInstruction.instruction {m : Core.Module} {access : AccessEnv} {function : Func}
    {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedViewValueInstruction m access function required label point instruction) :
    instAt function point = some instruction := by
  cases site with
  | @sliceView le root path before expression required point occurrence rows atPoint extended =>
    have emitted : emitDef (.sliceView (lowerExpr expression le before).1) le (lowerExpr expression le before).2 =
        ((lowerView (.val expression) le before).1, (lowerView (.val expression) le before).2) := by
      rw [lowerView_val_run]
    exact (emitDef_facts emitted atPoint extended).2.2.2.2

theorem GeneratedViewValueInstruction.requiredRows {m : Core.Module} {access : AccessEnv} {function : Func}
    {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedViewValueInstruction m access function required label point instruction) :
    ∃ (le : LEnv) (root : DemandNode) (expression : Expr) (before : LS)
      (occurrence : GeneratedDemandOccurrence m function le root label.path (.expression expression) before),
      GeneratedDemandRows m access occurrence required ∧ label.phase = .expression ∧ label.boundary = .exit := by
  cases site with
  | sliceView occurrence rows atPoint extended =>
    exact ⟨_, _, _, _, .first occurrence (.viewExpression rfl), .first (first := .viewExpression rfl) rows, rfl, rfl⟩

theorem generated_view_value_expression_extended {expression : Expr} {le : LEnv} {before : LS}
    {blocks : Array GIR.Block} (extended : ExtT (lowerView (.val expression) le before).2 blocks) :
    ExtT (lowerExpr expression le before).2 blocks := by
  rw [lowerView_val_run] at extended
  exact extended.of_adv (adv_emitDef rfl)

theorem view_value_runtime_reflection {cfg : Cfg} {env : Env} {expression : Expr} {sourceFuel targetFuel : Nat}
    {state intermediate after : St} {location : Loc} {start length : Nat}
    (evaluated : evalExpr sourceFuel cfg env expression state = .ok (.slice location start length) intermediate)
    {cx : FnCtx} {frame : GIR.Frame} {operand : ValueId} {value : RVal}
    (cell : frame.vals[operand]? = some (.val (.slice location start length)))
    (execution : execOp targetFuel cx frame (.sliceView operand) intermediate = .ok value after) :
    value = .view ⟨location, start, length, false⟩ ∧ after = intermediate ∧
      evalView (sourceFuel + 1) cfg env (.val expression) state = .ok ⟨location, start, length, false⟩ after := by
  simp only [execOp, execPure, getVal_of cell, expectSlice, pure_bind, pure_apply] at execution
  obtain ⟨rfl, rfl⟩ := Res.ok.inj execution
  refine ⟨rfl, rfl, ?_⟩
  simp only [evalView, bind_apply, evaluated, expectSlice, pure_apply]

theorem accepted_generated_view_value_runtime_step {cfg : Cfg} {env : Env} {expression : Expr}
    {state intermediate after : St} (source : ViewSource cfg env (.val expression) state)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path (.view (.val expression)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {fuel : Nat} {location : Loc} {start length : Nat}
    (evaluated : evalExpr fuel cfg env expression state = .ok (.slice location start length) intermediate)
    {initial frame : GIR.Frame} {point : Pt}
    (post : Post cfg env cx before initial (lowerExpr expression le before).2 frame point
      [((lowerExpr expression le before).1, .val (.slice location start length))])
    (bounded : map.Bounded (lowerExpr expression le before).2.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, intermediate⟩)
    (extended : ExtT (lowerView (.val expression) le before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame intermediate next nextFrame after) :
    ∃ child : ExprSource cfg env expression state, source.ExpressionChildAt child ∧
      GeneratedViewValueInstruction cfg.mod source.rootsEnv.access cx.fn required
        ⟨source.path ++ [0], .expression, .exit⟩ point
        (.def (lowerView (.val expression) le before).1 (.sliceView (lowerExpr expression le before).1)) ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        map.values map.runs ⟨point, frame, intermediate⟩ ∧
    ∃ sample, after = intermediate ∧ next = (point.1, point.2 + 1) ∧
      nextFrame = frame.set (lowerView (.val expression) le before).1 (.view sample) ∧
      evalView (fuel + 1) cfg env (.val expression) state = .ok sample after ∧
      Post cfg env cx before initial (lowerView (.val expression) le before).2 nextFrame next
        [((lowerView (.val expression) le before).1, .view sample)] ∧
      DemandUniformTraversal cx (fun runtime => map.Covers required ∧
        DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
          map.values map.runs runtime) 1 ⟨point, frame, intermediate⟩ ⟨next, nextFrame, after⟩ ∧
      ∀ aliases, source.rootsEnv.access.aliasView source.path (.val expression) = .ok aliases →
        (map.addRuns (lowerView (.val expression) le before).1 aliases).Realizes cfg.mod source.world env
          ⟨next, nextFrame, after⟩ := by
  have site : GeneratedViewValueInstruction cfg.mod source.rootsEnv.access cx.fn required
      ⟨source.path ++ [0], .expression, .exit⟩ point
      (.def (lowerView (.val expression) le before).1 (.sliceView (lowerExpr expression le before).1)) :=
    .sliceView occurrence rows post.pp extended
  have cell := post.has ((lowerExpr expression le before).1, .val (.slice location start length)) (by simp)
  obtain ⟨child, typing, roots, mutability, type, canonical⟩ := source.valChild
  have childResult := child.result fuel (.slice location start length) evaluated
  have childRealized : map.Realizes cfg.mod child.world env ⟨point, frame, intermediate⟩ := by
    simpa only [canonical.world] using realized
  refine ⟨child, canonical, site, ⟨⟨_, post.pp, post.rel⟩, childResult.frame, childRealized⟩, ?_⟩
  cases step with
  | define instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    obtain ⟨rfl, stateEq, done⟩ := view_value_runtime_reflection evaluated cell execution
    subst after
    let sample : ViewVal := ⟨location, start, length, false⟩
    let built := lowerView (.val expression) le before
    have emitted : emitDef (.sliceView (lowerExpr expression le before).1) le (lowerExpr expression le before).2 =
        (built.1, built.2) := by simp only [built, lowerView_val_run]
    obtain ⟨wholePost, _⟩ := Post.def_leaf post emitted extended (.view sample)
    obtain ⟨leafPost, _⟩ := Post.def_leaf (Post.init post.rel post.pp) emitted extended (.view sample)
    have carried : map.Realizes cfg.mod source.world env
        ⟨(point.1, point.2 + 1), frame.set built.1 (.view sample), intermediate⟩ :=
      realized.retained leafPost.same bounded.1 bounded.2 RetainsAliases.refl
    have result := source.result (fuel + 1) sample done
    have beforeFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
        intermediate source.context.outputFuture := by
      rw [← canonical.world, ← typing, ← roots, ← canonical.outputFuture]
      exact childResult.frame
    refine ⟨sample, rfl, rfl, rfl, done, wholePost,
      .next ⟨coverage, ⟨⟨_, post.pp, post.rel⟩, beforeFrame, realized⟩⟩ ?_
        (.done ⟨coverage, ⟨⟨_, wholePost.pp, wholePost.rel⟩, result.frame, carried⟩⟩), ?_⟩
    · intro targetFuel
      exact .definition site.instruction (by
        simp only [execOp, execPure, getVal_of cell, expectSlice, pure_bind, pure_apply])
    · intro aliases query
      exact result.extend_generated_runs query carried (wholePost.has (built.1, .view sample) (by simp))
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

end Goose.Lower
