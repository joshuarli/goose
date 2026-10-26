import Goose.Lower.DemandGeneratedScalarSources
import Goose.Lower.DemandExpressionCursor

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem ScalarExpression.owner_cursor {expression : Expr} (form : ScalarExpression expression)
    {cfg : Cfg} {env : Env} {state ownerState : St} {source : ExprSource cfg env expression state}
    {owner : ExprSource cfg env form.ownerExpression ownerState}
    (canonical : form.OwnerAt source owner) {map : RetainedSsaMap} {cx : FnCtx} {runtime : DemandRuntimePoint}
    (demanded : DemandFrameAt cfg env cx owner.world owner.typingEnv owner.rootsEnv (form.ownerFuture owner)
      map.values map.runs runtime) : CanonicalExpressionDemand map cx source runtime := by
  cases form with
  | literal | boolean =>
    obtain ⟨rfl, same⟩ := canonical
    have equal := eq_of_heq same
    cases equal
    exact .entry demanded
  | negate | unary | convert | binary | compare => exact .child canonical (.exit demanded)

theorem accepted_generated_scalar_runtime_step {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) {cfg : Cfg} {env : Env} {state intermediate after : St}
    (source : ExprSource cfg env expression state) {fuel : Nat}
    (evaluated : form.PrefixEvaluated inputs fuel cfg env state intermediate)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {required map : RetainedSsaMap} {point : Pt}
    (site : GeneratedScalarSite form cfg.mod source.rootsEnv.access cx.fn le root source.path before required point)
    (coverage : map.Covers required) {initial frame : GIR.Frame}
    (post : Post cfg env cx before initial (form.prefix le before) frame point (form.cells le before inputs))
    (bounded : map.Bounded (form.prefix le before).vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, intermediate⟩)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame intermediate next nextFrame after) :
    ∃ (ownerState : St) (owner : ExprSource cfg env form.ownerExpression ownerState),
      form.OwnerAt source owner ∧ owner.path = form.ownerPath source.path ∧ map.Covers required ∧
      DemandFrameAt cfg env cx owner.world owner.typingEnv owner.rootsEnv (form.ownerFuture owner)
        map.values map.runs ⟨point, frame, intermediate⟩ ∧
    ∃ value, form.compute cfg.profile inputs = .ok value ∧ after = intermediate ∧
      next = (point.1, point.2 + 1) ∧
      nextFrame = frame.set (lowerExpr expression le before).1 (.val value) ∧
      evalExpr (fuel + 1) cfg env expression state = .ok value after ∧
      ExpressionDemandBoundary source map cx before initial (lowerExpr expression le before).2
        (lowerExpr expression le before).1 value after next nextFrame := by
  obtain ⟨ownerState, owner, canonical, world, path, sourceFrame⟩ := form.canonical_owner inputs source evaluated
  have ownerRealized : map.Realizes cfg.mod owner.world env ⟨point, frame, intermediate⟩ := by
    simpa only [RetainedSsaMap.Realizes, world] using realized
  refine ⟨ownerState, owner, canonical, path, coverage, ⟨⟨_, post.pp, post.rel⟩, sourceFrame, ownerRealized⟩, ?_⟩
  cases step with
  | define instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    rw [form.instruction_decompose inputs post.rel.prof post.has] at execution
    cases computed : form.compute cfg.profile inputs with
    | error stop => simp only [computed] at execution; cases execution
    | ok value =>
      simp only [computed] at execution
      obtain ⟨rfl, rfl⟩ := Res.ok.inj execution
      have done : evalExpr (fuel + 1) cfg env expression state = .ok value intermediate := by
        rw [form.source_decompose inputs evaluated, computed]
        rfl
      have emitted : emitDef (form.operation le before) le (form.prefix le before) =
          ((emitDef (form.operation le before) le (form.prefix le before)).1,
            (emitDef (form.operation le before) le (form.prefix le before)).2) := rfl
      have extended : ExtT (emitDef (form.operation le before) le (form.prefix le before)).2 cx.fn.blocks := by
        simpa only [form.lower] using site.extended
      obtain ⟨whole, _⟩ := Post.def_leaf post emitted extended (.val value)
      obtain ⟨leaf, _⟩ := Post.def_leaf (Post.init post.rel post.pp) emitted extended (.val value)
      have finalPost : Post cfg env cx before initial (lowerExpr expression le before).2
          (frame.set (lowerExpr expression le before).1 (.val value)) (point.1, point.2 + 1)
          [((lowerExpr expression le before).1, .val value)] := by
        simpa only [form.lower] using whole
      have carried : map.Realizes cfg.mod source.world env
          ⟨(point.1, point.2 + 1), frame.set (lowerExpr expression le before).1 (.val value), intermediate⟩ := by
        simpa only [RetainedSsaMap.Realizes, form.lower] using
          realized.retained leaf.same bounded.1 bounded.2 RetainsAliases.refl
      have result := source.result (fuel + 1) value done
      refine ⟨value, rfl, rfl, rfl, rfl, done, finalPost,
        ⟨⟨_, finalPost.pp, finalPost.rel⟩, result.frame, carried⟩, ?_, ?_, ?_⟩
      · simpa only [form.lower] using bounded.mono leaf.mono
      · exact ValueAliasAt.of_post finalPost (v := value) (by simp) ⟨result.typed, result.rooted⟩
      · exact fun aliases query alias member => result.generated_value finalPost query member
  | effect instruction execution => cases site.instruction.symm.trans instruction
  | branch instruction read enter => cases site.instruction.symm.trans instruction
  | branchTrue instruction test read enter => cases site.instruction.symm.trans instruction
  | branchFalse instruction test read enter => cases site.instruction.symm.trans instruction

theorem accepted_generated_scalar_runtime_stop {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) {cfg : Cfg} {env : Env} {state intermediate after : St}
    (source : ExprSource cfg env expression state) {fuel : Nat}
    (evaluated : form.PrefixEvaluated inputs fuel cfg env state intermediate)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {required map : RetainedSsaMap} {point : Pt}
    (site : GeneratedScalarSite form cfg.mod source.rootsEnv.access cx.fn le root source.path before required point)
    (coverage : map.Covers required) {initial frame : GIR.Frame}
    (post : Post cfg env cx before initial (form.prefix le before) frame point (form.cells le before inputs))
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, intermediate⟩)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, intermediate⟩ stop after)
    (nonTimeout : stop ≠ .timeout) :
    map.Covers required ∧ map.Realizes cfg.mod source.world env ⟨point, frame, after⟩ ∧
      form.compute cfg.profile inputs = .error stop ∧ after = intermediate ∧
      evalExpr (fuel + 1) cfg env expression state = .stop stop after ∧
      DemandStoppedTraversal cx (CanonicalExpressionDemand map cx source) 0 targetFuel
        ⟨point, frame, intermediate⟩ stop after ∧
      ∃ (kind : NumAbort) (origin : OriginId), stop = .abort (AbortKind.ofNum kind) origin := by
  obtain ⟨ownerState, owner, canonical, world, path, sourceFrame⟩ := form.canonical_owner inputs source evaluated
  have cursor : CanonicalExpressionDemand map cx source ⟨point, frame, intermediate⟩ :=
    form.owner_cursor canonical ⟨⟨_, post.pp, post.rel⟩, sourceFrame, by simpa only [RetainedSsaMap.Realizes, world] using realized⟩
  cases stopped with
  | timeout => exact (nonTimeout rfl).elim
  | definition instruction execution =>
    have same := site.instruction.symm.trans instruction
    cases same
    rw [form.instruction_decompose inputs post.rel.prof post.has] at execution
    cases computed : form.compute cfg.profile inputs with
    | ok value => simp only [computed] at execution; cases execution
    | error actual =>
      simp only [computed] at execution
      obtain ⟨rfl, rfl⟩ := Res.stop.inj execution
      refine ⟨coverage, realized, rfl, rfl, ?_, ⟨_, .done _ cursor, ?_⟩,
        form.compute_error_numeric inputs cfg.profile computed⟩
      · rw [form.source_decompose inputs evaluated, computed]
        rfl
      · simpa only [Nat.sub_zero] using
          (DemandInstructionStop.definition site.instruction (by
            rw [form.instruction_decompose inputs post.rel.prof post.has, computed]))
  | effect instruction execution => cases site.instruction.symm.trans instruction

theorem accepted_generated_scalar_runtime_traversal {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) {cfg : Cfg} {env : Env} {state intermediate after : St}
    (source : ExprSource cfg env expression state) {fuel : Nat}
    (evaluated : form.PrefixEvaluated inputs fuel cfg env state intermediate)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {required map : RetainedSsaMap} {point : Pt}
    (site : GeneratedScalarSite form cfg.mod source.rootsEnv.access cx.fn le root source.path before required point)
    (coverage : map.Covers required) {initial frame : GIR.Frame}
    (post : Post cfg env cx before initial (form.prefix le before) frame point (form.cells le before inputs))
    (bounded : map.Bounded (form.prefix le before).vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, intermediate⟩)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Evidence.RuntimeStep cx.cfg cx.fn point frame intermediate next nextFrame after) (targetFuel : Nat) :
    DemandTraversal cx (CanonicalExpressionDemand map cx source) 1 (targetFuel + 1)
      ⟨point, frame, intermediate⟩ ⟨next, nextFrame, after⟩ := by
  obtain ⟨ownerState, owner, canonical, path, covered, ownerFrame, value, computed,
    stateEq, pointEq, frameEq, done, boundary⟩ :=
    accepted_generated_scalar_runtime_step form inputs source evaluated site coverage post bounded realized step
  have cursor := form.owner_cursor canonical ownerFrame
  refine .next cursor ?_ (.done targetFuel (.exit boundary.demanded))
  subst next nextFrame after
  exact .definition site.instruction (by rw [form.instruction_decompose inputs post.rel.prof post.has, computed])

end Goose.Lower
