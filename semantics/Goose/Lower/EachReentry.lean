import Goose.Lower.EachBodySource

namespace Goose.Lower

open Goose.Core Goose.Core.Sound Goose.Proofs.Memory

theorem EachLoopState.afterBody {cfg : Cfg} {env : Env} {initial state after : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    {plan : EachPlan source} {value : ViewVal} (runtime : EachLoopState plan value state)
    {pre : List (VarId × Val)} (blockSource : BlockSource cfg env pre body state)
    (typing : blockSource.typingEnv = { source.typingEnv with loops := source.typingEnv.loops + 1 })
    (roots : blockSource.rootsEnv = source.rootsEnv) (world : blockSource.world = source.world)
    (observation : blockSource.observation = source.observation)
    (future : blockSource.context.outputFuture = plan.bodyContext.outputFuture)
    (retained : blockSource.context.retained = plan.bodyContext.retained)
    (may : blockSource.context.mayShrink source.world.ownerP source.observation =
      plan.bodyContext.mayShrink source.world.ownerP source.observation)
    (fuel : Nat) (flow : Flow) (success : execBlock fuel cfg env pre body state = .ok flow after) :
    EachLoopState plan value after := by
  have result := blockSource.result fuel flow success
  have frame := result.frame
  rw [typing, roots, world, future] at frame
  have nextFrame := (frame.changeFuture (plan.bodyFuture_coversInput)).tenv_congr
    (t2 := source.typingEnv) rfl rfl rfl (fun _ h => h)
  have views : EachViewOk after.store value plan.element ∧
      ViewAliases cfg.mod source.world source.rootsEnv env after.store view value plan.element := by
    cases contextAt : source.context with
    | pilot profile active =>
      have monotone := result.pilotStore profile
      refine ⟨⟨runtime.typedView.1, fun fixed => (runtime.typedView.2.1 fixed).mono monotone, ?_⟩,
        ViewAliases.mono monotone runtime.aliases⟩
      intro resizable
      obtain ⟨start, owner⟩ := runtime.typedView.2.2 resizable
      exact ⟨start, owner.elim (fun h => Or.inl (LocTy.mono monotone h))
        (fun h => Or.inr (LocTy.mono monotone h))⟩
    | shrink profile context =>
      rename_i planContext
      let transition := context.child rfl 1 (.block body) .block
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      have access := source.access
      rw [contextAt] at access
      change planContext.approvals.access.mod = source.typingEnv.mod ∧
        planContext.approvals.access.impl.vars = source.typingEnv.vars ∧
        planContext.approvals.access.mod = source.rootsEnv.mod ∧
        planContext.approvals.access.impl = source.rootsEnv.impl ∧
        planContext.approvals.access.ctx = source.rootsEnv.ctx at access
      have accessAt : planContext.approvals.access = source.rootsEnv.access := by
        rcases access with ⟨_, _, moduleAt, implAt, ctxAt⟩
        cases accessAt : planContext.approvals.access
        rw [accessAt] at moduleAt implAt ctxAt
        simp only [AccessEnv.mk.injEq, PEnv.access]
        exact ⟨moduleAt, implAt, ctxAt⟩
      have child := transition.childFrameEq
      unfold DemandNode.childFrame at child
      cases expectedAt : (DemandNode.statement (.forEach x idx view byRef body origin)).childExpectation?
          planContext.approvals.access
          ⟨source.path, .expression, context.expected.frame.active,
            context.expected.frame.future, context.expected.frame.retained⟩ 1 with
      | none => simp [expectedAt, reject] at child
      | some expectation =>
        have aliasesAt : ∃ aliases,
            (DemandNode.statement (.forEach x idx view byRef body origin)).retainedForChild
              planContext.approvals.access source.path 1 = .ok aliases := by
          obtain ⟨aliases, sampled, _⟩ := (ex_bind_ok _ _ _).mp
            (show ((DemandNode.statement (.forEach x idx view byRef body origin)).retainedForChild
              planContext.approvals.access source.path 1 >>= fun aliases =>
                pure ⟨expectation.active, expectation.future, aliases ++ context.expected.frame.retained⟩) =
              .ok transition.childFrame from by simpa [expectedAt] using child)
          exact ⟨aliases, sampled⟩
        obtain ⟨aliases, sampled⟩ := aliasesAt
        have queryAt := sampled
        rw [accessAt] at queryAt
        obtain ⟨alias, singleton, query⟩ := forEach_retained_query_exists queryAt
        have member : alias ∈ aliases := by rw [singleton]; simp
        have kept := DemandNode.phaseFrame_retains transition.phaseFrameEq
          (DemandNode.childFrame_newAlias transition.childFrameEq sampled member)
        have bodyMember : alias ∈ plan.bodyContext.retained := by
          simp only [EachPlan.bodyContext, contextAt, EvaluationContext.child, EvaluationContext.retained]
          change alias ∈ transition.context.expected.frame.retained
          rw [transition.expectedFrameEq]
          exact kept
        have aliasPreserved := result.aliases alias (retained ▸ bodyMember)
        rw [world] at aliasPreserved
        exact eachViewAfterBody runtime.typedView runtime.aliases aliasPreserved query
  refine ⟨nextFrame, views.1, views.2, runtime.roots, ?_, ?_⟩
  · have observed := result.observed
    rw [world, observation, may] at observed
    have bodyMay : plan.bodyContext.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
      funext root
      exact propext (source.context.child_mayShrink_iff rfl 1 (.block body) .block
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) source.world.ownerP source.observation root)
    exact bodyMay ▸ observed
  · simpa only [world, observation] using result.classified

end Goose.Lower
