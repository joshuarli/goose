import Goose.Lower.SourceContexts

namespace Goose.Lower

open Goose.Core Goose.Core.Sound Goose.Proofs.Memory

structure RangePlan {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {lo hi : Expr} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forRange x lo hi body origin) state) where
  intTy : IntTy
  binder : LocalVar
  lowerTypingStart : Nat
  lowerTypingEnd : Nat
  upperTypingEnd : Nat
  bodyTypingEnd : Nat
  bodyTy : Ty
  binderLocated : env.vars[x]? = some binder
  binderScope : binder.scope = body.scope
  binderTy : binder.ty = .int intTy
  lowerTyped : tyExpr source.typingEnv lo lowerTypingStart = .ok (.int intTy, lowerTypingEnd)
  upperTyped : tyExpr source.typingEnv hi lowerTypingEnd = .ok (.int intTy, upperTypingEnd)
  bodyTyped : tyBlock { { source.typingEnv with loops := source.typingEnv.loops + 1 }
    with visible := x :: source.typingEnv.visible } [] body upperTypingEnd =
      .ok (bodyTy, bodyTypingEnd)
  lowerRootsEnd : RState
  upperRootsEnd : RState
  bodyRootsEnd : RState
  lowerRoots : List RootRef
  upperRoots : List RootRef
  bodyRoots : List RootRef
  bodyRootRange : Nat × Nat
  binderReserved : x = source.rootsStart.nextVar
  lowerRooted : rpExpr source.rootsEnv lo
    { source.rootsStart with nextVar := source.rootsStart.nextVar + 1 } =
      .ok (lowerRoots, lowerRootsEnd)
  upperRooted : rpExpr source.rootsEnv hi lowerRootsEnd = .ok (upperRoots, upperRootsEnd)
  bodyRooted : rpBlockValue source.rootsEnv [] body upperRootsEnd =
    .ok ((bodyRoots, bodyRootRange), bodyRootsEnd)
  bodyEffects : EffLe bodyRootsEnd.eff source.world.E
  bodyEscape : ∀ y, RootRef.local y ∈ bodyRoots → ¬ (x ≤ y ∧ y < upperRootsEnd.nextVar)

private theorem forRangeTypingWitness {typingEnv typingAfter : TEnv} {scope : Nat}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId}
    {typingStart typingEnd : Nat}
    (typed : tyStmt typingEnv scope (.forRange x lo hi body origin) typingStart =
      .ok (typingAfter, typingEnd)) :
    ∃ (intTy : IntTy) (binder : LocalVar)
      (lowerTypingStart lowerTypingEnd upperTypingEnd bodyTypingEnd : Nat) (bodyTy : Ty),
    typingEnv.vars[x]? = some binder ∧ binder.scope = body.scope ∧ binder.ty = .int intTy ∧
    tyExpr typingEnv lo lowerTypingStart = .ok (.int intTy, lowerTypingEnd) ∧
    tyExpr typingEnv hi lowerTypingEnd = .ok (.int intTy, upperTypingEnd) ∧
    tyBlock { { typingEnv with loops := typingEnv.loops + 1 }
      with visible := x :: typingEnv.visible } [] body upperTypingEnd =
        .ok (bodyTy, bodyTypingEnd) := by
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, binder, lowerStart, declared, _, lowerEnd, lowerTyped, intTy, rfl,
    _, upperEnd, upperTyped, _, rfl, rfl, binderTy, bodyTy, bodyEnd, bodyTyped,
    rfl, rfl⟩ := typed
  obtain ⟨_, binderLocated, binderScope, _, _⟩ := declare_ok _ _ _ _ _ declared
  simp only at binderLocated binderScope
  refine ⟨intTy, binder, lowerStart, lowerEnd, upperEnd, typingEnd, bodyTy,
    binderLocated, binderScope, ?_, lowerTyped, upperTyped, bodyTyped⟩
  simpa using binderTy

private theorem forRangeRootWitness {rootsEnv : PEnv} {rootsStart rootsEnd : RState}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId} {E : Eff}
    (rooted : rpStmt rootsEnv (.forRange x lo hi body origin) rootsStart = .ok ((), rootsEnd))
    (effects : EffLe rootsEnd.eff E) :
    ∃ (lowerRootsEnd upperRootsEnd bodyRootsEnd : RState)
      (lowerRoots upperRoots bodyRoots : List RootRef) (bodyRootRange : Nat × Nat),
    x = rootsStart.nextVar ∧
    rpExpr rootsEnv lo { rootsStart with nextVar := rootsStart.nextVar + 1 } =
      .ok (lowerRoots, lowerRootsEnd) ∧
    rpExpr rootsEnv hi lowerRootsEnd = .ok (upperRoots, upperRootsEnd) ∧
    rpBlockValue rootsEnv [] body upperRootsEnd =
      .ok ((bodyRoots, bodyRootRange), bodyRootsEnd) ∧
    EffLe bodyRootsEnd.eff E ∧
    ∀ y, RootRef.local y ∈ bodyRoots → ¬ (x ≤ y ∧ y < upperRootsEnd.nextVar) := by
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨binderReserved, lowerRoots, lowerRootsEnd, lowerRooted, upperRoots,
    upperRootsEnd, upperRooted, bodyRoots, rangeStart, rangeEnd, bodyRootsEnd,
    bodyRooted, checked, rfl⟩ := rooted
  have rangeEq := rpBlockValue_rng _ _ _ _ _ _ _ bodyRooted
  simp only at rangeEq
  have binderEscapes : ∀ y, RootRef.local y ∈ bodyRoots →
      ¬ (rootsStart.nextVar ≤ y ∧ y < upperRootsEnd.nextVar) := by
    intro y member interval
    have checked := checkBlockValue_ok _ _ _ checked y member
    have interval' : rootsStart.nextVar ≤ y ∧ y < rangeStart := by
      rw [rangeEq]
      exact interval
    exact checked interval'
  refine ⟨lowerRootsEnd, upperRootsEnd, rootsEnd, lowerRoots, upperRoots,
    bodyRoots, (rangeStart, rangeEnd), binderReserved, by simpa using lowerRooted,
    upperRooted, bodyRooted, ?_, ?_⟩
  · exact effects
  · intro y member interval
    have interval' : rootsStart.nextVar ≤ y ∧ y < upperRootsEnd.nextVar := by
      simpa [binderReserved] using interval
    exact binderEscapes y member interval'

private theorem rangePlan_nonempty {cfg : Cfg} {env : Env} {state : St}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forRange x lo hi body origin) state) : Nonempty (RangePlan source) := by
  obtain ⟨intTy, binder, lowerTypingStart, lowerTypingEnd, upperTypingEnd, bodyTypingEnd,
    bodyTy, binderLocated, binderScope, binderTy, lowerTyped, upperTyped, bodyTyped⟩ :=
    forRangeTypingWitness source.typed
  rw [source.frame.vars_t] at binderLocated
  obtain ⟨lowerRootsEnd, upperRootsEnd, bodyRootsEnd, lowerRoots, upperRoots, bodyRoots,
    bodyRootRange, binderReserved, lowerRooted, upperRooted, bodyRooted, bodyEffects,
    bodyEscape⟩ := forRangeRootWitness (by simpa using source.rooted) source.effects
  exact ⟨{
    intTy, binder, lowerTypingStart, lowerTypingEnd, upperTypingEnd, bodyTypingEnd, bodyTy,
    binderLocated, binderScope, binderTy, lowerTyped, upperTyped, bodyTyped,
    lowerRootsEnd, upperRootsEnd, bodyRootsEnd, lowerRoots, upperRoots, bodyRoots,
    bodyRootRange, binderReserved, lowerRooted, upperRooted, bodyRooted, bodyEffects, bodyEscape }⟩

noncomputable def StmtSource.rangePlan {cfg : Cfg} {env : Env} {state : St}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forRange x lo hi body origin) state) : RangePlan source :=
  Classical.choice (rangePlan_nonempty source)

private theorem rangeUpperInputFrame {cfg : Cfg} {env : Env} {state : St}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId}
    {initial : St} {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    (ec : EvaluationContext cfg.mod source.plans source.path
      (.statement (.forRange x lo hi body origin)) .statement)
    (active : ec.ActiveMatches source.typingEnv)
    (lowerFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (ec.child rfl 0 (.expression lo) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (ec.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have childAtLo : (DemandNode.statement (.forRange x lo hi body origin)).child? 0 =
      some (.expression lo) := by simp [DemandNode.child?, DemandNode.children]
  have childAtHi : (DemandNode.statement (.forRange x lo hi body origin)).child? 1 =
      some (.expression hi) := by simp [DemandNode.child?, DemandNode.children]
  have phaseLo : DemandNodeHasPhase (.expression lo) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have phaseHi : DemandNodeHasPhase (.expression hi) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile current =>
    have activeFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state current := by
      change Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
        ((DemandNode.expression lo).visibleAfter
          ((DemandNode.statement (.forRange x lo hi body origin)).visibleForChild current 0)) at lowerFrame
      simpa [DemandNode.visibleForChild, DemandNode.visibleAfter] using lowerFrame
    have upperFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
        (hi.variables ++ current) := by
      apply activeFrame.changeFuture
      intro y visible _
      exact (active y).2 visible
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleForChild] using upperFrame
  | shrink profile context =>
    rename_i planContext
    let transitionLo := context.child rfl 0 (.expression lo) .expression childAtLo phaseLo
    let transitionHi := context.child rfl 1 (.expression hi) .expression childAtHi phaseHi
    have lowerExpectation : (DemandNode.statement (.forRange x lo hi body origin)).childExpectation?
        planContext.approvals.access ⟨source.path, .statement, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ 0 = some ⟨
            (DemandNode.statement (.forRange x lo hi body origin)).visibleForChild
              context.expected.frame.active 0,
            (hi.variables ++ body.variables) ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, childAtLo]
    have upperExpectation : (DemandNode.statement (.forRange x lo hi body origin)).childExpectation?
        planContext.approvals.access ⟨source.path, .statement, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ 1 = some ⟨
            (DemandNode.statement (.forRange x lo hi body origin)).visibleForChild
              context.expected.frame.active 1,
            body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, childAtHi]
    have lowerFuture := DemandNode.childFrame_future transitionLo.childFrameEq lowerExpectation
    have upperFuture := DemandNode.childFrame_future transitionHi.childFrameEq upperExpectation
    have lowerFutureEq : transitionLo.context.expected.frame.future =
        (hi.variables ++ body.variables) ++ context.expected.frame.future := by
      rw [transitionLo.expectedFrameEq, DemandNode.phaseFrame_future transitionLo.phaseFrameEq,
        lowerFuture]
      simp [DemandNode.phaseFuture]
    have upperFutureEq : transitionHi.context.expected.frame.future =
        body.variables ++ context.expected.frame.future := by
      rw [transitionHi.expectedFrameEq, DemandNode.phaseFrame_future transitionHi.phaseFrameEq,
        upperFuture]
      simp [DemandNode.phaseFuture]
    have lowerContext :
        ((EvaluationContext.shrink profile context).child rfl 0 (.expression lo) .expression
          childAtLo phaseLo) = .shrink profile transitionLo.context := rfl
    have upperContext :
        ((EvaluationContext.shrink profile context).child rfl 1 (.expression hi) .expression
          childAtHi phaseHi) = .shrink profile transitionHi.context := rfl
    rw [lowerContext] at lowerFrame
    change Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      transitionLo.context.expected.frame.future at lowerFrame
    rw [lowerFutureEq] at lowerFrame
    have frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
        (hi.variables ++ (body.variables ++ context.expected.frame.future)) := by
      simpa [List.append_assoc] using lowerFrame
    rw [upperContext]
    change Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (hi.variables ++ transitionHi.context.expected.frame.future)
    rw [upperFutureEq]
    exact frame

theorem RangePlan.lowerChild {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) state}
    (plan : RangePlan source) :
    ∃ lowerSource : ExprSource cfg env lo state,
      lowerSource.typingEnv = source.typingEnv ∧ lowerSource.rootsEnv = source.rootsEnv ∧
      lowerSource.ty = .int plan.intTy ∧ lowerSource.world = source.world ∧
      lowerSource.observation = source.observation ∧
      lowerSource.context.outputFuture = (source.context.child rfl 0 (.expression lo) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      lowerSource.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation ∧
      lowerSource.path = source.path ++ [0] ∧ lowerSource.plans = source.plans ∧
      HEq lowerSource.context (source.context.child rfl 0 (.expression lo) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])) := by
  let childAt : (DemandNode.statement (.forRange x lo hi body origin)).child? 0 =
      some (.expression lo) := by simp [DemandNode.child?, DemandNode.children]
  have effects : EffLe plan.lowerRootsEnd.eff source.world.E :=
    (rpExpr_mono plan.upperRooted).2.trans
      ((rpBlockValue_mono plan.bodyRooted).2.trans plan.bodyEffects)
  obtain ⟨lowerSource, typingEnv, rootsEnv, ty, world, observation, future, may,
    path, plans, context⟩ :=
    source.firstExpressionChildSource lo childAt
      (by simp [DemandNode.visibleForChild])
      (by intro y member; simp [Stmt.variables]; exact Or.inl member)
      (fun parent => hi.variables ++ body.variables ++ parent.future)
      (by
        intro parent y member
        simp [Stmt.variables, List.append_assoc, List.mem_append] at member ⊢
        rcases member with hhi | hrest
        · exact Or.inr (Or.inl hhi)
        · rcases hrest with hbody | hfuture
          · exact Or.inr (Or.inr (Or.inl hbody))
          · exact Or.inr (Or.inr (Or.inr hfuture)))
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
      plan.lowerTypingStart plan.lowerTypingEnd (.int plan.intTy)
      { source.rootsStart with nextVar := source.rootsStart.nextVar + 1 }
      plan.lowerRootsEnd plan.lowerRoots plan.lowerTyped plan.lowerRooted effects
  exact ⟨lowerSource, typingEnv, rootsEnv, ty, world, observation, future, may,
    path, plans, context⟩

theorem RangePlan.upperChild {cfg : Cfg} {env : Env} {initial after : St} {x : VarId}
    {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    (plan : RangePlan source) (lowerSource : ExprSource cfg env lo initial)
    (lowerMetadata : lowerSource.typingEnv = source.typingEnv ∧
      lowerSource.rootsEnv = source.rootsEnv ∧ lowerSource.ty = .int plan.intTy ∧
      lowerSource.world = source.world ∧ lowerSource.observation = source.observation ∧
      lowerSource.context.outputFuture = (source.context.child rfl 0 (.expression lo) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      lowerSource.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation ∧
      lowerSource.path = source.path ++ [0] ∧ lowerSource.plans = source.plans ∧
      HEq lowerSource.context (source.context.child rfl 0 (.expression lo) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])))
    { lower : Int }
    (result : ExprResult lowerSource (.int plan.intTy lower) after) :
    ∃ upperSource : ExprSource cfg env hi after,
      upperSource.typingEnv = source.typingEnv ∧ upperSource.rootsEnv = source.rootsEnv ∧
      upperSource.ty = .int plan.intTy ∧ upperSource.world = source.world ∧
      upperSource.observation = source.observation ∧
      upperSource.context.outputFuture = (source.context.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      upperSource.context.retained = (source.context.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).retained ∧
      upperSource.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation ∧
      upperSource.path = source.path ++ [1] ∧ upperSource.plans = source.plans ∧
      HEq upperSource.context (source.context.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])) := by
  rcases lowerMetadata with ⟨typingEnv, rootsEnv, type, world, observation, future,
    shrink, path, plans, context⟩
  have childAt : (DemandNode.statement (.forRange x lo hi body origin)).child? 1 =
      some (.expression hi) := by simp [DemandNode.child?, DemandNode.children]
  have lowerFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
      (source.context.child rfl 0 (.expression lo) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture := by
    have frame := result.frame
    rw [world, typingEnv, rootsEnv, future] at frame
    exact frame
  have observed : ObservedSafe cfg.mod source.world
      (source.context.mayShrink source.world.ownerP source.observation) source.observation after.store := by
    have observed := result.observed
    rw [world, observation, shrink] at observed
    exact observed
  have classified : cfg.mod.profile = .shrink →
      ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store := by
    intro profile
    have classified := result.classified profile
    rw [world, observation] at classified
    exact classified
  have effects : EffLe plan.upperRootsEnd.eff source.world.E :=
    (rpBlockValue_mono plan.bodyRooted).2.trans plan.bodyEffects
  obtain ⟨upperSource, upperTypingEnv, upperRootsEnv, upperType, upperWorld,
    upperObservation, upperFuture, upperRetained, upperShrink, upperPath, upperPlans,
    upperContext⟩ := source.expressionChildSource 1 hi childAt
      (by simp [DemandNode.visibleForChild]) plan.lowerTypingEnd plan.upperTypingEnd
      (.int plan.intTy) plan.lowerRootsEnd plan.upperRootsEnd plan.upperRoots
      plan.upperTyped plan.upperRooted effects
      (rangeUpperInputFrame source.context source.active lowerFrame) observed classified
  exact ⟨upperSource, upperTypingEnv, upperRootsEnv, upperType, upperWorld,
    upperObservation, upperFuture, upperRetained, upperShrink, upperPath, upperPlans,
    upperContext⟩

noncomputable def RangePlan.bodyContext {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) state}
    (_plan : RangePlan source) :
    EvaluationContext cfg.mod source.plans (source.path ++ [2]) (.block body) .block :=
  source.context.child rfl 2 (.block body) .block
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

theorem RangePlan.bodyFuture {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) state}
    (plan : RangePlan source) :
    plan.bodyContext.outputFuture = match source.context with
      | .pilot _ active =>
        (DemandNode.statement (.forRange x lo hi body origin)).visibleForChild active 2
      | .shrink _ context => context.expected.frame.active.filter body.variables.contains ++
          context.expected.frame.future := by
  cases hcontext : source.context with
  | pilot profile active =>
    simp [RangePlan.bodyContext, hcontext, EvaluationContext.child,
      EvaluationContext.outputFuture, DemandNode.visibleAfter]
  | shrink profile context =>
    rename_i planContext
    have childAt : (DemandNode.statement (.forRange x lo hi body origin)).child? 2 =
        some (.block body) := by simp [DemandNode.child?, DemandNode.children]
    have phase : DemandNodeHasPhase (.block body) .block := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let transition := context.child rfl 2 (.block body) .block childAt phase
    have expectation : (DemandNode.statement (.forRange x lo hi body origin)).childExpectation?
        planContext.approvals.access ⟨source.path, .statement, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ 2 = some ⟨
            (DemandNode.statement (.forRange x lo hi body origin)).visibleForChild
              context.expected.frame.active 2,
            context.expected.frame.active.filter body.variables.contains ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt]
    have future := DemandNode.childFrame_future transition.childFrameEq expectation
    simp only [RangePlan.bodyContext, hcontext, EvaluationContext.child]
    change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, future]
    simp [DemandNode.phaseFuture]

private theorem rangeBinderVisible (x : VarId) (active : List VarId) (y : VarId) :
    y ∈ x :: active ↔ y ∈ (if active.contains x then active else x :: active) := by
  by_cases member : x ∈ active
  · have contains : active.contains x = true := List.contains_iff_mem.mpr member
    simp only [contains, ite_true, List.mem_cons]
    constructor
    · rintro (equal | inside)
      · exact equal ▸ member
      · exact inside
    · exact Or.inr
  · have contains : active.contains x = false := by
      cases found : active.contains x <;> simp_all
    simp [member]

theorem RangePlan.bodyFuture_coversInput {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) state}
    (plan : RangePlan source) (y : VarId) (visible : y ∈ source.typingEnv.visible)
    (future : y ∈ body.variables ++ source.context.outputFuture) :
    y ∈ plan.bodyContext.outputFuture := by
  rw [plan.bodyFuture]
  have active := source.active
  cases contextAt : source.context with
  | pilot profile current =>
    rw [contextAt] at active
    change y ∈ (DemandNode.statement (.forRange x lo hi body origin)).visibleForChild current 2
    have binderVisible : y ∈ x :: current := by
      simp only [List.mem_cons]
      exact Or.inr ((active y).2 visible)
    simpa [DemandNode.visibleForChild] using (rangeBinderVisible x current y).mp binderVisible
  | shrink profile context =>
    rw [contextAt] at future active
    simp only [EvaluationContext.outputFuture, List.mem_append] at future
    rcases future with bodyMember | outerMember
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨(active y).2 visible,
        List.contains_iff_mem.mpr bodyMember⟩)
    · exact List.mem_append_right _ outerMember

private theorem rangeUpperOutputFrame {cfg : Cfg} {env : Env} {initial state : St}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    (active : source.context.ActiveMatches source.typingEnv)
    (frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (source.context.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (body.variables ++ source.context.outputFuture) := by
  have childAt : (DemandNode.statement (.forRange x lo hi body origin)).child? 1 =
      some (.expression hi) := by simp [DemandNode.child?, DemandNode.children]
  have phase : DemandNodeHasPhase (.expression hi) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec : source.context with
  | pilot profile visible =>
    rw [ec] at frame active
    have activeFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state visible := by
      change Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
        ((DemandNode.expression hi).visibleAfter
          ((DemandNode.statement (.forRange x lo hi body origin)).visibleForChild visible 1)) at frame
      simpa [DemandNode.visibleForChild, DemandNode.visibleAfter] using frame
    have wantedFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
        (body.variables ++ visible) := by
      apply activeFrame.changeFuture
      intro y isVisible _
      exact (active y).2 isVisible
    simpa [EvaluationContext.outputFuture, DemandNode.visibleAfter] using wantedFrame
  | shrink profile context =>
    rename_i planContext
    let transition := context.child rfl 1 (.expression hi) .expression childAt phase
    have expectation : (DemandNode.statement (.forRange x lo hi body origin)).childExpectation?
        planContext.approvals.access ⟨source.path, .statement, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ 1 = some ⟨
            (DemandNode.statement (.forRange x lo hi body origin)).visibleForChild
              context.expected.frame.active 1,
            body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt]
    have future := DemandNode.childFrame_future transition.childFrameEq expectation
    have futureEq : ((EvaluationContext.shrink profile context).child rfl 1
        (.expression hi) .expression childAt phase).outputFuture =
        body.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transition.context.expected.frame.future = body.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, future]
      simp [DemandNode.phaseFuture]
    rw [ec] at frame
    rw [futureEq] at frame
    exact frame

private theorem rangeBodyInputFrame {cfg : Cfg} {env : Env} {initial state : St} {x : VarId}
    {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    {plan : RangePlan source}
    (frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (body.variables ++ source.context.outputFuture)) :
    Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      plan.bodyContext.inputFuture := by
  have inputFuture : plan.bodyContext.inputFuture =
      body.variables ++ plan.bodyContext.outputFuture := by
    cases plan.bodyContext <;> rfl
  rw [inputFuture]
  apply frame.changeFuture
  intro y visible member
  rcases List.mem_append.mp member with bodyMember | futureMember
  · exact List.mem_append_left _ bodyMember
  · rw [plan.bodyFuture] at futureMember
    have activeMatch := source.active
    cases hcontext : source.context with
    | pilot profile active =>
      rw [hcontext] at activeMatch futureMember
      change y ∈ (DemandNode.statement (.forRange x lo hi body origin)).visibleForChild active 2 at futureMember
      exact List.mem_append_right _ ((activeMatch y).2 visible)
    | shrink profile context =>
      rw [hcontext] at futureMember
      simp only [List.mem_append, List.mem_filter,
        List.contains_iff_mem] at futureMember
      rcases futureMember with filtered | outer
      · exact List.mem_append_left _ filtered.2
      · exact List.mem_append_right _ outer

structure RangeLoopState {cfg : Cfg} {env : Env} {initial : St} {x : VarId}
    {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    (plan : RangePlan source) (state : St) : Prop where
  frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
    (body.variables ++ source.context.outputFuture)
  observed : ObservedSafe cfg.mod source.world
    (source.context.mayShrink source.world.ownerP source.observation) source.observation state.store
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod source.world.P source.world.D source.observation state.store

theorem RangePlan.afterUpper {cfg : Cfg} {env : Env} {initial boundState state : St}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    (plan : RangePlan source) (upperSource : ExprSource cfg env hi boundState)
    (upperMetadata : upperSource.typingEnv = source.typingEnv ∧
      upperSource.rootsEnv = source.rootsEnv ∧ upperSource.ty = .int plan.intTy ∧
      upperSource.world = source.world ∧ upperSource.observation = source.observation ∧
      upperSource.context.outputFuture = (source.context.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      upperSource.context.retained = (source.context.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).retained ∧
      upperSource.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation ∧
      upperSource.path = source.path ++ [1] ∧ upperSource.plans = source.plans ∧
      HEq upperSource.context (source.context.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])))
    { upper : Int }
    (result : ExprResult upperSource (.int plan.intTy upper) state) : RangeLoopState plan state := by
  rcases upperMetadata with ⟨typingEnv, rootsEnv, type, world, observation, outputFuture,
    retained, may, path, plans, context⟩
  have frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (source.context.child rfl 1 (.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture := by
    have frame := result.frame
    rw [world, typingEnv, rootsEnv, outputFuture] at frame
    exact frame
  have observed : ObservedSafe cfg.mod source.world
      (source.context.mayShrink source.world.ownerP source.observation) source.observation state.store := by
    have observed := result.observed
    rw [world, observation, may] at observed
    exact observed
  have classified : cfg.mod.profile = .shrink →
      ClassifiedParameters cfg.mod source.world.P source.world.D source.observation state.store := by
    intro profile
    have classified := result.classified profile
    rw [world, observation] at classified
    exact classified
  exact ⟨rangeUpperOutputFrame source.active frame, observed, classified⟩

theorem RangeLoopState.bodyChild {cfg : Cfg} {env : Env} {initial state : St}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    {plan : RangePlan source} (runtime : RangeLoopState plan state)
    {runtimeType : IntTy} (runtimeTypeEq : runtimeType = plan.intTy) (index : Int) :
    ∃ child : BlockSource cfg env [(x, .int runtimeType index)] body state,
      child.typingEnv = { source.typingEnv with loops := source.typingEnv.loops + 1 } ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧
      child.observation = source.observation ∧ child.plans = source.plans ∧
      child.path = source.path ++ [2] ∧
      child.context.outputFuture = plan.bodyContext.outputFuture ∧
      child.context.retained = plan.bodyContext.retained ∧
      child.context.mayShrink source.world.ownerP source.observation =
        plan.bodyContext.mayShrink source.world.ownerP source.observation ∧
      HEq child.context plan.bodyContext := by
  have binderIndex : x < plan.upperRootsEnd.nextVar := by
    have lowerGrowth := (rpExpr_mono plan.lowerRooted).1
    have upperGrowth := (rpExpr_mono plan.upperRooted).1
    calc
      x = source.rootsStart.nextVar := plan.binderReserved
      _ < source.rootsStart.nextVar + 1 := Nat.lt_succ_self _
      _ ≤ plan.lowerRootsEnd.nextVar := lowerGrowth
      _ ≤ plan.upperRootsEnd.nextVar := upperGrowth
  have flatValue : FlatTy (.int plan.intTy) (.int plan.intTy index) := rfl
  have active : ∀ inner next,
      declarePre { { { source.typingEnv with loops := source.typingEnv.loops + 1 }
        with visible := [x] ++ source.typingEnv.visible }
        with scopes := body.scope :: source.typingEnv.scopes } body.scope [] plan.upperTypingEnd =
        .ok (inner, next) → plan.bodyContext.ActiveMatches inner := by
    intro inner next declared
    obtain ⟨_, visible, _, _⟩ := declarePre_ok _ _ _ _ _ _ declared
    apply source.context.child_activeMatches rfl 2 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) source.typingEnv inner source.active
    intro y
    change y ∈ inner.visible ↔ y ∈
      (DemandNode.statement (.forRange x lo hi body origin)).visibleForChild
        source.typingEnv.visible 2
    rw [visible y]
    simpa [DemandNode.visibleForChild] using
      (rangeBinderVisible x source.typingEnv.visible y)
  have access : plan.bodyContext.AccessMatches
      { source.typingEnv with loops := source.typingEnv.loops + 1 } source.rootsEnv := by
    simpa [RangePlan.bodyContext, EvaluationContext.AccessMatches, NodeContext.AccessMatches] using
      (source.context.child_accessMatches_iff rfl 2 (.block body) .block
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) _ _).mpr source.access
  have may : plan.bodyContext.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl 2 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) source.world.ownerP source.observation root)
  have names : ([(x, .int runtimeType index)] : List (VarId × Val)).map Prod.fst = [x] := rfl
  have distinct : ([x] : List VarId).Nodup := by simp
  have frame := rangeBodyInputFrame (plan := plan) runtime.frame
  have frame := frame.tenv_congr
    (t2 := { source.typingEnv with loops := source.typingEnv.loops + 1 }) rfl rfl rfl (fun _ h => h)
  apply blockSource_reserved source.accepted plan.bodyContext
    [(x, .int runtimeType index)] [x] x active access (may ▸ source.protection)
    (may ▸ runtime.observed) runtime.classified source.permission frame plan.bodyTyped
    plan.bodyRooted plan.bodyEffects names distinct
  · intro variableId value member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    refine ⟨Nat.le_refl _, binderIndex, plan.binder, plan.binderLocated,
      plan.binderScope, ?_, ?_, ?_⟩
    · simp [plan.binderTy, Ty.paramOk, Ty.storable, Ty.isRefSlice]
    · rw [plan.binderTy, runtimeTypeEq]
      exact hasTy_of_flat flatValue (Or.inl rfl)
    · intro root target
      exact (flat_no_targets (P := fun _ => False) flatValue root target).elim
  · exact Nat.le_of_lt binderIndex
  · intro y member interval
    exact plan.bodyEscape y member interval

theorem RangeLoopState.afterBody {cfg : Cfg} {env : Env} {initial state after : St}
    {x : VarId} {lo hi : Expr} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    {plan : RangePlan source} (_runtime : RangeLoopState plan state)
    {runtimeType : IntTy} (_runtimeTypeEq : runtimeType = plan.intTy) {index : Int}
    (child : BlockSource cfg env [(x, .int runtimeType index)] body state)
    (typing : child.typingEnv = { source.typingEnv with loops := source.typingEnv.loops + 1 })
    (roots : child.rootsEnv = source.rootsEnv) (world : child.world = source.world)
    (observation : child.observation = source.observation)
    (future : child.context.outputFuture = plan.bodyContext.outputFuture)
    (_retained : child.context.retained = plan.bodyContext.retained)
    (may : child.context.mayShrink source.world.ownerP source.observation =
      plan.bodyContext.mayShrink source.world.ownerP source.observation)
    (fuel : Nat) (flow : Flow) (success : execBlock fuel cfg env
      [(x, .int runtimeType index)] body state = .ok flow after)
    (_normalOrContinue : flow = .cont ∨ ∃ value, flow = .normal value) :
    RangeLoopState plan after := by
  have result := child.result fuel flow success
  have frame := result.frame
  rw [typing, roots, world, future] at frame
  have parentFrame := frame.changeFuture (by
    intro y visible member
    exact plan.bodyFuture_coversInput y visible member)
  have nextFrame := parentFrame.tenv_congr
    (t2 := source.typingEnv) rfl rfl rfl (fun _ h => h)
  refine ⟨nextFrame, ?_, ?_⟩
  · have observed := result.observed
    rw [world, observation, may] at observed
    have bodyMay : plan.bodyContext.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
      funext root
      exact propext (source.context.child_mayShrink_iff rfl 2 (.block body) .block
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) source.world.ownerP source.observation root)
    exact bodyMay ▸ observed
  · simpa only [world, observation] using result.classified

end Goose.Lower
