import Goose.Lower.EachSource

namespace Goose.Lower

open Goose.Core Goose.Core.Sound Goose.Proofs.Memory

noncomputable def EachPlan.bodyContext {cfg : Cfg} {env : Env} {initial : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    (_plan : EachPlan source) :
    EvaluationContext cfg.mod source.plans (source.path ++ [1]) (.block body) .block :=
  source.context.child rfl 1 (.block body) .block
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private theorem eachBinders_visible (binders active : List VarId) (y : VarId) :
    y ∈ binders ++ active ↔ y ∈ binders.foldl
      (fun current binder => if current.contains binder then current else binder :: current) active := by
  induction binders generalizing active with
  | nil => simp
  | cons binder rest ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    by_cases contains : active.contains binder = true
    · have member := List.contains_iff_mem.mp contains
      simp only [contains, ite_true, List.mem_append, List.mem_cons]
      constructor
      · intro membership
        rcases membership with first | inside
        · rcases first with equal | inside
          · subst y
            exact Or.inr member
          · exact Or.inl inside
        · exact Or.inr inside
      · rintro (inside | inside)
        · exact Or.inl (Or.inr inside)
        · exact Or.inr inside
    · simp only [contains, Bool.false_eq_true, ite_false, List.mem_append, List.mem_cons]
      simp only [or_assoc, or_left_comm]

theorem EachPlan.bodyFuture {cfg : Cfg} {env : Env} {initial : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    (plan : EachPlan source) :
    plan.bodyContext.outputFuture = match source.context with
      | .pilot _ active =>
        (DemandNode.statement (.forEach x idx view byRef body origin)).visibleForChild active 1
      | .shrink _ context => context.expected.frame.active.filter body.variables.contains ++
          context.expected.frame.future := by
  cases hcontext : source.context with
  | pilot profile active =>
    simp [EachPlan.bodyContext, hcontext, EvaluationContext.child, EvaluationContext.outputFuture,
      DemandNode.visibleAfter]
  | shrink profile context =>
    rename_i planContext
    have childAt : (DemandNode.statement (.forEach x idx view byRef body origin)).child? 1 =
        some (.block body) := by simp [DemandNode.child?, DemandNode.children]
    have phase : DemandNodeHasPhase (.block body) .block := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let transition := context.child rfl 1 (.block body) .block childAt phase
    have expectation : (DemandNode.statement (.forEach x idx view byRef body origin)).childExpectation?
        planContext.approvals.access ⟨source.path, .statement, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ 1 = some ⟨
            (DemandNode.statement (.forEach x idx view byRef body origin)).visibleForChild
              context.expected.frame.active 1,
            context.expected.frame.active.filter body.variables.contains ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?,
        DemandNode.children, DemandNode.visibleForChild]
    have future := DemandNode.childFrame_future transition.childFrameEq expectation
    simp only [EachPlan.bodyContext, hcontext, EvaluationContext.child]
    change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, future]
    simp [DemandNode.phaseFuture]

theorem EachPlan.bodyFuture_coversInput {cfg : Cfg} {env : Env} {initial : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    (plan : EachPlan source) (y : VarId) (visible : y ∈ source.typingEnv.visible)
    (future : y ∈ body.variables ++ source.context.outputFuture) :
    y ∈ plan.bodyContext.outputFuture := by
  rw [plan.bodyFuture]
  have active := source.active
  cases contextAt : source.context with
  | pilot profile current =>
    rw [contextAt] at active
    change y ∈ (DemandNode.statement (.forEach x idx view byRef body origin)).visibleForChild current 1
    apply (eachBinders_visible (x :: idx.toList) current y).mp
    exact List.mem_append_right _ ((active y).2 visible)
  | shrink profile context =>
    rw [contextAt] at future active
    simp only [EvaluationContext.outputFuture, List.mem_append] at future
    rcases future with bodyMember | outerMember
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨(active y).2 visible, List.contains_iff_mem.mpr bodyMember⟩)
    · exact List.mem_append_right _ outerMember

private theorem eachBody_input_frame {cfg : Cfg} {env : Env} {initial state : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    {plan : EachPlan source} {value : ViewVal} (runtime : EachLoopState plan value state) :
    Core.Sound.Frame cfg.mod source.world
      { source.typingEnv with loops := source.typingEnv.loops + 1 }
      source.rootsEnv env state plan.bodyContext.inputFuture := by
  have outer := runtime.frame.tenv_congr
    (t2 := { source.typingEnv with loops := source.typingEnv.loops + 1 }) rfl rfl rfl (fun _ h => h)
  have inputFuture : plan.bodyContext.inputFuture = body.variables ++ plan.bodyContext.outputFuture := by
    cases plan.bodyContext <;> rfl
  rw [inputFuture]
  apply outer.changeFuture
  intro y visible member
  rcases List.mem_append.mp member with bodyMember | futureMember
  · exact List.mem_append_left _ bodyMember
  · rw [EachPlan.bodyFuture plan] at futureMember
    have activeMatch := source.active
    cases hcontext : source.context with
    | pilot profile active =>
      rw [hcontext] at activeMatch futureMember
      exact List.mem_append_right _ ((activeMatch y).2 visible)
    | shrink profile context =>
      rw [hcontext] at futureMember
      simp only [List.mem_append, List.mem_filter, List.contains_iff_mem] at futureMember
      exact futureMember.elim (fun h => List.mem_append_left _ h.2) (List.mem_append_right _)

private theorem eachBinder_value {cfg : Cfg} {env : Env} {initial state : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    {plan : EachPlan source} {value : ViewVal} (runtime : EachLoopState plan value state)
    (i : Nat) (element : Val)
    (location : LocTy state.store ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩ plan.element)
    (success : (if byRef then pure (Val.ref ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩)
      else readLoc ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩) state = .ok element state) :
    ∃ localVar, env.vars[x]? = some localVar ∧ localVar.scope = body.scope ∧
      localVar.ty.paramOk = true ∧ HasTy cfg.mod source.world.G state.store element localVar.ty ∧
      ∀ root, Targets element root → ∃ annotation, source.rootsEnv.ann x = some annotation ∧
        Gam env source.world.P annotation root ∧
        (OwnerRefTy localVar.ty → Gam env source.world.ownerP annotation root) := by
  obtain ⟨localVar, located, inScope, storable, binder⟩ := plan.binder
  have typed := (eachElement_success location success).2
  refine ⟨localVar, located, inScope, paramOk_of_storable storable, ?_, ?_⟩
  · cases byRef with
    | true =>
      simp only [ite_true] at binder typed
      obtain ⟨⟨mutability, refType⟩, _⟩ := binder
      rw [refType, typed]
      exact ⟨_, rfl, Or.inl ⟨flat_refTarget runtime.typedView.1,
        Or.inl location, HeaderLoc.ofFlat runtime.typedView.1⟩⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false] at binder typed
      rw [binder]
      exact hasTy_of_flat typed (Or.inl runtime.typedView.1)
  · intro root target
    cases byRef with
    | true =>
      simp only [ite_true] at binder typed
      obtain ⟨⟨mutability, refType⟩, bound⟩ := binder
      rw [typed] at target
      cases target
      obtain ⟨_, annotation, _, annotated, subset, _⟩ := bindRootsV_ok _ _ _ _ bound
      refine ⟨annotation, annotated, runtime.roots.subset subset, ?_⟩
      intro owner
      rw [refType] at owner
      rcases owner with ⟨otherMutability, target, equal | equal⟩
      all_goals
        have elementType := (Ty.ref.inj equal).2
        have flat := runtime.typedView.1
        rw [elementType] at flat
        simp [Ty.flat] at flat
    | false =>
      simp only [Bool.false_eq_true, ite_false] at typed
      exact (flat_no_targets (P := fun _ => False) typed root target).elim

theorem EachLoopState.bodySource {cfg : Cfg} {env : Env} {initial state elementState : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    {plan : EachPlan source} {value : ViewVal} (runtime : EachLoopState plan value state)
    (i : Nat) (element : Val)
    (location : LocTy state.store ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩ plan.element)
    (success : (if byRef then pure (Val.ref ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩)
      else readLoc ⟨value.loc.root, value.loc.path ++ [value.start + i]⟩) state = .ok element elementState) :
    ∃ blockSource : BlockSource cfg env (eachCorePre x idx element i) body elementState,
      blockSource.typingEnv = { source.typingEnv with loops := source.typingEnv.loops + 1 } ∧
      blockSource.rootsEnv = source.rootsEnv ∧ blockSource.world = source.world ∧
      blockSource.observation = source.observation ∧ blockSource.plans = source.plans ∧
      blockSource.path = source.path ++ [1] ∧
      blockSource.context.outputFuture = plan.bodyContext.outputFuture ∧
      blockSource.context.retained = plan.bodyContext.retained ∧
      blockSource.context.mayShrink source.world.ownerP source.observation =
        plan.bodyContext.mayShrink source.world.ownerP source.observation ∧
      HEq blockSource.context plan.bodyContext := by
  have unchanged := (eachElement_success location success).1
  subst elementState
  have values := eachBinder_value runtime i element location success
  have active : ∀ inner next,
      declarePre { { { source.typingEnv with loops := source.typingEnv.loops + 1 }
        with visible := (x :: idx.toList) ++ source.typingEnv.visible }
        with scopes := body.scope :: source.typingEnv.scopes } body.scope [] plan.typingStart =
        .ok (inner, next) → plan.bodyContext.ActiveMatches inner := by
    intro inner next declared
    obtain ⟨_, visible, _, _⟩ := declarePre_ok _ _ _ _ _ _ declared
    apply source.context.child_activeMatches rfl 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) source.typingEnv inner source.active
    intro y
    change y ∈ inner.visible ↔ y ∈ (DemandNode.statement (.forEach x idx view byRef body origin)).visibleForChild
      source.typingEnv.visible 1
    rw [visible y]
    simpa [DemandNode.visibleForChild] using eachBinders_visible (x :: idx.toList) source.typingEnv.visible y
  have access : plan.bodyContext.AccessMatches
      { source.typingEnv with loops := source.typingEnv.loops + 1 } source.rootsEnv := by
    simpa [EachPlan.bodyContext, EvaluationContext.AccessMatches, NodeContext.AccessMatches] using
      (source.context.child_accessMatches_iff rfl 1 (.block body) .block
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) _ _).mpr source.access
  have may : plan.bodyContext.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl 1 (.block body) .block
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) source.world.ownerP source.observation root)
  have names : (eachCorePre x idx element i).map Prod.fst = x :: idx.toList := by
    cases idx <;> rfl
  have distinct : (x :: idx.toList).Nodup := by
    cases idx with
    | none => simp
    | some j =>
      have afterX := (plan.indexBinder j rfl).1
      simp only [Option.toList_some, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      intro equal
      exact Nat.ne_of_lt (Nat.lt_succ_self x) (equal.trans afterX)
  apply eachBlockSource_reserved source.accepted plan.bodyContext (eachCorePre x idx element i)
    (x :: idx.toList) x active access (may ▸ source.protection) (may ▸ runtime.observed)
    runtime.classified source.permission (eachBody_input_frame runtime) plan.typed plan.rooted
    plan.effects names distinct
  · intro variableId variableValue member
    cases idx with
    | none =>
      simp only [eachCorePre, List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      exact ⟨Nat.le_refl _, Nat.lt_of_le_of_lt (Nat.le_add_right _ _) plan.reserved, values⟩
    | some j =>
      simp only [eachCorePre, List.mem_cons, List.not_mem_nil,
        or_false, Prod.mk.injEq] at member
      rcases member with first | second
      · obtain ⟨identified, valued⟩ := first
        subst variableId
        subst variableValue
        exact ⟨Nat.le_refl _, Nat.lt_of_le_of_lt (Nat.le_add_right _ _) plan.reserved, values⟩
      · obtain ⟨identified, valued⟩ := second
        subst variableId
        subst variableValue
        obtain ⟨afterX, localVar, located, inScope, typed⟩ := plan.indexBinder j rfl
        refine ⟨Nat.le_of_lt (lt_of_lt_of_eq (Nat.lt_succ_self x) afterX.symm), ?_,
          localVar, located, inScope, ?_, ?_, ?_⟩
        · exact lt_of_eq_of_lt afterX (by simpa using plan.reserved)
        · rw [typed]; rfl
        · rw [typed]
          exact hasTy_of_flat (show FlatTy (.int .i64) (.int .i64 i) from rfl) (Or.inl rfl)
        · intro root impossible
          exact impossible.elim
  · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) plan.reserved)
  · exact plan.escape

end Goose.Lower
