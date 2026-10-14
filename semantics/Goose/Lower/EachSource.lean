import Goose.Lower.SourceContexts
import Goose.Lower.EachTyped
import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.Core.Sound Goose.Proofs.Memory

private theorem eachView_input_subset {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forEach x idx view byRef body origin) state) :
    ∀ y, y ∈ (source.context.child rfl 0 (.view view) .view
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      y ∈ source.context.inputFuture := by
  have childAt : (DemandNode.statement (.forEach x idx view byRef body origin)).child? 0 =
      some (.view view) := by simp [DemandNode.child?, DemandNode.children]
  have phase : DemandNodeHasPhase (.view view) .view := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases hcontext : source.context with
  | pilot profile active =>
    intro y member
    simp only [EvaluationContext.child] at member ⊢
    change y ∈ view.variables ++
      (DemandNode.statement (.forEach x idx view byRef body origin)).visibleForChild active 0 at member
    simp only [DemandNode.visibleForChild] at member
    simp only [EvaluationContext.inputFuture, DemandNode.variables, Stmt.variables]
    change y ∈ (view.variables ++ body.variables) ++ active
    simp only [List.mem_append] at member ⊢
    exact member.elim (fun h => Or.inl (Or.inl h)) Or.inr
  | shrink profile context =>
    rename_i planContext
    let transition := context.child rfl 0 (.view view) .view childAt phase
    have expectation : (DemandNode.statement (.forEach x idx view byRef body origin)).childExpectation?
        planContext.approvals.access ⟨source.path, .statement, context.expected.frame.active, context.expected.frame.future,
          context.expected.frame.retained⟩ 0 = some ⟨
            (DemandNode.statement (.forEach x idx view byRef body origin)).visibleForChild
              context.expected.frame.active 0, body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt]
    have future := DemandNode.childFrame_future transition.childFrameEq expectation
    intro y member
    change y ∈ view.variables ++ transition.context.expected.frame.future at member
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, future] at member
    simp only [DemandNode.phaseFuture] at member
    simp only [EvaluationContext.inputFuture, NodeContext.inputFuture, DemandNode.variables, Stmt.variables]
    change y ∈ (view.variables ++ body.variables) ++ context.expected.frame.future
    simp only [List.mem_append] at member ⊢
    simpa only [or_assoc] using member

private theorem eachViewSource_at {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forEach x idx view byRef body origin) state)
    (typingStart typingEnd : Nat) (element : Ty) (mutable : Bool)
    (rootsStart rootsEnd : RState) (roots : List RootRef)
    (typed : tyView source.typingEnv view typingStart = .ok ((element, mutable), typingEnd))
    (rooted : rpView source.rootsEnv view rootsStart = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E) :
    ∃ child : ViewSource cfg env view state,
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.plans = source.plans ∧ child.path = source.path ++ [0] ∧
      child.element = element ∧ child.roots = roots ∧
      child.context.outputFuture = (source.context.child rfl 0 (.view view) .view
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation ∧ HEq child.context (source.context.child rfl 0 (.view view) .view
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])) := by
  have childAt : (DemandNode.statement (.forEach x idx view byRef body origin)).child? 0 =
      some (.view view) := by simp [DemandNode.child?, DemandNode.children]
  have phase : DemandNodeHasPhase (.view view) .view := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let child := source.context.child rfl 0 (.view view) .view childAt phase
  have may : child.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl 0 (.view view) .view childAt phase
      source.world.ownerP source.observation root)
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [0], context := child,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := typingStart, typingEnd := typingEnd,
    element := element, mutable := mutable, rootsStart := rootsStart, rootsEnd := rootsEnd, roots := roots,
    active := source.context.child_activeMatches rfl 0 (.view view) .view childAt phase
      source.typingEnv source.typingEnv source.active (by simp [DemandNode.visibleForChild]),
    access := (source.context.child_accessMatches_iff rfl 0 (.view view) .view childAt phase _ _).mpr source.access,
    protection := may ▸ source.protection, observed := may ▸ source.observed,
    classified := source.classified, permission := source.permission,
    frame := source.frame.narrowFuture (eachView_input_subset source),
    typed := typed, rooted := rooted, effects := effects },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, may, HEq.rfl⟩

theorem StmtSource.eachViewChild {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forEach x idx view byRef body origin) state) :
    ∃ child : ViewSource cfg env view state,
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.plans = source.plans ∧ child.path = source.path ++ [0] ∧
      HEq child.context (source.context.child rfl 0 (.view view) .view
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])) := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, lv, t0, hd, t1, hdi, element, mutable, t2, hview, t3, hloop, bt, t4,
    hbody, _, _⟩ := typed
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨hxi, roots, r1, hrootView, rooted⟩ := rooted
  have effects : EffLe r1.eff source.world.E := by
    rcases rooted with ⟨_, _, bodyRoots, l1, l2, r2, hrootBody, _, heq⟩ |
      ⟨_, r2, hreads, bodyRoots, l1, l2, r3, hrootBody, _, heq⟩
    · subst heq
      exact (rpBlockValue_mono hrootBody).2.trans source.effects
    · subst heq
      exact (PMono.addReads _ _ _ _ hreads).2.trans ((rpBlockValue_mono hrootBody).2.trans source.effects)
  obtain ⟨child, htyping, hroots, hworld, hobs, hplans, hpath, _, _, _, _, hcontext⟩ :=
    eachViewSource_at source t1 t2 element mutable _ r1 roots hview hrootView effects
  exact ⟨child, htyping, hroots, hworld, hobs, hplans, hpath, hcontext⟩

private theorem eachGam_scope {env : Env} {scope : Nat} {newScope : ScopeInst}
    {parameters : Nat → RootInst → Prop} {roots : List RootRef} {root : RootInst}
    (fresh : scope ∉ env.scopes.map Prod.fst) (related : Gam env parameters roots root) :
    Gam { env with scopes := (scope, newScope) :: env.scopes } parameters roots root := by
  obtain ⟨reference, member, interpreted⟩ := related
  refine ⟨reference, member, ?_⟩
  cases reference with
  | global index | param index => exact interpreted
  | «local» localId =>
    obtain ⟨localVar, scopeInstance, located, inScope, rfl⟩ := interpreted
    refine ⟨localVar, scopeInstance, located, ?_, rfl⟩
    have different : localVar.scope ≠ scope := fun equal => fresh (equal ▸ lookup_key inScope)
    simp only [lookup_cons, different, ite_false]
    exact inScope

theorem eachBlockSource_reserved {cfg : Cfg} {env : Env} {state : St}
    {plans : Array (Array DemandPoint)} {path : List Nat} {world : World}
    {typingEnv : TEnv} {rootsEnv : PEnv} {block : Block} {observation : Observation}
    {typingStart typingEnd : Nat} {ty : Ty} {rootsStart rootsEnd : RState}
    {roots : List RootRef} {range : Nat × Nat} (accepted : Core.validate cfg.mod = .ok ())
    (context : EvaluationContext cfg.mod plans path (.block block) .block)
    (pre : List (VarId × Val)) (binders : List VarId) (lowerBound : Nat)
    (active : ∀ inner next,
      declarePre { { typingEnv with visible := binders ++ typingEnv.visible }
        with scopes := block.scope :: typingEnv.scopes } block.scope [] typingStart = .ok (inner, next) →
      context.ActiveMatches inner)
    (access : context.AccessMatches typingEnv rootsEnv)
    (protection : ShrinkProtected world.D world.A (context.mayShrink world.ownerP observation))
    (observed : ObservedSafe cfg.mod world (context.mayShrink world.ownerP observation) observation state.store)
    (classified : cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod world.P world.D observation state.store)
    (permission : Perm cfg.mod world)
    (frame : Core.Sound.Frame cfg.mod world typingEnv rootsEnv env state context.inputFuture)
    (typed : tyBlock { typingEnv with visible := binders ++ typingEnv.visible } [] block typingStart =
      .ok (ty, typingEnd))
    (rooted : rpBlockValue rootsEnv [] block rootsStart = .ok ((roots, range), rootsEnd))
    (effects : EffLe rootsEnd.eff world.E) (binderNames : pre.map Prod.fst = binders)
    (distinct : binders.Nodup)
    (values : ∀ x v, (x, v) ∈ pre → lowerBound ≤ x ∧ x < rootsStart.nextVar ∧
      ∃ localVar, env.vars[x]? = some localVar ∧ localVar.scope = block.scope ∧
        localVar.ty.paramOk = true ∧ HasTy cfg.mod world.G state.store v localVar.ty ∧
        ∀ root, Targets v root → ∃ annotation, rootsEnv.ann x = some annotation ∧
          Gam env world.P annotation root ∧ (OwnerRefTy localVar.ty → Gam env world.ownerP annotation root))
    (bounded : lowerBound ≤ rootsStart.nextVar)
    (reservedEscape : ∀ y, RootRef.local y ∈ roots → ¬ (lowerBound ≤ y ∧ y < rootsStart.nextVar)) :
    ∃ source : BlockSource cfg env pre block state,
      source.typingEnv = typingEnv ∧ source.rootsEnv = rootsEnv ∧ source.world = world ∧
      source.observation = observation ∧ source.plans = plans ∧ source.path = path ∧
      HEq source.context context := by
  obtain ⟨sc, stmts, value⟩ := block
  obtain ⟨fresh, inner, next, after, finish, declared, typedStatements, typedValue⟩ :=
    tyBlock_ok _ _ _ _ _ _ _ _ typed
  obtain ⟨same, visible, _, _⟩ := declarePre_ok _ _ _ _ _ _ declared
  obtain ⟨_, middle, rootedStatements, rootedValue, escaped, _⟩ :=
    rpBlockValue_ok _ _ _ _ _ _ _ _ _ rooted
  have pretyped : PreOk cfg.mod world rootsEnv
      { env with scopes := (sc, state.nextScope) :: env.scopes } sc lowerBound
      (rootsStart.nextVar + ([] : List VarId).length) state.store pre := by
    refine ⟨binderNames ▸ distinct, ?_⟩
    intro x v member
    obtain ⟨lo, hi, localVar, located, scope, param, typedValue, rootedValue⟩ := values x v member
    refine ⟨lo, hi, localVar, located, scope, param, typedValue, ?_⟩
    intro root target
    obtain ⟨annotation, located, gam, owner⟩ := rootedValue root target
    exact ⟨annotation, located, eachGam_scope (frame.scopes_t ▸ fresh) gam,
      fun ownerType => eachGam_scope (frame.scopes_t ▸ fresh) (owner ownerType)⟩
  refine ⟨{
    accepted := accepted, plans := plans, path := path, context := context,
    observation := observation, world := world, typingEnv := typingEnv,
    typingInner := inner, typingAfter := after, rootsEnv := rootsEnv,
    typingStart := next, typingValue := finish, typingEnd := typingEnd, ty := ty,
    rootsStart := { rootsStart with nextVar := rootsStart.nextVar + ([] : List VarId).length },
    rootsValue := middle, rootsEnd := rootsEnd, roots := roots, lowerBound := lowerBound,
    active := active inner next declared, access := access, protection := protection,
    observed := observed, classified := classified, permission := permission, frame := frame,
    fresh := fresh, same := ?_, visible := ?_, pretyped := pretyped, bounded := bounded,
    typed := typedStatements, typedValue := ?_, rooted := rootedStatements, rootedValue := ?_,
    effects := effects, rootsEscape := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩
  · exact ⟨same.mod, same.impl, same.vars, same.loops, same.inExpr, same.scopes,
      fun x member => same.sub x (List.mem_append_right _ member)⟩
  · intro y
    rw [visible y, ← binderNames]
    simp
  · cases value with
    | none => exact typedValue.1
    | some expr => exact typedValue
  · cases value <;> exact rootedValue
  · intro y member interval
    by_cases reserved : y < rootsStart.nextVar
    · exact reservedEscape y member ⟨interval.1, reserved⟩
    · exact escaped y member ⟨Nat.le_of_not_lt reserved, interval.2⟩

theorem eachBlock_typed_sim {n : Nat} {cfg : Cfg} {env : Env} {state : St}
    {results : List Ty} {loop : LoopCtx} {pre : List (GIR.SlotId × GIR.ValueId × OriginId)}
    {pre' : List (VarId × Val)} {block : Core.Block}
    (source : BlockSource cfg env pre' block state)
    (simulation : TypedBlockLoopSimulation n cfg results (some loop) pre pre' false block)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (lexicalLoop : source.typingEnv.loops ≠ 0)
    (input output : LS) (result : GIR.ValueId) (pt : GIR.Pt) (cx : GIR.FnCtx) (frame : GIR.Frame)
    (lowered : lowerBlock (some loop) pre false block (lowerEnv cfg.mod env.vars results) input =
      (result, output))
    (point : input.pp = some pt) (extension : ExtT output cx.fn.blocks)
    (related : Rel cfg env cx frame input) (binders : PreRel frame pre pre')
    (module : cx.cfg.mod = lower cfg.mod) (returned : cx.fn.results = results)
    (depth : loop.depth = env.scopes.length) (targets : LoopTargets cx.fn loop)
    (counter : LoopCounterAt (some loop) input frame) :
    SimEAt cx pt frame (execBlock n cfg env pre' block >>= prepareReturn env)
      (LoopFlowPost cfg env cx input frame output loop block result) state := by
  have loops : LoopSourceMatches source.typingEnv (some loop) := by
    simp only [LoopSourceMatches, Option.some_ne_none]
    exact ⟨False.elim, lexicalLoop⟩
  have h := simulation env state source metadata loops input output result pt cx frame lowered
    point extension related binders module returned (Nat.le_of_eq depth) targets counter
  rw [prepareLoopFlow_at_depth env loop depth] at h
  refine h.mono fun flow _ pt' frame' _ post => ?_
  rcases post with ⟨value, hflow, _, normal⟩ | returned | ⟨context, same, abnormal⟩
  · exact Or.inl ⟨value, hflow, normal⟩
  · exact Or.inr (Or.inl returned)
  · cases same
    simpa [LoopFlowPost, depth] using (Or.inr (Or.inr abnormal) :
      (∃ value, flow = .normal value ∧ Post cfg env cx input frame output frame' pt'
        (blockCells block false result value)) ∨ ReturnedAt cx flow pt' frame' ∨
      (flow = .brk ∧ ExitedAt loop frame input.vals.size
        (env.scopes.drop (env.scopes.length - loop.depth)) pt' frame') ∨
      (flow = .cont ∧ ContinuedAt loop frame input.vals.size
        (env.scopes.drop (env.scopes.length - loop.depth)) pt' frame'))

structure EachPlan {cfg : Cfg} {env : Env} {state : St} {x : VarId} {idx : Option VarId}
    {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forEach x idx view byRef body origin) state) where
  element : Ty
  roots : List RootRef
  viewSource : ViewSource cfg env view state
  viewTyping : viewSource.typingEnv = source.typingEnv
  viewRoots : viewSource.rootsEnv = source.rootsEnv
  viewWorld : viewSource.world = source.world
  viewObservation : viewSource.observation = source.observation
  viewPlans : viewSource.plans = source.plans
  viewPath : viewSource.path = source.path ++ [0]
  viewElement : viewSource.element = element
  viewContext : HEq viewSource.context (source.context.child rfl 0 (.view view) .view
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]))
  viewFuture : viewSource.context.outputFuture = (source.context.child rfl 0 (.view view) .view
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture
  viewMay : viewSource.context.mayShrink source.world.ownerP source.observation =
    source.context.mayShrink source.world.ownerP source.observation
  viewRootValues : viewSource.roots = roots
  typingStart : Nat
  typingEnd : Nat
  bodyType : Ty
  rootsStart : RState
  rootsEnd : RState
  bodyRoots : List RootRef
  range : Nat × Nat
  binder : ∃ localVar, env.vars[x]? = some localVar ∧ localVar.scope = body.scope ∧
    localVar.ty.storable = true ∧
    (if byRef then (∃ mutability, localVar.ty = .ref mutability element) ∧
      bindRootsV source.rootsEnv (body.scope :: source.rootsEnv.scopes) x roots = .ok ()
      else localVar.ty = element)
  indexBinder : ∀ j, idx = some j → j = x + 1 ∧ ∃ localVar,
    env.vars[j]? = some localVar ∧ localVar.scope = body.scope ∧ localVar.ty = .int .i64
  reserved : x + idx.toList.length < rootsStart.nextVar
  typed : tyBlock { source.typingEnv with loops := source.typingEnv.loops + 1, visible := x :: idx.toList ++ source.typingEnv.visible } [] body typingStart = .ok (bodyType, typingEnd)
  rooted : rpBlockValue source.rootsEnv [] body rootsStart = .ok ((bodyRoots, range), rootsEnd)
  effects : EffLe rootsEnd.eff source.world.E
  escape : ∀ y, RootRef.local y ∈ bodyRoots → ¬ (x ≤ y ∧ y < rootsStart.nextVar)

theorem StmtSource.eachPlan {cfg : Cfg} {env : Env} {state : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forEach x idx view byRef body origin) state) :
    Nonempty (EachPlan source) := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨_, localVar, t0, declared, t1, declaredIndex, element, mutable, t2, typedView,
    t3, typedBinder, bodyType, t4, typedBody, _, _⟩ := typed
  obtain ⟨reservedX, roots, r1, rootedView, rootedBody⟩ := rooted
  obtain ⟨xStart, localAt, localScope, storable, nextStart⟩ := declare_ok _ _ _ _ _ declared
  simp only at localAt localScope storable nextStart
  rw [source.frame.vars_t] at localAt
  obtain ⟨_, declaredIndices⟩ := declareIndex_ok _ _ _ _ _ declaredIndex
  obtain ⟨_, binderType⟩ := loopVarOk_ok _ _ _ _ _ _ typedBinder
  have rootX : x = source.rootsStart.nextVar := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at reservedX
    exact reservedX.1
  have indices : ∀ j, idx = some j → j = x + 1 ∧ ∃ localVar,
      env.vars[j]? = some localVar ∧ localVar.scope = body.scope ∧ localVar.ty = .int .i64 := by
    intro j equal
    obtain ⟨afterX, localVar, located, inScope, typed⟩ := declaredIndices j equal
    rw [source.frame.vars_t] at located
    exact ⟨afterX.trans (nextStart.trans (congrArg (fun value => value + 1) xStart.symm)),
      localVar, located, inScope, typed⟩
  have reservedView : x + idx.toList.length < r1.nextVar := by
    have grew := (rpView_mono rootedView).1
    dsimp at grew
    exact lt_of_eq_of_lt (congrArg (fun value => value + idx.toList.length) rootX)
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_right (Nat.lt_succ_self _) _) grew)
  rcases rootedBody with ⟨byReference, bindRoots, bodyRoots, lo, hi, finish, bodyRooted, escapes, endEq⟩ |
    ⟨byValue, readState, reads, bodyRoots, lo, hi, finish, bodyRooted, escapes, endEq⟩
  · subst byReference
    subst endEq
    have effects : EffLe r1.eff source.world.E := (rpBlockValue_mono bodyRooted).2.trans source.effects
    obtain ⟨child, htyping, hroots, hworld, hobs, hplans, hpath, helement, hrootValues, hfuture, hmay, hcontext⟩ :=
      eachViewSource_at source t1 t2 element mutable _ r1 roots typedView rootedView effects
    have rangeAt := rpBlockValue_rng _ _ _ _ _ _ _ bodyRooted
    simp only at rangeAt
    refine ⟨{
      element := element, roots := roots, viewSource := child, viewTyping := htyping,
      viewRoots := hroots, viewWorld := hworld, viewObservation := hobs, viewPlans := hplans,
      viewPath := hpath, viewElement := helement, viewContext := hcontext, viewFuture := hfuture, viewMay := hmay,
      viewRootValues := ?_, typingStart := t3, typingEnd := t4, bodyType := bodyType,
      rootsStart := r1, rootsEnd := source.rootsEnd, bodyRoots := bodyRoots, range := (lo, hi),
      binder := ⟨localVar, localAt, localScope, storable, ?_⟩,
      indexBinder := indices, reserved := reservedView, typed := typedBody,
      rooted := bodyRooted, effects := source.effects, escape := ?_ }⟩
    · exact hrootValues
    · exact ⟨by simpa using binderType, bindRoots⟩
    · intro y member interval
      have outside := checkBlockValue_ok _ _ _ escapes y member
      exact outside ⟨Nat.le_trans (Nat.le_of_eq rootX.symm) interval.1,
        lt_of_lt_of_eq interval.2 rangeAt.symm⟩
  · have byValue' : byRef = false := by simpa using byValue
    subst byValue'
    subst endEq
    have effects : EffLe r1.eff source.world.E :=
      (PMono.addReads _ _ _ _ reads).2.trans ((rpBlockValue_mono bodyRooted).2.trans source.effects)
    obtain ⟨child, htyping, hroots, hworld, hobs, hplans, hpath, helement, hrootValues, hfuture, hmay, hcontext⟩ :=
      eachViewSource_at source t1 t2 element mutable _ r1 roots typedView rootedView effects
    have rangeAt := rpBlockValue_rng _ _ _ _ _ _ _ bodyRooted
    simp only at rangeAt
    have nextVar := (addReads_ok _ _ _ reads).1
    simp only at nextVar
    refine ⟨{
      element := element, roots := roots, viewSource := child, viewTyping := htyping,
      viewRoots := hroots, viewWorld := hworld, viewObservation := hobs, viewPlans := hplans,
      viewPath := hpath, viewElement := helement, viewContext := hcontext, viewFuture := hfuture, viewMay := hmay,
      viewRootValues := ?_, typingStart := t3, typingEnd := t4, bodyType := bodyType,
      rootsStart := readState, rootsEnd := source.rootsEnd, bodyRoots := bodyRoots, range := (lo, hi),
      binder := ⟨localVar, localAt, localScope, storable, ?_⟩,
      indexBinder := indices, reserved := ?_, typed := typedBody,
      rooted := bodyRooted, effects := source.effects, escape := ?_ }⟩
    · exact hrootValues
    · simpa using binderType
    · rw [nextVar]
      exact reservedView
    · intro y member interval
      have outside := checkBlockValue_ok _ _ _ escapes y member
      exact outside ⟨Nat.le_trans (Nat.le_of_eq rootX.symm) interval.1,
        lt_of_lt_of_eq interval.2 rangeAt.symm⟩

private theorem eachView_output_frame {cfg : Cfg} {env : Env} {state after : St} {x : VarId}
    {idx : Option VarId} {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.forEach x idx view byRef body origin) state)
    (frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
      (source.context.child rfl 0 (.view view) .view
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
      (body.variables ++ source.context.outputFuture) := by
  have childAt : (DemandNode.statement (.forEach x idx view byRef body origin)).child? 0 =
      some (.view view) := by simp [DemandNode.child?, DemandNode.children]
  have phase : DemandNodeHasPhase (.view view) .view := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have activeMatch := source.active
  cases hcontext : source.context with
  | pilot profile active =>
    rw [hcontext] at activeMatch frame
    have activeFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after active := by
      simpa [EvaluationContext.child, EvaluationContext.outputFuture,
        DemandNode.visibleAfter, DemandNode.visibleForChild] using frame
    have changed := activeFrame.changeFuture (future' := body.variables ++ active)
      (fun y visible _ => (activeMatch y).2 visible)
    simpa [EvaluationContext.outputFuture, DemandNode.visibleAfter] using changed
  | shrink profile context =>
    rename_i planContext
    let transition := context.child rfl 0 (.view view) .view childAt phase
    have expectation : (DemandNode.statement (.forEach x idx view byRef body origin)).childExpectation?
        planContext.approvals.access ⟨source.path, .statement, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ 0 = some ⟨
            (DemandNode.statement (.forEach x idx view byRef body origin)).visibleForChild
              context.expected.frame.active 0, body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt]
    have future := DemandNode.childFrame_future transition.childFrameEq expectation
    rw [hcontext] at frame
    change Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after
      transition.context.expected.frame.future at frame
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, future] at frame
    simpa [DemandNode.phaseFuture, EvaluationContext.outputFuture, NodeContext.outputFuture] using frame

structure EachLoopState {cfg : Cfg} {env : Env} {initial : St} {x : VarId} {idx : Option VarId}
    {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    (plan : EachPlan source) (value : ViewVal) (state : St) : Prop where
  frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
    (body.variables ++ source.context.outputFuture)
  typedView : EachViewOk state.store value plan.element
  aliases : ViewAliases cfg.mod source.world source.rootsEnv env state.store view value plan.element
  roots : Gam env source.world.P plan.roots value.loc.root
  observed : ObservedSafe cfg.mod source.world
    (source.context.mayShrink source.world.ownerP source.observation) source.observation state.store
  classified : cfg.mod.profile = .shrink →
    ClassifiedParameters cfg.mod source.world.P source.world.D source.observation state.store

theorem EachPlan.initial {cfg : Cfg} {env : Env} {initial state : St} {x : VarId} {idx : Option VarId}
    {view : View} {byRef : Bool} {body : Block} {origin : OriginId}
    {source : StmtSource cfg env (.forEach x idx view byRef body origin) initial}
    (plan : EachPlan source) (fuel : Nat) (value : ViewVal)
    (success : evalView fuel cfg env view initial = .ok value state) : EachLoopState plan value state := by
  have result := plan.viewSource.result fuel value success
  have frame := result.frame
  rw [plan.viewTyping, plan.viewRoots, plan.viewWorld, plan.viewFuture] at frame
  refine ⟨eachView_output_frame source frame, ?_, ?_, ?_, ?_, ?_⟩
  · have typed := result.typed.eachView
    simpa only [plan.viewElement] using typed
  · have aliases := result.viewAliases
    simpa only [plan.viewWorld, plan.viewRoots, plan.viewElement] using aliases
  · have roots := result.rooted
    simpa only [plan.viewWorld, plan.viewRootValues] using roots
  · have observed := result.observed
    simpa only [plan.viewWorld, plan.viewObservation, plan.viewMay] using observed
  · have classified := result.classified
    simpa only [plan.viewWorld, plan.viewObservation] using classified

end Goose.Lower
