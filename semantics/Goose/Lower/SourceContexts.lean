import Goose.Lower.TypedExpressions

namespace Goose.Lower

open Goose.Core Goose.Proofs.Memory
open Goose.Core.Sound

structure StmtSource (cfg : Cfg) (env : Env) (stmt : Stmt) (state : St) where
  accepted : Core.validate cfg.mod = .ok ()
  plans : Array (Array DemandPoint)
  path : List Nat
  observation : Observation
  world : World
  typingEnv : TEnv
  typingAfter : TEnv
  rootsEnv : PEnv
  typingStart : Nat
  typingEnd : Nat
  rootsStart : RState
  rootsEnd : RState
  lowerBound : Nat
  scope : Nat
  context : EvaluationContext cfg.mod plans path (.statement stmt) .statement
  active : context.ActiveMatches typingEnv
  access : context.AccessMatches typingEnv rootsEnv
  protection : ShrinkProtected world.D world.A (context.mayShrink world.ownerP observation)
  observed : ObservedSafe cfg.mod world (context.mayShrink world.ownerP observation) observation state.store
  classified : cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod world.P world.D observation state.store
  permission : Perm cfg.mod world
  frame : Core.Sound.Frame cfg.mod world typingEnv rootsEnv env state context.inputFuture
  scopeHead : typingEnv.scopes.head? = some scope
  top : TopB env lowerBound rootsStart.nextVar state
  bounded : lowerBound ≤ rootsStart.nextVar
  typed : tyStmt typingEnv scope stmt typingStart = .ok (typingAfter, typingEnd)
  rooted : rpStmt rootsEnv stmt rootsStart = .ok ((), rootsEnd)
  effects : EffLe rootsEnd.eff world.E

structure StmtResult {cfg : Cfg} {env : Env} {stmt : Stmt} {state : St}
    (source : StmtSource cfg env stmt state) (flow : Flow) (after : St) : Prop where
  frame : Core.Sound.Frame cfg.mod source.world source.typingAfter source.rootsEnv env after source.context.outputFuture
  footprint : FootprintS env (Dset source.world) state after
  rootTypes : PreservesRootTypes cfg.mod source.world.G source.observation.roots state.store after.store
  values : PreservesValues cfg.mod source.world.G source.observation.values state.store after.store
  observed : ObservedSafe cfg.mod source.world (source.context.mayShrink source.world.ownerP source.observation) source.observation after.store
  aliases : RetainsAliases cfg.mod source.world env state.store after.store source.context.retained
  pilotStore : PilotStoreLe cfg.mod state after
  same : TSame source.typingEnv source.typingAfter
  top : TopB env source.lowerBound source.rootsEnd.nextVar after
  flow : match flow with
    | .normal _ => stmt.diverges cfg.mod.noReturn = false
    | .brk => source.typingEnv.loops ≠ 0 ∧ stmt.hasBreak = true
    | .cont => source.typingEnv.loops ≠ 0
    | .ret v => source.typingEnv.inExpr = false ∧ RetOk cfg.mod source.world source.typingEnv source.rootsEnv after v
  classified : cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store
  forbidden : PreservesForbiddenOwnerRoots (m := cfg.mod) (G := source.world.G) (env := env) (P := source.world.P) source.context.forbiddenOwners state after
  mutations : MutationFootprint env source.world.P source.world.base (effectMutationRoots cfg.mod source.rootsEnv.impl source.rootsEnd.eff) state after

theorem StmtSource.result {cfg : Cfg} {env : Env} {stmt : Stmt} {state after : St}
    (source : StmtSource cfg env stmt state) (fuel : Nat) (flow : Flow)
    (done : execStmt fuel cfg env stmt state = .ok flow after) : StmtResult source flow after := by
  have checked := (Core.Sound.specs_all (validate_modOk cfg.mod source.accepted)
    cfg.profile source.plans fuel).stmt source.path stmt source.context source.observation source.world source.typingEnv source.typingAfter source.rootsEnv env state source.scope source.typingStart source.typingEnd source.rootsStart source.rootsEnd source.lowerBound source.active source.access source.protection source.observed source.classified source.permission source.frame source.scopeHead source.top source.bounded source.typed source.rooted source.effects
  unfold Sat at checked
  rw [done] at checked
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := checked
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩

structure StmtsSource (cfg : Cfg) (env : Env) (stmts : List Stmt) (state : St) where
  accepted : Core.validate cfg.mod = .ok ()
  plans : Array (Array DemandPoint)
  path : List Nat
  observation : Observation
  world : World
  typingEnv : TEnv
  typingAfter : TEnv
  rootsEnv : PEnv
  typingStart : Nat
  typingEnd : Nat
  rootsStart : RState
  rootsEnd : RState
  lowerBound : Nat
  scope : Nat
  all : List Stmt
  value : Option Expr
  context : EvaluationContext cfg.mod plans path (.block (.mk scope all value)) .block
  offset : Nat
  offsetBounded : offset ≤ all.length
  suffix : stmts = all.drop offset
  active : ∀ x, x ∈ blockSuffixActive context offset ↔ x ∈ typingEnv.visible
  access : context.AccessMatches typingEnv rootsEnv
  protection : ShrinkProtected world.D world.A (context.mayShrink world.ownerP observation)
  observed : ObservedSafe cfg.mod world (context.mayShrink world.ownerP observation) observation state.store
  classified : cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod world.P world.D observation state.store
  permission : Perm cfg.mod world
  frame : Core.Sound.Frame cfg.mod world typingEnv rootsEnv env state (blockSuffixFuture context offset)
  scopeHead : typingEnv.scopes.head? = some scope
  top : TopB env lowerBound rootsStart.nextVar state
  bounded : lowerBound ≤ rootsStart.nextVar
  typed : tyStmts typingEnv scope stmts typingStart = .ok (typingAfter, typingEnd)
  rooted : rpStmts rootsEnv stmts rootsStart = .ok ((), rootsEnd)
  effects : EffLe rootsEnd.eff world.E

structure StmtsResult {cfg : Cfg} {env : Env} {stmts : List Stmt} {state : St}
    (source : StmtsSource cfg env stmts state) (flow : Flow) (after : St) : Prop where
  frame : ∃ typingFinal, TSame source.typingEnv typingFinal ∧
    Core.Sound.Frame cfg.mod source.world typingFinal source.rootsEnv env after (blockSuffixFuture source.context source.all.length) ∧
    (∀ v, flow = .normal v → typingFinal = source.typingAfter)
  footprint : FootprintS env (Dset source.world) state after
  rootTypes : PreservesRootTypes cfg.mod source.world.G source.observation.roots state.store after.store
  values : PreservesValues cfg.mod source.world.G source.observation.values state.store after.store
  observed : ObservedSafe cfg.mod source.world (source.context.mayShrink source.world.ownerP source.observation) source.observation after.store
  aliases : RetainsAliases cfg.mod source.world env state.store after.store source.context.retained
  pilotStore : PilotStoreLe cfg.mod state after
  top : TopB env source.lowerBound source.rootsEnd.nextVar after
  flow : match flow with
    | .normal v => v = .unit ∧ stmtsDiverge cfg.mod.noReturn stmts = false
    | .brk => source.typingEnv.loops ≠ 0 ∧ stmtsHaveBreak stmts = true
    | .cont => source.typingEnv.loops ≠ 0
    | .ret v => source.typingEnv.inExpr = false ∧ RetOk cfg.mod source.world source.typingEnv source.rootsEnv after v
  classified : cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store
  forbidden : PreservesForbiddenOwnerRoots (m := cfg.mod) (G := source.world.G) (env := env) (P := source.world.P) source.context.forbiddenOwners state after
  mutations : MutationFootprint env source.world.P source.world.base (effectMutationRoots cfg.mod source.rootsEnv.impl source.rootsEnd.eff) state after

theorem StmtsSource.result {cfg : Cfg} {env : Env} {stmts : List Stmt} {state after : St}
    (source : StmtsSource cfg env stmts state) (fuel : Nat) (flow : Flow)
    (done : execStmts fuel cfg env stmts state = .ok flow after) : StmtsResult source flow after := by
  have checked := (Core.Sound.specs_all (validate_modOk cfg.mod source.accepted)
    cfg.profile source.plans fuel).stmts source.path source.scope source.all source.value source.context source.offset stmts source.observation source.world source.typingEnv source.typingAfter source.rootsEnv env state source.typingStart source.typingEnd source.rootsStart source.rootsEnd source.lowerBound source.offsetBounded source.suffix source.active source.access source.protection source.observed source.classified source.permission source.frame source.scopeHead source.top source.bounded source.typed source.rooted source.effects
  unfold Sat at checked
  rw [done] at checked
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := checked
  cases flow <;> exact ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

variable {m : Module} {plans : Array (Array DemandPoint)}

theorem blockStmtChild? {sc : Nat} {all : List Stmt} {value : Option Expr}
    {offset : Nat} {st : Stmt} {rest : List Stmt}
    (hdrop : st :: rest = all.drop offset) :
    DemandNode.child? (.block (.mk sc all value)) offset = some (.statement st) := by
  have hget0 : (all.drop offset)[0]? = some st := by rw [← hdrop]; rfl
  rw [List.getElem?_drop] at hget0
  simp only [Nat.add_zero] at hget0
  have hbound : offset < all.length := (List.getElem?_eq_some_iff.mp hget0).choose
  have hbound' : offset < (all.map (some ∘ DemandNode.statement)).length := by
    simpa using hbound
  change ((all.map (some ∘ DemandNode.statement) ++
    [value.map DemandNode.expression])[offset]?).join = _
  rw [List.getElem?_append_left hbound']
  rw [List.getElem?_map, hget0]
  rfl

noncomputable def blockStmtContext {path : List Nat} {sc : Nat}
    {all : List Stmt} {value : Option Expr}
    (bc : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (offset : Nat) (st : Stmt)
    (hchild : DemandNode.child? (.block (.mk sc all value)) offset = some (.statement st)) :
    EvaluationContext m plans (path ++ [offset]) (.statement st) .statement :=
  bc.child rfl offset (.statement st) .statement hchild
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

theorem stmt_visibleAfter {tenv tenv' : TEnv} {sc tn tn' : Nat} {st : Stmt}
    (ht : tyStmt tenv sc st tn = .ok (tenv', tn')) :
    ∀ x, x ∈ tenv'.visible ↔ x ∈ (DemandNode.statement st).visibleAfter tenv.visible := by
  cases st with
  | resize owner size fill origin =>
    cases fill
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all [DemandNode.visibleAfter]
    all_goals try (split <;> simp_all)
  | ret value origin =>
    cases value
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all [DemandNode.visibleAfter]
    all_goals try (split <;> simp_all)
  | ifS condition yes no origin =>
    cases no
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all [DemandNode.visibleAfter]
    all_goals try (split <;> simp_all)
  | _ =>
    skip
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all [DemandNode.visibleAfter]
    all_goals try (split <;> simp_all)

theorem blockSuffixActive_succ {path sc all value offset st rest}
    (bc : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (hdrop : st :: rest = all.drop offset) :
    blockSuffixActive bc (offset + 1) =
      (DemandNode.statement st).visibleAfter (blockSuffixActive bc offset) := by
  have hget : all[offset]? = some st := by
    have h : (all.drop offset)[0]? = some st := by rw [← hdrop]; rfl
    simpa using h
  cases bc <;> simp only [blockSuffixActive, DemandNode.visibleForChild]
  all_goals rw [List.take_add_one, hget]; simp only [Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]; cases st <;> rfl

theorem blockStmt_shrinkFuture {path sc all value offset st rest}
    {pc : PlanContext m plans} (profile : m.profile = .shrink)
    (context : NodeContext pc path (.block (.mk sc all value)) .block)
    (hdrop : st :: rest = all.drop offset)
    (hchild : DemandNode.child? (.block (.mk sc all value)) offset = some (.statement st)) :
    (blockStmtContext (.shrink profile context) offset st hchild).outputFuture =
      rest.flatMap Stmt.variables ++ value.toList.flatMap Expr.variables ++ context.outputFuture := by
  have hphase : DemandNodeHasPhase (.statement st) .statement := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let transition := context.child rfl offset (.statement st) .statement hchild hphase
  have hbound : offset < all.length := by
    have hlen := congrArg List.length hdrop
    rw [List.length_drop] at hlen
    simp only [List.length_cons] at hlen
    omega
  have hrest : rest = all.drop (offset + 1) := by
    rw [List.drop_add_one_eq_tail_drop, ← hdrop]; rfl
  have hexpectation :
      (DemandNode.block (.mk sc all value)).childExpectation?
        pc.approvals.access
        ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
          context.expected.frame.retained⟩ offset =
        some ⟨(DemandNode.block (.mk sc all value)).visibleForChild context.expected.frame.active offset,
          rest.flatMap Stmt.variables ++ value.toList.flatMap Expr.variables ++ context.outputFuture⟩ := by
    simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild, hbound, hrest,
      NodeContext.outputFuture, List.append_assoc]

  have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
  change transition.context.expected.frame.future = _
  rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, hfuture]
  cases st <;> rfl


theorem StmtsSource.split {cfg : Cfg} {env : Env} {stmt : Stmt} {rest : List Stmt}
    {state : St} (source : StmtsSource cfg env (stmt :: rest) state) :
    ∃ head : StmtSource cfg env stmt state,
      head.typingEnv = source.typingEnv ∧ head.rootsEnv = source.rootsEnv ∧
      ∀ fuel value after, execStmt fuel cfg env stmt state = .ok (.normal value) after →
        ∃ tail : StmtsSource cfg env rest after,
          tail.typingEnv = head.typingAfter ∧ tail.rootsEnv = source.rootsEnv ∧
          tail.typingAfter = source.typingAfter := by
  rcases cfg with ⟨prof, m⟩
  rcases source with ⟨accepted, plans, path, observation, W, tenv, tenv', penv,
    tn, tn', rst, rst', lo, sc, all, value, bc, offset, hOffset, hDrop, hActive, hAccess,
    hProtected, hObserved, hClass, hp, hF, hsc, hT, hlo, ht, hr, hE⟩
  have hchild := blockStmtChild? (sc := sc) (value := value) hDrop
  let statementContext := blockStmtContext bc offset stmt hchild
  simp only [tyStmts] at ht; inv at ht
  simp only [rpStmts] at hr; inv at hr
  obtain ⟨tenv1, t1, hts, htr⟩ := ht
  obtain ⟨r1, hrs, hrr⟩ := hr
  have hm1 := rpStmt_mono hrs
  have hm2 := rpStmts_mono hrr
  have hrest : rest = all.drop (offset + 1) := by
    rw [List.drop_add_one_eq_tail_drop, ← hDrop]; rfl
  have hnextBound : offset + 1 ≤ all.length := by
    have hlen := congrArg List.length hDrop
    simp only [List.length_cons, List.length_drop] at hlen
    omega
  have hmay : statementContext.mayShrink W.ownerP observation = bc.mayShrink W.ownerP observation := by
    funext r
    exact propext (bc.child_mayShrink_iff rfl offset (.statement stmt) .statement hchild
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation r)
  have haccess : statementContext.AccessMatches tenv penv :=
    (bc.child_accessMatches_iff rfl offset (.statement stmt) .statement hchild
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv penv).2 hAccess
  have hactive : statementContext.ActiveMatches tenv := by
    cases bc with
    | pilot profile active => exact hActive
    | shrink profile context =>
      let transition := context.child rfl offset (.statement stmt) .statement hchild
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      change ∀ x, x ∈ transition.context.expected.frame.active ↔ x ∈ tenv.visible
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_active transition.phaseFrameEq,
        DemandNode.childFrame_active transition.childFrameEq]
      exact hActive
  have hinput : Frame m W tenv penv env state statementContext.inputFuture := by
    apply hF.changeFuture
    intro x hx hf
    cases bc with
    | pilot profile active => exact (hActive x).2 hx
    | shrink profile context =>
      have hout := blockStmt_shrinkFuture profile context hDrop hchild
      have hin : statementContext.inputFuture = stmt.variables ++ statementContext.outputFuture := rfl
      rw [hin, hout] at hf
      simpa [blockSuffixFuture, EvaluationContext.outputFuture, ← hDrop,
        List.flatMap_cons, List.append_assoc] using hf
  have hout : statementContext.outputFuture = blockSuffixFuture bc (offset + 1) := by
    cases bc with
    | pilot profile active =>
      change (DemandNode.statement stmt).visibleAfter (blockSuffixActive
        (EvaluationContext.pilot profile active : EvaluationContext m plans path (.block (.mk sc all value)) .block) offset) = _
      exact (blockSuffixActive_succ (EvaluationContext.pilot profile active :
        EvaluationContext m plans path (.block (.mk sc all value)) .block) hDrop).symm
    | shrink profile context =>
      simpa [blockSuffixFuture, EvaluationContext.outputFuture, ← hrest] using
        blockStmt_shrinkFuture profile context hDrop hchild
  let head : StmtSource ⟨prof, m⟩ env stmt state := {
    accepted := accepted, plans := plans, path := path ++ [offset], context := statementContext,
    observation := observation, world := W, typingEnv := tenv, typingAfter := tenv1,
    rootsEnv := penv, scope := sc, typingStart := tn, typingEnd := t1,
    rootsStart := rst, rootsEnd := r1, lowerBound := lo, active := hactive,
    access := haccess, protection := hmay ▸ hProtected, observed := hmay ▸ hObserved,
    classified := hClass, permission := hp, frame := hinput, scopeHead := hsc,
    top := hT, bounded := hlo, typed := hts, rooted := hrs, effects := hm2.2.trans hE }
  refine ⟨head, rfl, rfl, ?_⟩
  intro fuel runtimeValue after done
  have result := head.result fuel (.normal runtimeValue) done
  have hF1 := result.frame
  have hSafe1 := result.observed
  have hS1 : TSame tenv tenv1 := result.same
  have hT1 := result.top
  change Core.Sound.Frame m W tenv1 penv env after statementContext.outputFuture at hF1
  rw [hout] at hF1
  change ObservedSafe m W (statementContext.mayShrink W.ownerP observation) observation after.store at hSafe1
  rw [hmay] at hSafe1
  have hActive1 : ∀ x, x ∈ blockSuffixActive bc (offset + 1) ↔ x ∈ tenv1.visible := by
    rw [blockSuffixActive_succ bc hDrop]
    intro x
    have htvis := stmt_visibleAfter hts x
    cases stmt <;> simp only [DemandNode.visibleAfter] at htvis ⊢
    all_goals first
      | exact (hActive x).trans htvis.symm
      | (split <;> split at htvis <;> simp_all [List.contains_iff_mem])
  refine ⟨{
    accepted := accepted, plans := plans, path := path, observation := observation,
    world := W, typingEnv := tenv1, typingAfter := tenv', rootsEnv := penv,
    typingStart := t1, typingEnd := tn', rootsStart := r1, rootsEnd := rst', lowerBound := lo,
    scope := sc, all := all, value := value, context := bc, offset := offset + 1,
    offsetBounded := hnextBound, suffix := hrest, active := hActive1,
    access := ?_, protection := hProtected, observed := hSafe1, classified := result.classified,
    permission := hp, frame := hF1, scopeHead := ?_, top := hT1,
    bounded := Nat.le_trans hlo hm1.1, typed := htr, rooted := hrr, effects := hE }, rfl, rfl, rfl⟩
  · cases bc <;> simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches,
      hS1.mod, hS1.vars] using hAccess
  · rw [hS1.scopes]
    exact hsc

structure BlockSource (cfg : Cfg) (env : Env) (pre : List (VarId × Val)) (block : Block) (state : St) where
  accepted : Core.validate cfg.mod = .ok ()
  plans : Array (Array DemandPoint)
  path : List Nat
  context : EvaluationContext cfg.mod plans path (.block block) .block
  observation : Observation
  world : World
  typingEnv : TEnv
  typingInner : TEnv
  typingAfter : TEnv
  rootsEnv : PEnv
  typingStart : Nat
  typingValue : Nat
  typingEnd : Nat
  ty : Ty
  rootsStart : RState
  rootsValue : RState
  rootsEnd : RState
  roots : List RootRef
  lowerBound : Nat
  active : context.ActiveMatches typingInner
  access : context.AccessMatches typingEnv rootsEnv
  protection : ShrinkProtected world.D world.A (context.mayShrink world.ownerP observation)
  observed : ObservedSafe cfg.mod world (context.mayShrink world.ownerP observation) observation state.store
  classified : cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod world.P world.D observation state.store
  permission : Perm cfg.mod world
  frame : Core.Sound.Frame cfg.mod world typingEnv rootsEnv env state context.inputFuture
  fresh : block.scope ∉ typingEnv.scopes
  same : TSame { typingEnv with scopes := block.scope :: typingEnv.scopes } typingInner
  visible : ∀ y, y ∈ typingInner.visible ↔ y ∈ pre.map Prod.fst ∨ y ∈ typingEnv.visible
  pretyped : PreOk cfg.mod world rootsEnv { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.scope lowerBound rootsStart.nextVar state.store pre
  bounded : lowerBound ≤ rootsStart.nextVar
  typed : tyStmts typingInner block.scope block.stmts typingStart = .ok (typingAfter, typingValue)
  typedValue : match block.value with
    | none => ty = .unit
    | some expr => tyExpr typingAfter expr typingValue = .ok (ty, typingEnd)
  rooted : rpStmts { rootsEnv with scopes := block.scope :: rootsEnv.scopes } block.stmts rootsStart = .ok ((), rootsValue)
  rootedValue : match block.value with
    | none => roots = [] ∧ rootsEnd = rootsValue
    | some expr => rpExpr { rootsEnv with scopes := block.scope :: rootsEnv.scopes } expr rootsValue = .ok (roots, rootsEnd)
  effects : EffLe rootsEnd.eff world.E
  rootsEscape : ∀ y, RootRef.local y ∈ roots → ¬ (lowerBound ≤ y ∧ y < rootsEnd.nextVar)

theorem BlockSource.enter {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Block} {state : St} (source : BlockSource cfg env pre block state) :
    ∃ statements : StmtsSource cfg
        { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store },
      statements.typingEnv = source.typingInner ∧
      statements.typingAfter = source.typingAfter ∧
      statements.rootsEnv = { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes } := by
  rcases cfg with ⟨prof, m⟩
  rcases block with ⟨sc, stmts, value⟩
  rcases source with ⟨accepted, plans, path, bc, observation, W, tenv, tenv1, tenv2,
    penv, tn1, tn2, tn3, ty, rst1, rst2, rst3, rho, lo,
    hActive, hAccess, hProtected, hObserved, hClass, hp, hF, hsc, hsame, hvis,
    hpre, hlo, hts, htv, hrs, hrv, hE, hkeep⟩
  have hF0 := hF.push hsc
  have hfreshAll : ∀ x, state.store.roots[RootInst.local env.act state.nextScope x]? = none := fun x => by
    cases h : state.store.roots[RootInst.local env.act state.nextScope x]? with
    | none => rfl
    | some v => exact absurd (hF.inv.fresh _ _ _ (by rw [h]; simp)) (Nat.lt_irrefl _)
  obtain ⟨hnd, hpreAll⟩ := hpre
  obtain ⟨tfin, hFb, hSb, hvisb, hleb, hkeepb, hbackb⟩ :=
    frame_pre (future := bc.inputFuture) (penv := { penv with scopes := sc :: penv.scopes })
      (env := { env with scopes := (sc, state.nextScope) :: env.scopes }) (rest0 := env.scopes)
      rfl pre _ { state with nextScope := state.nextScope + 1 } hF0 hnd (by
        intro x v hm
        obtain ⟨_, _, lv, g1, g2, g3, g4, g5⟩ := hpreAll x v hm
        refine ⟨hfreshAll x, lv, g1, g2, g3, g4, ?_, ?_⟩
        · intro r hr
          obtain ⟨ann, ha, hg, _⟩ := g5 r hr
          refine ⟨⟨ann, ha, hg⟩, ?_⟩
          rcases hasTy_target_dom g4 hr with ⟨g, rfl⟩ | hd
          · trivial
          · cases r with
            | global g => trivial
            | «local» a si' x' => exact Nat.le_of_lt (hF.inv.fresh _ _ _ hd)
        · intro hty r hr
          obtain ⟨ann, ha, _, howner⟩ := g5 r hr
          exact ⟨ann, ha, howner hty⟩)
  have hF1 := hFb.tenv_congr (t2 := tenv1) (hsame.mod.trans hSb.mod.symm)
    (hsame.vars.trans hSb.vars.symm) (hsame.scopes.trans hSb.scopes.symm)
    (fun y hy => (hvisb y).2 ((hvis y).1 hy))
  have hTop : TopB { env with scopes := (sc, state.nextScope) :: env.scopes } lo rst1.nextVar
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } := by
    intro sc' si' rest' he y hy
    cases he
    cases hv : (preStore env.act state.nextScope pre state.store).roots[RootInst.local env.act state.nextScope y]? with
    | none => exact absurd hv hy
    | some v' =>
      rcases hbackb _ v' hv with h0 | ⟨x, hx, e⟩
      · have := hfreshAll y
        rw [this] at h0; cases h0
      · cases e
        obtain ⟨⟨x', v''⟩, hm, rfl⟩ := List.mem_map.1 hx
        obtain ⟨g1, g2, _⟩ := hpreAll _ _ hm
        exact ⟨g1, g2⟩
  have hE2 : EffLe rst2.eff W.E := by
    cases value with
    | none => rw [← hrv.2]; exact hE
    | some e => exact (rpExpr_mono hrv).2.trans hE
  let inner := { env with scopes := (sc, state.nextScope) :: env.scopes }
  let bound := { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }
  have hPreFoot : FootprintS inner (Dset W) { state with nextScope := state.nextScope + 1 } bound := by
    refine ⟨Nat.le_refl _, fun r v hv _ _ _ => hkeepb r v hv, ?_, ?_⟩
    · intro r v hv hr hn hd
      rcases hbackb r v hv with h0 | ⟨x, hx, rfl⟩
      · exact h0
      · exact False.elim (hn env.act state.nextScope x rfl (by simp [inner, insts]))
    · intro r hr
      cases hv : bound.store.roots[r]? with
      | none => exact False.elim (hr hv)
      | some v =>
        rcases hbackb r v hv with h0 | ⟨x, hx, rfl⟩
        · exact Or.inl (by rw [h0]; simp)
        · obtain ⟨⟨x', v'⟩, hm, hfst⟩ := List.mem_map.1 hx
          simp only at hfst
          subst x'
          obtain ⟨_, _, lv, hlv, hlsc, _⟩ := hpreAll _ _ hm
          exact Or.inr ⟨x, lv, state.nextScope, env.scopes, by simp [inner, hlsc, Block.scope], hlv, rfl⟩
  have hSafeB : ObservedSafe m W (bc.mayShrink W.ownerP observation) observation bound.store := by
    refine { hObserved with typed := ⟨?_, ?_⟩, rootsProtected := ?_ }
    · intro r T hobs
      obtain ⟨v, hv, hty⟩ := hObserved.typed.roots r T hobs
      exact ⟨v, hkeepb r v hv, hty.mono hleb⟩
    · intro v T hobs
      exact (hObserved.typed.values v T hobs).mono hleb
    · intro r T v hobs hv hi target ht
      rcases hbackb r v hv with hv0 | ⟨x, _, hr⟩
      · exact hObserved.rootsProtected r T v hobs hv0 hi target ht
      · have hbefore := hObserved.rootsOlder r T hobs
        rw [hr] at hbefore
        exact False.elim ((Nat.not_lt_of_ge hF.base_le) hbefore)
  have hStart : Frame m W tenv1 { penv with scopes := sc :: penv.scopes } inner bound
      (blockSuffixFuture bc 0) := by
    apply hF1.narrowFuture
    intro x hx
    apply List.mem_append_right
    cases bc with
    | pilot profile active =>
      apply List.mem_append_right
      simpa [blockSuffixFuture, blockSuffixActive, DemandNode.visibleForChild] using hx
    | shrink profile context =>
      cases value <;> simpa [blockSuffixFuture, EvaluationContext.inputFuture,
        EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture,
        DemandNode.variables, Block.variables, List.append_assoc] using hx
  have hClassBound : m.profile = .shrink → ClassifiedParameters m W.P W.D observation bound.store := by
    intro hshrink
    exact ClassifiedParameters.advanceS (s := { state with nextScope := state.nextScope + 1 })
      (hClass hshrink) hF0 hPreFoot
  refine ⟨{
    accepted := accepted, plans := plans, path := path, observation := observation, world := W,
    typingEnv := tenv1, typingAfter := tenv2, rootsEnv := { penv with scopes := sc :: penv.scopes },
    typingStart := tn1, typingEnd := tn2, rootsStart := rst1, rootsEnd := rst2, lowerBound := lo,
    scope := sc, all := stmts, value := value, context := bc, offset := 0,
    offsetBounded := Nat.zero_le _, suffix := rfl, active := ?_, access := ?_,
    protection := hProtected, observed := hSafeB, classified := hClassBound, permission := hp,
    frame := hStart, scopeHead := ?_, top := hTop, bounded := hlo,
    typed := hts, rooted := hrs, effects := hE2 }, rfl, rfl, rfl⟩
  · cases bc <;> simpa [blockSuffixActive, DemandNode.visibleForChild,
      EvaluationContext.ActiveMatches, NodeContext.ActiveMatches, DemandExpectedPoint.toPoint,
      DemandPoint.ActiveMatches] using hActive
  · cases bc <;> simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches,
      hsame.mod, hsame.vars] using hAccess
  · rw [hsame.scopes]
    rfl

def InitialWorld (globals base : Nat) (effects : Eff) : World :=
  ⟨globals, fun _ _ => False, fun _ _ => False, effects, base,
    fun _ _ => False, fun _ _ => False⟩

theorem initialFrame {m : Module} {state : St} {globals : Nat} {effects : Eff}
    (invariant : StoreInv m globals state) (future : List VarId)
    (typing : TEnv) (roots : PEnv)
    (typingModule : typing.mod = m) (rootsModule : roots.mod = m)
    (typingVars : typing.vars = #[]) (rootsVars : roots.impl.vars = #[])
    (typingScopes : typing.scopes = []) (rootsScopes : roots.scopes = [])
    (typingVisible : typing.visible = []) (rootsContents : ∀ x, roots.cont x = none) :
    Core.Sound.Frame m (InitialWorld globals state.nextScope effects) typing roots noEnv state future := by
  refine {
    mod_t := typingModule, mod_p := rootsModule, vars_t := typingVars, vars_p := rootsVars,
    scopes_t := typingScopes, scopes_p := rootsScopes, nodup := List.nodup_nil,
    sorted := List.Pairwise.nil, below := ?_, base_le := Nat.le_refl _,
    ownerSubset := ?_, ownerShape := ?_, pAge := ?_, vis := ?_, bindings := ?_,
    storage := ?_, rooted := ?_, rootedOwners := ?_, inv := ?_,
    aOlder := ?_, dOut := ?_, dFun := ?_, sa := ?_, pref := ?_ }
  · intro pair member
    cases member
  · intro i r impossible
    exact impossible.elim
  · intro i r impossible
    exact impossible.elim
  · intro i a si x impossible
    exact impossible.elim
  · intro x member
    rw [typingVisible] at member
    cases member
  · intro x member
    rw [typingVisible] at member
    cases member
  · rintro r T ⟨x, lv, si, present, _, _⟩
    simp [noEnv] at present
  · intro x lv si v present
    simp [noEnv] at present
  · intro x lv si v present
    simp [noEnv] at present
  · exact invariant.changeDemand (fun _ _ => Or.inl trivial)
  · intro r t impossible
    exact impossible.elim
  · intro r E impossible
    exact impossible.elim
  · intro r E E' impossible
    exact impossible.elim
  · intro r E impossible
    exact impossible.elim
  · intro x cont present
    rw [rootsContents x] at present
    cases present

theorem acceptedGlobalSource {cfg : Cfg} {state : St} {g : GlobalId} {global : Global}
    (accepted : Core.validate cfg.mod = .ok ())
    (globalAt : cfg.mod.globals[g]? = some global)
    (invariant : StoreInv cfg.mod g state) :
    ∃ source : ExprSource cfg noEnv global.init state,
      source.typingEnv = initEnv cfg.mod g ∧
      source.rootsEnv = ⟨cfg.mod, initImpl, initContext, []⟩ ∧ source.ty = global.ty := by
  have moduleOk := validate_modOk cfg.mod accepted
  obtain ⟨plans, derived, wellFormed⟩ := moduleOk.demandPlans
  have globalOk := moduleOk.glob g global globalAt
  obtain ⟨tn, typed⟩ := globalOk.init
  obtain ⟨rho, rst, rooted, unknown, allowed⟩ := globalOk.roots
  let context := EvaluationContext.forGlobal derived wellFormed globalAt
  let world := InitialWorld g state.nextScope rst.eff
  have permission : Perm cfg.mod world := by
    refine Or.inr ⟨unknown, ?_⟩
    intro target member
    cases target with
    | global h => exact allowed (.global h) member h rfl
    | param i => intro r impossible; exact impossible.elim
  refine ⟨{
    accepted := accepted, plans := plans, path := [], context := context,
    observation := Observation.empty, world := world, typingEnv := initEnv cfg.mod g,
    rootsEnv := ⟨cfg.mod, initImpl, initContext, []⟩,
    typingStart := 0, typingEnd := tn, ty := global.ty,
    rootsStart := ⟨0, {}⟩, rootsEnd := rst, roots := rho,
    active := EvaluationContext.forGlobal_activeMatches derived wellFormed globalAt _ rfl,
    access := EvaluationContext.forGlobal_accessMatches derived wellFormed globalAt _ rfl rfl,
    protection := ?_, observed := ObservedSafe.empty _ _ _ _, classified := ?_,
    permission := permission, frame := ?_, typed := typed, rooted := rooted,
    effects := EffLe.refl _ }, rfl, rfl, rfl⟩
  · intro holder element target impossible
    exact impossible.elim
  · intro profile i r impossible
    exact impossible.elim
  · exact initialFrame invariant context.inputFuture (initEnv cfg.mod g)
      ⟨cfg.mod, initImpl, initContext, []⟩ rfl rfl rfl rfl rfl rfl rfl (by intro x; rfl)

private theorem blockValueChild? {sc : Nat} {ss : List Stmt} {e : Expr} :
    (DemandNode.block (.mk sc ss (some e))).child? ss.length = some (.expression e) := by
  change ((ss.map (some ∘ DemandNode.statement) ++ [some (.expression e)])[ss.length]?).join = _
  rw [List.getElem?_append_right (by simp)]
  simp

private theorem blockValue_shrinkFuture {path sc ss e} {pc : PlanContext m plans}
    (profile : m.profile = .shrink)
    (context : NodeContext pc path (.block (.mk sc ss (some e))) .block) :
    ((EvaluationContext.shrink profile context : EvaluationContext m plans path
      (.block (.mk sc ss (some e))) .block).child rfl ss.length (.expression e) .expression
      blockValueChild? (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture =
      context.outputFuture := by
  let transition := context.child rfl ss.length (.expression e) .expression blockValueChild?
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have hexpectation : (DemandNode.block (.mk sc ss (some e))).childExpectation?
      pc.approvals.access
      ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
        context.expected.frame.retained⟩ ss.length =
      some ⟨(DemandNode.block (.mk sc ss (some e))).visibleForChild context.expected.frame.active ss.length,
        context.expected.frame.future⟩ := by
    simp [DemandNode.childExpectation?, DemandNode.childFuture, blockValueChild?]
  have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
  change transition.context.expected.frame.future = context.expected.frame.future
  rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, hfuture]
  simp [DemandNode.phaseFuture]


private theorem contextEff_unique {impl : Impl} {ctx : Context} {E E' : Eff}
    (h : ContextEff m impl ctx E) (h' : ContextEff m impl ctx E') : E = E' := by
  rcases h with ⟨rho, range, state, hrun, hE⟩
  rcases h' with ⟨rho', range', state', hrun', hE'⟩
  rw [hrun] at hrun'
  cases hrun'
  exact hE.symm.trans hE'


private theorem pre_fst_range (f : Param × Val → VarId × Val) (hf : ∀ p v, f (p, v) = (p.var, v)) :
    ∀ (ps : List Param) (vs : List Val) (k : Nat), ps.length = vs.length →
    (∀ i p, ps[i]? = some p → p.var = k + i) →
    ((ps.zip vs).map f).map Prod.fst = List.range' k ps.length
  | [], vs, k, _, _ => by simp
  | p :: ps, [], k, hl, _ => by simp at hl
  | p :: ps, v :: vs, k, hl, hvar => by
    have h0 : p.var = k := by simpa using hvar 0 p rfl
    have ih := pre_fst_range f hf ps vs (k + 1) (by simpa using hl) (fun i p' h => by
      have := hvar (i + 1) p' (by simpa using h)
      rw [this]; omega)
    simp only [List.zip_cons_cons, List.map_cons, hf, List.length_cons, List.range'_succ, ih, h0]

private theorem pre_mem (f : Param × Val → VarId × Val) (hf : ∀ p v, f (p, v) = (p.var, v)) :
    ∀ (ps : List Param) (vs : List Val) (x : VarId) (v : Val), (x, v) ∈ (ps.zip vs).map f →
    ∃ (i : Nat) (p : Param), ps[i]? = some p ∧ vs[i]? = some v ∧ p.var = x
  | [], vs, x, v, h => by simp at h
  | p :: ps, [], x, v, h => by simp at h
  | p :: ps, v' :: vs, x, v, h => by
    simp only [List.zip_cons_cons, List.map_cons, hf, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨0, p, rfl, rfl, rfl⟩
    · obtain ⟨i, p', h1, h2, h3⟩ := pre_mem f hf ps vs x v h
      exact ⟨i + 1, p', by simpa using h1, by simpa using h2, h3⟩

private theorem ownerRefParam_of_type {impl : Impl} (checked : ImplOk m impl)
    {i : Nat} {parameter : Param} {declaration : LocalVar}
    (parameterAt : impl.params[i]? = some parameter)
    (variableAt : impl.vars[i]? = some declaration)
    (ownerType : OwnerRefTy declaration.ty) : OwnerRefParam impl i := by
  obtain ⟨parameterId, checkedDeclaration, checkedAt, declarationScope, _⟩ :=
    checked.params i parameter parameterAt
  rw [variableAt] at checkedAt
  cases checkedAt
  have parameterBound : i < impl.params.size := (Array.getElem?_eq_some_iff.1 parameterAt).1
  have mode : parameter.mode = .byRef := by
    cases parameterMode : parameter.mode with
    | byRef => rfl
    | byValue =>
      obtain ⟨mu, element, referenceType | referenceType⟩ := ownerType
      · have shape := checked.parameterShape i parameterBound
        simp [checkParam, parameterAt, parameterId, variableAt, declarationScope,
          parameterMode, referenceType] at shape
        inv at shape
      · have shape := checked.parameterShape i parameterBound
        simp [checkParam, parameterAt, parameterId, variableAt, declarationScope,
          parameterMode, referenceType] at shape
        inv at shape
  exact ⟨parameter, declaration, parameterAt, mode, by simpa [parameterId] using variableAt, ownerType⟩


theorem acceptedCalleeSource {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)}
    (accepted : Core.validate m = .ok ()) :
  ∀ (G : Nat) (P ownerP : Nat → RootInst → Prop) (D : RootInst → Ty → Prop)
    (A : RootInst → RootInst → Prop) (depth : Nat) (c : ContextId) (vals : List Val)
    (s : St) (ctx : Context) (impl : Impl) (E : Eff) (observation : Observation)
    (root : EvaluationContext m plans [] (.block impl.body) .block),
    root.ActiveMatches (implEnv m impl) →
    root.AccessMatches { implEnv m impl with visible := [] } ⟨m, impl, ctx, []⟩ →
    ContextEff m impl ctx E → m.contexts[c]? = some ctx → m.impls[ctx.impl]? = some impl →
    (∀ i r, ownerP i r → P i r) → OwnerParameterShape impl ownerP →
    StoreInv m G s (ObservationDemand observation) →
    ObservedSafe m ⟨G, P, ownerP, E, s.nextScope, D, A⟩ (root.mayShrink ownerP observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m P D observation s.store) →
    ShrinkProtected D A (root.mayShrink ownerP observation) → vals.length = impl.params.size →
    (∀ i v, vals[i]? = some v → ∃ lv, impl.vars[i]? = some lv ∧ HasTy m G s.store v lv.ty ∧
      (OwnerRefParam impl i → OwnerRooted noEnv ownerP [.param i] v lv.ty) ∧
      ∀ r, Targets v r → ∃ ann, (ctx.varRoots.find? (·.1 == i)).map (·.2) = some ann ∧ Gam noEnv P ann r) →
    (∀ i a si x, P i (.local a si x) → si < s.nextScope) →
    (∀ r t, A r t → Older t r) →
    (∀ r el, D r el → ∃ a si x, r = RootInst.local a si x ∧ si < s.nextScope) →
    (∀ r el el', D r el → D r el' → el = el') → OuterOk m G D A s →
    (∀ x cont, (ctx.contentRoots.find? (·.1 == x)).map (·.2) = some cont → PRef P D A ⟨m, impl, ctx, []⟩ impl.vars x cont) →
    (m.globals.size ≤ G ∨ SumOk G P impl ctx) →
    ∃ source : BlockSource ⟨prof, m⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩
      (impl.params.toList.zip vals |>.map (fun item => (item.1.var, item.2)))
      impl.body { s with nextAct := s.nextAct + 1 },
      source.typingEnv = { implEnv m impl with visible := [] } ∧
      source.rootsEnv = ⟨m, impl, ctx, []⟩ ∧
      source.world = ⟨G, P, ownerP, E, s.nextScope, D, A⟩ := by
  have hm := validate_modOk m accepted
  intro G P ownerP D A depth c vals s ctx impl E observation root hActiveRoot hAccessRoot hEff
    hctx himpl hOwnerSubset hOwnerShape hInv hObserved hClass hProtected hlen hargs hPage hAO
    hDout hDfun hSA hcont hperm
  obtain ⟨impl', himpl', hcOk⟩ := hm.ctx c ctx hctx
  rw [himpl] at himpl'
  cases himpl'
  have hiOk := hm.impl _ _ himpl
  have hpar := hiOk.params
  have hsc0 := hiOk.bodyScope
  obtain ⟨bodyTy, tnb, htb, hresTy⟩ := hiOk.body
  obtain ⟨rho, rng, st, hrb, hck, hcs⟩ := hcOk.body
  have hEffEq : E = st.eff := contextEff_unique hEff ⟨rho, rng, st, hrb, rfl⟩
  subst E
  have hpW : Perm m ⟨G, P, ownerP, st.eff, s.nextScope, D, A⟩ := by
    rcases hperm with h | ⟨sm, hs, hall⟩
    · exact Or.inl h
    · obtain ⟨hu, h1, h2, h3, _⟩ := checkSummary_ok _ _ _ _ hcs sm hs
      refine Or.inr ⟨hu, fun t ht => ?_⟩
      rcases ht with ht | ht | ht | ht
      · exact hall t (Or.inl (h1 t ht))
      · exact hall t (Or.inr (Or.inl (h2 t ht)))
      · exact hall t (Or.inr (Or.inr (Or.inl (h3 t ht))))
      · exact hall t (Or.inr (Or.inr (Or.inr (checkSummary_shrinks_ok m impl ctx st.eff hcs sm hs t ht))))
  have hF0 : Frame m ⟨G, P, ownerP, st.eff, s.nextScope, D, A⟩
      { implEnv m impl with visible := [] }
      ⟨m, impl, ctx, []⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩
      { s with nextAct := s.nextAct + 1 } root.inputFuture :=
    { mod_t := rfl, mod_p := rfl, vars_t := rfl, vars_p := rfl
      scopes_t := rfl, scopes_p := rfl
      nodup := List.nodup_nil, sorted := List.Pairwise.nil
      below := fun p hp => by cases hp
      base_le := Nat.le_refl _
      ownerSubset := hOwnerSubset
      ownerShape := hOwnerShape
      pAge := hPage
      vis := fun x hx => by cases hx
      bindings := fun x hx => by cases hx
      storage := by
        rintro r T ⟨x, lv, si, _, hscope, _⟩ v hv
        simp [List.lookup] at hscope
      rooted := fun x lv si v _ h => by simp [List.lookup] at h
      rootedOwners := fun x lv si v _ h => by simp [List.lookup] at h
      inv := {
        live := by
          intro r v hv hd
          cases r with
          | global g => exact hInv.live _ v hv trivial
          | «local» a si x =>
            rcases hd with ⟨_, _, _, lv, _, hscope⟩
            simp [List.lookup] at hscope
        age := hInv.age, fresh := hInv.fresh, globals := hInv.globals
        globalNonRefs := hInv.globalNonRefs
        globalStorageDomain := hInv.globalStorageDomain }
      aOlder := hAO, dOut := hDout, dFun := hDfun, sa := hSA
      pref := fun x cont h => hcont x cont h }
  have hpreFst := pre_fst_range (fun x => (x.fst.var, x.snd)) (fun _ _ => rfl) impl.params.toList
    vals 0 (by simp [hlen]) (fun i p h => by
      have := (hpar i p (by simpa using h)).1
      simp [this])
  generalize impl.body = body at *
  obtain ⟨sc, stmts, value⟩ := body
  have hsc : sc = 0 := hsc0
  subst hsc
  obtain ⟨_, env1, tn1, env2, tn2, hdp, hts, htv⟩ := tyBlock_ok _ _ _ _ _ _ _ _ htb
  obtain ⟨hsame, hvisT, _, _⟩ := declarePre_ok _ _ _ _ _ _ hdp
  obtain ⟨_, st2, hrs, hrv, _⟩ := rpBlockValue_ok _ _ _ _ _ _ _ _ _ hrb
  have hpreOk : PreOk m ⟨G, P, ownerP, st.eff, s.nextScope, D, A⟩ ⟨m, impl, ctx, []⟩
      { vars := impl.vars, act := s.nextAct, scopes := [(0, s.nextScope)], depth := depth + 1 } 0 0
      (impl.params.size + 0) s.store
      (List.map (fun x => (x.fst.var, x.snd)) (impl.params.toList.zip vals)) := by
    refine ⟨by rw [hpreFst]; exact List.nodup_range', ?_⟩
    intro x v hxv
    obtain ⟨i, p, h1, h2, h3⟩ := pre_mem _ (fun _ _ => rfl) _ _ x v hxv
    have h1' : impl.params[i]? = some p := by simpa using h1
    obtain ⟨hvar, lv, hlv, hlsc, hlst⟩ := hpar i p h1'
    rw [hvar] at h3
    subst h3
    obtain ⟨lv', hlv', hty, hownerRoots, hroots⟩ := hargs i v h2
    rw [hlv] at hlv'
    cases hlv'
    refine ⟨Nat.zero_le _, by simpa using (Array.getElem?_eq_some_iff.1 h1').1, lv, hlv, hlsc, hlst,
      hty, fun r hr => ?_⟩
    obtain ⟨ann, ha, hg⟩ := hroots r hr
    refine ⟨ann, ha, gam_of_noEnv hg, fun howner => ?_⟩
    have hownerSlot := ownerRefParam_of_type hiOk h1' hlv howner
    have hownerRoot := hownerRoots hownerSlot howner r hr
    obtain ⟨ownerRef, hownerMember, hownerDenoted⟩ := hownerRoot
    have hownerEq : ownerRef = .param i := by simpa using hownerMember
    subst ownerRef
    obtain ⟨q, hq, hdenoted⟩ := hg
    rcases hcOk.paramAnn i ann (by simpa using (Array.getElem?_eq_some_iff.1 h1').1)
        ha q hq with rfl | ⟨global, rfl⟩
    · exact ⟨.param i, hq, hownerDenoted⟩
    · exact ⟨.global global, hq, hdenoted⟩
  have hvisB : ∀ y, y ∈ env1.visible ↔
      y ∈ (List.map (fun x => (x.fst.var, x.snd)) (impl.params.toList.zip vals)).map Prod.fst ∨
        y ∈ ([] : List VarId) := by
    intro y
    rw [hvisT y, hpreFst]
    simp [implEnv, List.range_eq_range']
  have hkeep : ∀ y, RootRef.local y ∈ rho → ¬ (0 ≤ y ∧ y < st.nextVar) := by
    intro y hy
    cases value with
    | none => rw [hrv.1] at hy; cases hy
    | some e => exact absurd hy ((checkResultV_ok _ _ (hck rfl)).1 y)
  have hactive : root.ActiveMatches env1 := by
    have hvisible : ∀ x, x ∈ env1.visible ↔ x ∈ (implEnv m impl).visible := by
      intro x
      rw [hvisB x, hpreFst]
      simp [implEnv, List.range_eq_range']
    cases root <;> intro x <;> exact (hActiveRoot x).trans (hvisible x).symm
  refine ⟨{
    accepted := accepted, plans := plans, path := [], context := root,
    observation := observation, world := ⟨G, P, ownerP, st.eff, s.nextScope, D, A⟩,
    typingEnv := { implEnv m impl with visible := [] }, typingInner := env1,
    typingAfter := env2, rootsEnv := ⟨m, impl, ctx, []⟩,
    typingStart := tn1, typingValue := tn2, typingEnd := tnb, ty := bodyTy,
    rootsStart := ⟨impl.params.size, {}⟩, rootsValue := st2, rootsEnd := st,
    roots := rho, lowerBound := 0, active := hactive, access := hAccessRoot,
    protection := hProtected, observed := hObserved, classified := hClass,
    permission := hpW, frame := hF0, fresh := by simp [implEnv, Block.scope],
    same := ⟨hsame.mod, hsame.impl, hsame.vars, hsame.loops, hsame.inExpr, hsame.scopes,
      fun _ h => by cases h⟩, visible := hvisB, pretyped := hpreOk,
    bounded := Nat.zero_le _, typed := hts, typedValue := ?_, rooted := hrs,
    rootedValue := ?_, effects := EffLe.refl _, rootsEscape := hkeep }, rfl, rfl, rfl⟩
  · cases value with
    | none => exact htv.1
    | some e => exact htv
  · cases value <;> exact hrv

theorem acceptedContextRoot {m : Module} (accepted : Core.validate m = .ok ())
    {c : ContextId} {ctx : Context} {impl : Impl}
    (contextAt : m.contexts[c]? = some ctx) (implementationAt : m.impls[ctx.impl]? = some impl) :
    ∃ plans, ∃ root : EvaluationContext m plans [] (.block impl.body) .block,
      root.ActiveMatches (implEnv m impl) ∧
      root.AccessMatches { implEnv m impl with visible := [] } ⟨m, impl, ctx, []⟩ := by
  have checked := validate_modOk m accepted
  obtain ⟨plans, derived, wellFormed⟩ := checked.demandPlans
  let selected := EvaluationContext.forContext derived wellFormed contextAt impl implementationAt
  have owner := EvaluationContext.forContext_ownerMatches derived wellFormed contextAt impl implementationAt
  let root := selected.callBody owner contextAt implementationAt
  refine ⟨plans, root, ?_, ?_⟩
  · apply EvaluationContext.callBody_activeMatches
    intro x
    change x ∈ List.range impl.params.size ↔ x ∈ impl.params.toList.map (·.var)
    constructor
    · intro member
      have bound := List.mem_range.mp member
      let parameter := impl.params[x]
      have present : impl.params[x]? = some parameter := Array.getElem?_eq_getElem bound
      have id := (checked.impl _ impl implementationAt).params x parameter present
      exact List.mem_map.mpr ⟨parameter, Array.mem_toList_iff.mpr
        (Array.mem_iff_getElem?.mpr ⟨x, present⟩), id.1⟩
    · intro member
      obtain ⟨parameter, member, id⟩ := List.mem_map.mp member
      obtain ⟨index, present⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
      have indexEq := ((checked.impl _ impl implementationAt).params index parameter present).1
      rw [← id, indexEq]
      exact List.mem_range.mpr (Array.getElem?_eq_some_iff.mp present).1
  · exact EvaluationContext.callBody_accessMatches selected owner contextAt implementationAt
      _ _ rfl rfl rfl rfl rfl

theorem acceptedEntrySource {cfg : Cfg} {state : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (invariant : StoreInv cfg.mod cfg.mod.globals.size state) :
    ∃ ctx impl, cfg.mod.contexts[cfg.mod.entry]? = some ctx ∧
      cfg.mod.impls[ctx.impl]? = some impl ∧ impl.params.size = 0 ∧ impl.results.toList = [] ∧
      ∃ source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩
          (impl.params.toList.zip [] |>.map (fun item => (item.1.var, item.2))) impl.body
          { state with nextAct := state.nextAct + 1 },
        source.typingEnv = { implEnv cfg.mod impl with visible := [] } ∧
        source.rootsEnv = ⟨cfg.mod, impl, ctx, []⟩ := by
  rcases cfg with ⟨profile, module⟩
  let cfg : Cfg := ⟨profile, module⟩
  have checked := validate_modOk cfg.mod accepted
  obtain ⟨ctx, impl, contextAt, implementationAt, noParameters, noResults⟩ := checked.entry
  obtain ⟨plans, root, active, access⟩ := acceptedContextRoot accepted contextAt implementationAt
  obtain ⟨otherImpl, otherAt, contextOk⟩ := checked.ctx _ ctx contextAt
  rw [implementationAt] at otherAt
  cases otherAt
  obtain ⟨rho, range, replayState, replay, resultCheck, summary⟩ := contextOk.body
  have frameInvariant : StoreInv cfg.mod cfg.mod.globals.size state (ObservationDemand Observation.empty) :=
    invariant.changeDemand (fun _ _ => Or.inl trivial)
  obtain ⟨source, typingEq, rootsEq, worldEq⟩ := acceptedCalleeSource (prof := cfg.profile) accepted
    cfg.mod.globals.size (fun _ _ => False) (fun _ _ => False) (fun _ _ => False)
    (fun _ _ => False) 0 cfg.mod.entry [] state ctx impl replayState.eff Observation.empty root
    active access ⟨rho, range, replayState, replay, rfl⟩ contextAt implementationAt
    (by intro i r impossible; exact impossible.elim)
    (by intro i r impossible; exact impossible.elim) frameInvariant (ObservedSafe.empty _ _ _ _)
    (by intro profile i r impossible; exact impossible.elim)
    (by intro holder element target impossible; exact impossible.elim)
    (by simp [noParameters]) (by intro i v impossible; simp at impossible)
    (by intro i a si x impossible; exact impossible.elim)
    (by intro r t impossible; exact impossible.elim)
    (by intro r el impossible; exact impossible.elim)
    (by intro r el el' impossible; exact impossible.elim)
    (by intro r el impossible; exact impossible.elim)
    (by
      intro x contents present
      have bound := (contextOk.content x contents present).1
      omega)
    (Or.inl (Nat.le_refl _))
  refine ⟨ctx, impl, contextAt, implementationAt, noParameters, noResults, ?_⟩
  exact ⟨source, typingEq, rootsEq⟩

private theorem stmts_visible {tenv tenv' : TEnv} {sc tn tn' : Nat} {ss : List Stmt}
    (ht : tyStmts tenv sc ss tn = .ok (tenv', tn')) :
    ∀ x, x ∈ tenv'.visible ↔
      x ∈ (DemandNode.block (.mk sc ss none)).visibleForChild tenv.visible ss.length := by
  induction ss generalizing tenv tn with
  | nil =>
    simp only [tyStmts] at ht; inv at ht
    obtain ⟨rfl, rfl⟩ := ht
    intro x; rfl
  | cons st rest ih =>
    simp only [tyStmts] at ht; inv at ht
    obtain ⟨mid, next, hstmt, hrest⟩ := ht
    intro x
    have h1 := ih hrest x
    have h2 := (DemandNode.block (.mk sc rest none)).visibleForChild_mem_congr rest.length
      (stmt_visibleAfter hstmt) x
    cases st <;> simpa only [DemandNode.visibleForChild, List.take_length, List.foldl_cons,
      DemandNode.visibleAfter] using h1.trans h2


theorem StmtsSource.valueChild {cfg : Cfg} {env : Env} {stmts : List Stmt} {state after : St}
    (source : StmtsSource cfg env stmts state) (expr : Expr)
    (hasValue : source.value = some expr) (ty : Ty) (typingEnd : Nat)
    (roots : List RootRef) (rootsEnd : RState)
    (typed : tyExpr source.typingAfter expr source.typingEnd = .ok (ty, typingEnd))
    (rooted : rpExpr source.rootsEnv expr source.rootsEnd = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E)
    (fuel : Nat) (value : Val) (done : execStmts fuel cfg env stmts state = .ok (.normal value) after) :
    ∃ child : ExprSource cfg env expr after,
      child.typingEnv = source.typingAfter ∧ child.rootsEnv = source.rootsEnv ∧ child.ty = ty := by
  have result := source.result fuel (.normal value) done
  obtain ⟨finalTyping, same, frame, normal⟩ := result.frame
  have finalEq := normal value rfl
  subst finalTyping
  rcases cfg with ⟨prof, m⟩
  rcases source with ⟨accepted, plans, path, observation, W, tenv, tenv', penv,
    tn, tn', rst, rst', lo, sc, all, blockValue, bc, offset, hOffset, hDrop, hActive, hAccess,
    hProtected, hObserved, hClass, hp, hF, hsc, hT, hlo, ht, hr, hE⟩
  dsimp only at hasValue
  subst blockValue
  have same : TSame tenv tenv' := same
  have hall : all.take offset ++ stmts = all := by
    rw [hDrop]
    exact List.take_append_drop offset all
  have hfold : (DemandNode.block (.mk sc stmts none)).visibleForChild
      (blockSuffixActive bc offset) stmts.length = blockSuffixActive bc all.length := by
    cases bc <;> simp only [blockSuffixActive, DemandNode.visibleForChild, List.take_length]
    all_goals rw [← List.foldl_append]; exact congrArg _ hall
  have hfinalActive : ∀ x, x ∈ blockSuffixActive bc all.length ↔ x ∈ tenv'.visible := by
    intro x
    have initial := (DemandNode.block (.mk sc stmts none)).visibleForChild_mem_congr
      stmts.length hActive x
    rw [hfold] at initial
    exact initial.trans (stmts_visible ht x).symm
  let ec := bc.child rfl all.length (.expression expr) .expression blockValueChild?
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have hAct : ec.ActiveMatches tenv' := by
    cases bc with
    | pilot profile active => exact hfinalActive
    | shrink profile context =>
      let transition := context.child rfl all.length (.expression expr) .expression blockValueChild?
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      change ∀ x, x ∈ transition.context.expected.frame.active ↔ x ∈ tenv'.visible
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_active transition.phaseFrameEq,
        DemandNode.childFrame_active transition.childFrameEq]
      exact hfinalActive
  have hAcc : ec.AccessMatches tenv' penv := by
    apply (bc.child_accessMatches_iff rfl all.length (.expression expr) .expression
      blockValueChild? (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) _ _).2
    cases bc <;> simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches,
      (show tenv'.mod = tenv.mod from same.mod), (show tenv'.vars = tenv.vars from same.vars)] using hAccess
  have hMay : ec.mayShrink W.ownerP observation = bc.mayShrink W.ownerP observation := by
    funext r
    exact propext (bc.child_mayShrink_iff rfl all.length (.expression expr) .expression
      blockValueChild? (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation r)
  have hInput : Core.Sound.Frame m W tenv' penv env after ec.inputFuture := by
    apply frame.changeFuture
    intro x hx hf
    cases bc with
    | pilot profile active => exact (hAct x).2 hx
    | shrink profile context =>
      have hout := blockValue_shrinkFuture profile context
      have hin : ec.inputFuture = expr.variables ++ ec.outputFuture := rfl
      rw [hin, hout] at hf
      simpa [blockSuffixFuture, List.drop_length, EvaluationContext.outputFuture,
        List.flatMap_nil, List.nil_append] using hf
  refine ⟨{
    accepted := accepted, plans := plans, path := path ++ [all.length], context := ec,
    observation := observation, world := W, typingEnv := tenv', rootsEnv := penv,
    typingStart := tn', typingEnd := typingEnd, ty := ty, rootsStart := rst',
    rootsEnd := rootsEnd, roots := roots, active := hAct, access := hAcc,
    protection := hMay ▸ hProtected, observed := ?_, classified := result.classified,
    permission := hp, frame := hInput, typed := typed, rooted := rooted, effects := effects }, rfl, rfl, rfl⟩
  rw [hMay]
  exact result.observed

theorem SourceResults.tsame {before after : TEnv} {roots : PEnv} {results : List Ty}
    (metadata : SourceResults before roots results) (same : TSame before after) :
    SourceResults after roots results := by
  intro impl present
  apply metadata impl
  rw [same.impl] at present
  exact present

structure BlockResult {cfg : Cfg} {env : Env} {pre : List (VarId × Val)} {block : Block} {state : St}
    (source : BlockSource cfg env pre block state) (flow : Flow) (after : St) : Prop where
  frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after source.context.outputFuture
  footprint : Footprint (Core.Sound.insts env) (Dset source.world) state after
  rootTypes : PreservesRootTypes cfg.mod source.world.G source.observation.roots state.store after.store
  values : PreservesValues cfg.mod source.world.G source.observation.values state.store after.store
  observed : ObservedSafe cfg.mod source.world (source.context.mayShrink source.world.ownerP source.observation) source.observation after.store
  aliases : RetainsAliases cfg.mod source.world env state.store after.store source.context.retained
  pilotStore : PilotStoreLe cfg.mod state after
  flow : match flow with
    | .normal value => HasTy cfg.mod source.world.G after.store value source.ty ∧
        (∀ root, Targets value root → Gam env source.world.P source.roots root) ∧
        stmtsDiverge cfg.mod.noReturn block.stmts = false ∧
        OwnerRooted env source.world.ownerP source.roots value source.ty
    | .brk => source.typingEnv.loops ≠ 0 ∧ stmtsHaveBreak block.stmts = true
    | .cont => source.typingEnv.loops ≠ 0
    | .ret value => source.typingEnv.inExpr = false ∧ RetOk cfg.mod source.world source.typingEnv source.rootsEnv after value
  classified : cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store
  forbidden : PreservesForbiddenOwnerRoots (m := cfg.mod) (G := source.world.G) (env := env) (P := source.world.P) source.context.forbiddenOwners state after
  mutations : MutationFootprint env source.world.P source.world.base (effectMutationRoots cfg.mod source.rootsEnv.impl source.rootsEnd.eff) state after

theorem BlockSource.result {cfg : Cfg} {env : Env} {pre : List (VarId × Val)} {block : Block} {state after : St}
    (source : BlockSource cfg env pre block state) (fuel : Nat) (flow : Flow)
    (done : execBlock fuel cfg env pre block state = .ok flow after) : BlockResult source flow after := by
  cases block with
  | mk scope stmts value =>
    have checked := (Core.Sound.specs_all (validate_modOk cfg.mod source.accepted)
      cfg.profile source.plans fuel).block source.path scope stmts value source.context
      source.observation source.world source.typingEnv source.typingInner source.typingAfter
      source.rootsEnv env state pre source.typingStart source.typingValue source.typingEnd
      source.ty source.rootsStart source.rootsValue source.rootsEnd source.roots source.lowerBound
      source.active source.access source.protection source.observed source.classified source.permission
      source.frame source.fresh source.same source.visible source.pretyped source.bounded source.typed
      (by cases value <;> exact source.typedValue) source.rooted
      (by cases value <;> exact source.rootedValue) source.effects source.rootsEscape
    unfold Sat at checked
    rw [done] at checked
    obtain ⟨a, b, c, d, e, f, g, h, i, j, k⟩ := checked
    cases flow <;> exact ⟨a, b, c, d, e, f, g, h, i, j, k⟩

end Goose.Lower
