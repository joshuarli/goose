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

private theorem blockStmtChild? {sc : Nat} {all : List Stmt} {value : Option Expr}
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

private noncomputable def blockStmtContext {path : List Nat} {sc : Nat}
    {all : List Stmt} {value : Option Expr}
    (bc : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (offset : Nat) (st : Stmt)
    (hchild : DemandNode.child? (.block (.mk sc all value)) offset = some (.statement st)) :
    EvaluationContext m plans (path ++ [offset]) (.statement st) .statement :=
  bc.child rfl offset (.statement st) .statement hchild
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private theorem stmt_visibleAfter {tenv tenv' : TEnv} {sc tn tn' : Nat} {st : Stmt}
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

private theorem blockSuffixActive_succ {path sc all value offset st rest}
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

private theorem blockStmt_shrinkFuture {path sc all value offset st rest}
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
      statements.rootsEnv = { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes } ∧
      statements.world = source.world ∧ statements.observation = source.observation ∧
      statements.typingStart = source.typingStart ∧ statements.typingEnd = source.typingValue ∧
      statements.rootsStart = source.rootsStart ∧ statements.rootsEnd = source.rootsValue ∧
      statements.plans = source.plans ∧ statements.path = source.path ∧
      HEq statements.context source.context ∧ statements.all = block.stmts ∧
      statements.value = block.value ∧ statements.offset = 0 := by
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
    typed := hts, rooted := hrs, effects := hE2 }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl, rfl, rfl, rfl⟩
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
    (typingVisible : typing.visible = []) (rootsContents : ∀ x, roots.cont x = none)
    (activation : ActId) :
    Core.Sound.Frame m (InitialWorld globals state.nextScope effects) typing roots ⟨#[], activation, [], 0⟩ state future := by
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
    simp at present
  · intro x lv si v present
    simp at present
  · intro x lv si v present
    simp at present
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
    (invariant : StoreInv cfg.mod g state) (activation : ActId) :
    ∃ source : ExprSource cfg ⟨#[], activation, [], 0⟩ global.init state,
      source.typingEnv = initEnv cfg.mod g ∧
      source.rootsEnv = ⟨cfg.mod, initImpl, initContext, []⟩ ∧ source.ty = global.ty ∧ source.world.G = g := by
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
    effects := EffLe.refl _ }, rfl, rfl, rfl, rfl⟩
  · intro holder element target impossible
    exact impossible.elim
  · intro profile i r impossible
    exact impossible.elim
  · exact initialFrame invariant context.inputFuture (initEnv cfg.mod g)
      ⟨cfg.mod, initImpl, initContext, []⟩ rfl rfl rfl rfl rfl rfl rfl (by intro x; rfl) activation

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

theorem initialStoreInvariant (module : Module) : StoreInv module 0 St.initial := by
  constructor
  all_goals simp [St.initial, Store.empty]

private theorem sampledCalleeSource {prof : NumProfile} {plans path c args origin}
    (accepted : Core.validate m = .ok ())
    (ec : EvaluationContext m plans path (.expression (.call c args origin)) .expression)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St)
    (ctx : Context) (callee : Impl) (E : Eff) (vals : List Val) (ars : List (List RootRef))
    (retained : List RetainedAlias) (ty : Ty) (rho : List RootRef) (initialEffects : Eff)
    (contextAt : m.contexts[c]? = some ctx) (implementationAt : m.impls[ctx.impl]? = some callee)
    (implementationChecked : ImplOk m callee) (contextChecked : CtxOk m callee ctx)
    (effectReplay : ContextEff m callee ctx E)
    (active : ec.ActiveMatches tenv) (access : ec.AccessMatches tenv penv)
    (protectedSlices : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (sourceSafe : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (sourceClassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (permission : Perm m W)
    (frame : Frame m W tenv penv env s (callArgsFuture ec args.length []))
    (size : callee.params.size = args.length) (length : vals.length = args.length)
    (argumentsChecked : ∀ i, i < callee.params.size → checkArgRoots callee ctx ars i = .ok ())
    (contentsChecked : ∀ i, i < args.length → checkContent penv ctx args ars i = .ok ())
    (sampled : ∀ (i : Nat) (v : Val), vals[i]? = some v →
      ∃ (p : Param) (pv : LocalVar) (ar : List RootRef) (a : Arg) (t : Ty)
        (tn0 tn1 : Nat) (rst0 rst1 : RState),
      callee.params.toList[i]? = some p ∧ callee.vars[p.var]? = some pv ∧
      ars[i]? = some ar ∧ HasTy m W.G s.store v pv.ty ∧
      (∀ r, Targets v r → Gam env W.P ar r) ∧
      OwnerRooted env W.ownerP ar v pv.ty ∧ args[i]? = some a ∧
      ArgTy tenv a tn0 t tn1 ∧ t.passableTo pv.ty = true ∧ ArgRp penv a rst0 ar rst1)
    (resultType : (callee.results.toList = [] ∧ ty = .unit) ∨ callee.results.toList = [ty])
    (resultReplay : callResultRoots callee ctx ars = .ok rho)
    (effects : EffLe (callEffects callee ctx ars initialEffects) W.E)
    (retainedSubset : ∀ alias, alias ∈ ec.retained → alias ∈ retained) :
    let Pc := fun i root => Gam env W.P (ars[i]?.getD []) root
    let boundary := callObservation (m := m) observation W tenv env ec.outputFuture retained s.store
    let root := ec.calleeContext callee contextAt implementationAt
    let calleeWorld := World.mk W.G Pc (callOwnerP W callee env ars) E s.nextScope
      (callD W tenv env ec.outputFuture args) (callA W penv env)
    ObservedSafe m calleeWorld (root.mayShrink (callOwnerP W callee env ars) boundary) boundary s.store →
    (m.profile = .shrink → ClassifiedParameters m Pc
      (callD W tenv env ec.outputFuture args) boundary s.store) →
    ShrinkProtected (callD W tenv env ec.outputFuture args) (callA W penv env)
      (root.mayShrink (callOwnerP W callee env ars) boundary) →
    ∃ source : BlockSource ⟨prof, m⟩ ⟨callee.vars, s.nextAct, [], env.depth + 1⟩
      (callee.params.toList.zip vals |>.map (fun item => (item.1.var, item.2))) callee.body
      { s with nextAct := s.nextAct + 1 },
      source.typingEnv = { implEnv m callee with visible := [] } ∧
      source.rootsEnv = ⟨m, callee, ctx, []⟩ := by
  dsimp only
  intro boundarySafe boundaryClassified boundaryProtected
  have futureSubset : ∀ x, x ∈ ec.outputFuture → x ∈ callArgsFuture ec args.length [] := by
    cases ec with
    | pilot _ _ =>
      intro x member
      simpa [callArgsFuture, EvaluationContext.outputFuture, DemandNode.visibleAfter] using member
    | shrink _ _ =>
      intro x member
      simp only [callArgsFuture, List.flatMap_nil, List.append_nil, List.mem_append]
      exact Or.inr member
  have outer : OuterOk m W.G (callD W tenv env ec.outputFuture args) (callA W penv env) s :=
    callOuterOk frame (fun x lv mu element variableAt typeEq visible needed =>
      callArgsFuture_sliceHolder ec active access frame.vars_t variableAt typeEq visible needed)
  have invariant := (frame.callDemand boundarySafe.typed
    (fun root element hd => by obtain ⟨v, hv, ht, _⟩ := outer root element hd; exact ⟨v, hv, ht⟩)).observationDemand
  let root := ec.calleeContext callee contextAt implementationAt
  have owner := ec.calleeContext_owner callee contextAt implementationAt
  have hvisible : ∀ x, x ∈ (implEnv m callee).visible ↔ x ∈ callee.params.toList.map (·.var) := by
    intro x
    change x ∈ List.range callee.params.size ↔ x ∈ callee.params.toList.map (·.var)
    constructor
    · intro member
      have bound := List.mem_range.mp member
      let parameter := callee.params[x]
      have present : callee.params[x]? = some parameter := Array.getElem?_eq_getElem bound
      have id := implementationChecked.params x parameter present
      exact List.mem_map.mpr ⟨parameter, Array.mem_toList_iff.mpr
        (Array.mem_iff_getElem?.mpr ⟨x, present⟩), id.1⟩
    · intro member
      obtain ⟨parameter, member, id⟩ := List.mem_map.mp member
      obtain ⟨index, present⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
      have indexEq := (implementationChecked.params index parameter present).1
      rw [← id, indexEq]
      exact List.mem_range.mpr (Array.getElem?_eq_some_iff.mp present).1
  have hmay : (root.callBody owner contextAt implementationAt).mayShrink
      (callOwnerP W callee env ars) (callObservation (m := m) observation W tenv env ec.outputFuture retained s.store) =
      root.mayShrink (callOwnerP W callee env ars) (callObservation (m := m) observation W tenv env ec.outputFuture retained s.store) := by
    funext r
    exact propext (root.callBody_mayShrink_iff owner contextAt implementationAt _ _ r)
  obtain ⟨source, typingEq, rootsEq, worldEq⟩ := acceptedCalleeSource accepted W.G (fun i root => Gam env W.P (ars[i]?.getD []) root)
    (callOwnerP W callee env ars) (callD W tenv env ec.outputFuture args) (callA W penv env) env.depth c vals s ctx callee E
    (callObservation (m := m) observation W tenv env ec.outputFuture retained s.store)
    (root.callBody owner contextAt implementationAt)
    (root.callBody_activeMatches owner contextAt implementationAt _ hvisible)
    (root.callBody_accessMatches owner contextAt implementationAt _ _ rfl rfl rfl rfl rfl)
    effectReplay contextAt implementationAt
    (frame.callOwnerP_subset callee ars) (callOwnerP.shape W callee env ars)
    invariant (by rw [hmay]; exact boundarySafe) boundaryClassified
    (by rw [hmay]; exact boundaryProtected)
    (by rw [length]; exact size.symm)
    (by
      intro i value valueAt
      obtain ⟨lv, variableAt, typed, roots⟩ := callValues_ok implementationChecked
        contextChecked argumentsChecked (fun j v sampledAt => by
          obtain ⟨p, pv, ar, _, _, _, _, _, _, hp, hv, hr, ht, roots, _⟩ := sampled j v sampledAt
          exact ⟨p, pv, ar, hp, hv, hr, ht, roots⟩) i value valueAt
      refine ⟨lv, variableAt, typed, ?_, roots⟩
      exact callValues_ownerRooted implementationChecked (fun j v sampledAt => by
        obtain ⟨p, pv, ar, _, _, _, _, _, _, hp, hv, hr, _, _, owner, _⟩ := sampled j v sampledAt
        exact ⟨p, pv, ar, hp, hv, hr, owner⟩) i value lv valueAt variableAt)

    (fun i activation instanceId variableId denoted => frame.gam_older denoted _ _ _ rfl)
    (callA_older frame) (callD_out frame) (callD_fun frame) outer
    (call_pref frame implementationChecked contextChecked contentsChecked size length sampled)
    (callPermission permission contextChecked effects)
  exact ⟨source, typingEq, rootsEq⟩

theorem ExprSource.calleeAfterArgs {cfg : Cfg} {env : Env} {state after : St}
    {c : ContextId} {args : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call c args origin) state)
    (fuel : Nat) (vals : List Val)
    (done : mapList (evalArg fuel cfg env) args state = .ok vals after) :
    ∃ ctx callee, cfg.mod.contexts[c]? = some ctx ∧ cfg.mod.impls[ctx.impl]? = some callee ∧
      ∃ body : BlockSource cfg ⟨callee.vars, after.nextAct, [], env.depth + 1⟩
        (callee.params.toList.zip vals |>.map (fun item => (item.1.var, item.2))) callee.body
        { after with nextAct := after.nextAct + 1 },
        body.typingEnv = { implEnv cfg.mod callee with visible := [] } ∧
        body.rootsEnv = ⟨cfg.mod, callee, ctx, []⟩ := by
  rcases cfg with ⟨prof, m⟩
  let ec := source.context
  let W := source.world
  let tenv := source.typingEnv
  let penv := source.rootsEnv
  let observation := source.observation
  have hm := validate_modOk m source.accepted
  have frame : Core.Sound.Frame m W tenv penv env state ec.inputFuture := source.frame
  have typing : tyExpr tenv (.call c args origin) source.typingStart = .ok (source.ty, source.typingEnd) := source.typed
  have replay : rpExpr penv (.call c args origin) source.rootsStart = .ok (source.roots, source.rootsEnd) := source.rooted
  have effects := source.effects
  have active : ec.ActiveMatches tenv := source.active
  have access : ec.AccessMatches tenv penv := source.access
  have protectedSlices : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation) := source.protection
  have sourceReplay := replay
  simp only [rpExpr] at replay
  inv at replay
  obtain ⟨ars, state1, argumentsReplay, contentsCheck, callReplay⟩ := replay
  have argumentsEffects := (PMono.rpCall _ _ _ _ _ _ callReplay).2.trans effects
  obtain ⟨ctx, callee, contextAt, implementationAt, argumentCheck, effectAt, resultReplay⟩ :=
    rpCall_ok _ _ _ _ _ _ callReplay
  have contents := checkContents_ok _ _ _ _ ctx contentsCheck contextAt
  rw [frame.mod_p] at contextAt implementationAt
  have contextAtT : tenv.mod.contexts[c]? = some ctx := by rw [frame.mod_t]; exact contextAt
  have implementationAtT : tenv.mod.impls[ctx.impl]? = some callee := by
    rw [frame.mod_t]
    exact implementationAt
  simp only [tyExpr, contextAtT, implementationAtT] at typing
  inv at typing
  obtain ⟨_, size, next, argumentTypes, _, _, resultType, _⟩ := typing
  obtain ⟨other, otherAt, contextChecked⟩ := hm.ctx c ctx contextAt
  rw [implementationAt] at otherAt
  cases otherAt
  have implementationChecked := hm.impl _ _ implementationAt
  have suffixFrame : Core.Sound.Frame m W tenv penv env state (callArgsFuture ec 0 args) := by
    cases hcontext : source.context <;>
      simpa [ec, hcontext, callArgsFuture, EvaluationContext.inputFuture, NodeContext.inputFuture,
        NodeContext.outputFuture, DemandNode.variables, Expr.variables] using frame
  have checked := args_spec ec observation (specs_all hm prof source.plans fuel).arg
    source.permission active access protectedSlices callee implementationChecked args callee.params.toList
    0 state source.typingStart next source.rootsStart state1 ars (by simp) (by omega)
    (fun _ member => member) suffixFrame source.observed source.classified (by simpa using size)
    argumentTypes argumentsReplay argumentsEffects
  unfold Sat at checked
  rw [done] at checked
  obtain ⟨frame1, footprint1, roots1, values1, source1, retained1, pilot1, _, length,
    sampled, class1, forbidden1, argumentsMutation⟩ := checked
  obtain ⟨bodyRoots, range, bodyState, bodyReplay, _, _⟩ := contextChecked.body
  have bodyEffects : ContextEff m callee ctx bodyState.eff :=
    ⟨bodyRoots, range, bodyState, bodyReplay, rfl⟩
  have charged : EffLe (callEffects callee ctx ars state1.eff) W.E := by
    rw [effectAt] at effects
    exact effects
  have body := sampledCalleeSource (prof := prof) source.accepted ec observation W tenv penv env after
    ctx callee bodyState.eff vals ars ec.retained source.ty source.roots state1.eff contextAt implementationAt
    implementationChecked contextChecked bodyEffects active access protectedSlices source1 class1
    source.permission frame1 size length argumentCheck contents sampled resultType resultReplay charged
    (fun _ member => member)
  refine ⟨ctx, callee, contextAt, implementationAt, ?_⟩
  cases hcontext : ec with
  | pilot profile bindings =>
    rw [hcontext] at body source1 frame1
    change ObservedSafe m W (fun _ => False) observation after.store at source1
    have boundary := callBody_pilot_observed (args := args) (ars := ars) (callee := callee)
      (E := bodyState.eff) (by simpa [callArgsFuture] using frame1) source1
    apply body
    · change ObservedSafe m _ (fun _ => False) _ _
      exact boundary
    · intro shrink
      rw [profile] at shrink
      cases shrink
    · intro holder element target holderProtected alias targetRoot shrink
      change False at shrink
      exact shrink.elim
  | shrink profile context =>
    rw [hcontext] at body active access protectedSlices source1 frame1
    let ec : EvaluationContext m source.plans source.path (.expression (.call c args origin)) .expression :=
      .shrink profile context
    have declarations := ArgumentRootDeclarations.ofCallArgs frame hm
      (context.callerContext_checked hm access) size argumentTypes argumentsReplay
    let boundary := callObservation (m := m) observation W tenv env context.outputFuture ec.retained after.store
    let root := ec.calleeContext callee contextAt implementationAt
    let shrinking := root.mayShrink (callOwnerP W callee env ars) boundary
    have recorded : ∀ rootInst, shrinking rootInst →
        MayShrinkEff (callOwnerP W callee env ars) bodyState.eff rootInst ∧ OwnerCap m boundary rootInst :=
      fun _ shrink => EvaluationContext.callBody_effect root
        (ec.calleeContext_owner callee contextAt implementationAt) contextAt implementationAt hm bodyEffects shrink
    have coverage := NodeContext.callBody_coverage (retained := ec.retained) context frame1
      access contextAt implementationAt contextChecked bodyEffects
      source1.rootsOlder argumentsReplay
    have cover : ∀ rootInst, shrinking rootInst → ∃ owner,
        owner ∈ context.callMutationContext.expected.shrinkOwners ∧ owner.invalidates = true ∧
        Gam env W.ownerP owner.roots rootInst :=
      fun rootInst shrink => coverage rootInst (recorded rootInst shrink).1 (recorded rootInst shrink).2
    have caps : ∀ rootInst, shrinking rootInst → OwnerCap m boundary rootInst :=
      fun rootInst shrink => (recorded rootInst shrink).2
    have futureSubset : ∀ x, x ∈ context.outputFuture → x ∈ callArgsFuture ec args.length [] := by
      simp only [ec, callArgsFuture, List.flatMap_nil, List.append_nil, List.mem_append]
      exact fun _ member => Or.inr member
    have initialized : ∀ global, shrinking (.global global) → global < W.G := by
      intro global shrink
      obtain ⟨owner, ownerMember, _, ownerIn⟩ := cover _ shrink
      exact NodeContext.callGlobal_initialized context hm frame1 access
        source.permission sourceReplay effects ownerMember ownerIn (caps _ shrink)
    have boundaryObserved := context.callObservation_observed frame1 active
      access futureSubset source1
      protectedSlices caps initialized (context.callMutation_retains_parent) cover
    have protectedBoundary := context.callD_shrinkProtected frame1 active
      access protectedSlices caps cover
    have boundaryClass := frame1.callObservation_classified (continuation := context.outputFuture)
      (args := args) (retained := ec.retained) declarations (class1 profile)
    apply body
    · exact ⟨boundaryObserved.typed, boundaryObserved.rootsOlder, boundaryObserved.valuesOlder,
        boundaryObserved.rootsProtected, boundaryObserved.valuesProtected,
        callObservation_callD_holderTypes frame1 source1 boundaryObserved⟩
    · exact fun _ => boundaryClass
    · exact protectedBoundary

private theorem nextActivationInvariant {module : Module} {globals : Nat} {state : St}
    {demanded : RootInst → Prop} (invariant : StoreInv module globals state demanded) :
    StoreInv module globals { state with nextAct := state.nextAct + 1 } demanded :=
  ⟨invariant.live, invariant.age, invariant.fresh, invariant.globals,
    invariant.globalNonRefs, invariant.globalStorageDomain⟩

theorem acceptedGlobalActivation {cfg : Cfg} {state : St} {g : GlobalId} {global : Global}
    (accepted : Core.validate cfg.mod = .ok ())
    (globalAt : cfg.mod.globals[g]? = some global) (invariant : StoreInv cfg.mod g state) :
    ∃ source : ExprSource cfg ⟨#[], state.nextAct, [], 0⟩ global.init
        { state with nextAct := state.nextAct + 1 },
      source.typingEnv = initEnv cfg.mod g ∧
      source.rootsEnv = ⟨cfg.mod, initImpl, initContext, []⟩ ∧ source.ty = global.ty ∧ source.world.G = g :=
  acceptedGlobalSource accepted globalAt (nextActivationInvariant invariant) state.nextAct

structure InitializedGlobals (module : Module) (count : Nat) (state : St) : Prop where
  invariant : StoreInv module count state
  domain : ∀ (root : RootInst) (value : Val), state.store.roots[root]? = some value →
    ∃ global : GlobalId, root = RootInst.global global ∧ global < count

theorem InitializedGlobals.initial (module : Module) : InitializedGlobals module 0 St.initial :=
  ⟨initialStoreInvariant module, by intro root value present; simp [St.initial, Store.empty] at present⟩

theorem InitializedGlobals.afterInitializer {cfg : Cfg} {before after : St} {g : GlobalId}
    {global : Global} {value : Val} (accepted : Core.validate cfg.mod = .ok ())
    (globalAt : cfg.mod.globals[g]? = some global) (initialized : InitializedGlobals cfg.mod g before)
    (fuel : Nat) (done : evalExpr fuel cfg ⟨#[], before.nextAct, [], 0⟩ global.init
      { before with nextAct := before.nextAct + 1 } = .ok value after) :
    InitializedGlobals cfg.mod (g + 1) { after with store := after.store.introduce (.global g) value } := by
  obtain ⟨source, _, _, typeEq, countEq⟩ := acceptedGlobalActivation accepted globalAt initialized.invariant
  have result := source.result fuel value done
  have domain : ∀ (root : RootInst) (value : Val), after.store.roots[root]? = some value →
      ∃ global : GlobalId, root = RootInst.global global ∧ global < g := by
    intro root value present
    have oldPresent := result.footprint.dom root (by rw [present]; simp)
    obtain ⟨old, oldAt⟩ := Option.ne_none_iff_exists'.mp oldPresent
    exact initialized.domain root old oldAt
  have currentInvariant : StoreInv cfg.mod g after := by
    have invariant := result.frame.inv
    rw [countEq] at invariant
    apply invariant.changeDemand
    intro root demanded
    cases root with
    | global _ => exact Or.inl trivial
    | «local» act scope slot =>
      apply Or.inr
      cases present : after.store.roots[RootInst.local act scope slot]? with
      | none => rfl
      | some v => obtain ⟨_, impossible, _⟩ := domain _ v present; cases impossible
  have free : after.store.roots[RootInst.global g]? = none := by
    cases present : after.store.roots[RootInst.global g]? with
    | none => rfl
    | some v =>
      obtain ⟨index, equal, bound⟩ := domain _ v present
      have indexEq := RootInst.global.inj equal
      exact False.elim (Nat.lt_irrefl g (indexEq.symm ▸ bound))
  have typed : HasTy cfg.mod g after.store value global.ty := by
    have typed := result.typed
    rw [typeEq, countEq] at typed
    exact typed
  have globalOk := (validate_modOk cfg.mod accepted).glob g global globalAt
  have nonref := typed.not_ref globalOk.ty.2
  have boundInvariant := currentInvariant.bind free typed.held
    (fun root targeted => False.elim (nonref targeted.isRef))
    (by intro act scope slot impossible; cases impossible)
    (fun _ _ => nonref)
    (fun _ equal => by cases equal; exact Or.inl (Array.getElem?_eq_some_iff.mp globalAt).1)
  have boundDomain : ∀ root v,
      (after.store.introduce (.global g) value).roots[root]? = some v →
      ∃ global : GlobalId, root = RootInst.global global ∧ global < g + 1 := by
    intro root v present
    rw [get_introduce] at present
    split at present
    · rename_i same
      exact ⟨g, same.symm, Nat.lt_succ_self _⟩
    · obtain ⟨index, equal, bound⟩ := domain _ v present
      exact ⟨index, equal, Nat.lt_succ_of_lt bound⟩
  refine ⟨{
    live := ?_, age := boundInvariant.age, fresh := boundInvariant.fresh,
    globals := ?_, globalNonRefs := boundInvariant.globalNonRefs,
    globalStorageDomain := boundInvariant.globalStorageDomain }, boundDomain⟩
  · intro root v present demanded
    obtain ⟨index, equal, _⟩ := boundDomain root v present
    subst root
    have nonref := boundInvariant.globalNonRefs index v present
    cases v <;> simp [IsRef, Held] at nonref ⊢
  · intro index declaration bound present
    by_cases old : index < g
    · exact boundInvariant.globals index declaration old present
    · have equal : index = g := by omega
      subst index
      rw [globalAt] at present
      cases present
      refine ⟨value, ?_, typed.flatOfStorableNonref globalOk.ty.1 globalOk.ty.2⟩
      apply (read_ok_iff _ _ _).mpr
      exact ⟨value, by simp [get_introduce], by simp [get_nil]⟩

theorem InitializedGlobals.afterInitializers {cfg : Cfg}
    (accepted : Core.validate cfg.mod = .ok ()) (fuel : Nat) :
    ∀ (count first : Nat) (before after : St),
      first + count ≤ cfg.mod.globals.size → InitializedGlobals cfg.mod first before →
      initGlobals fuel cfg (List.range' first count) before = .ok () after →
      InitializedGlobals cfg.mod (first + count) after := by
  intro count
  induction count with
  | zero =>
    intro first before after bounded initialized done
    simp only [List.range'_zero, initGlobals] at done
    change Res.ok () before = Res.ok () after at done
    cases done
    exact initialized
  | succ count induction =>
    intro first before after bounded initialized done
    have bound : first < cfg.mod.globals.size := by omega
    let global := cfg.mod.globals[first]
    have globalAt : cfg.mod.globals[first]? = some global := Array.getElem?_eq_getElem bound
    simp only [List.range'_succ, initGlobals, lookupGlobal, globalAt, pure_bind] at done
    change M.bind' (evalExpr fuel cfg ⟨#[], before.nextAct, [], 0⟩ global.init) (fun value =>
      M.bind' (bindRoot (.global first) value) (fun _ =>
        initGlobals fuel cfg (List.range' (first + 1) count)))
      { before with nextAct := before.nextAct + 1 } = .ok () after at done
    cases evaluated : evalExpr fuel cfg ⟨#[], before.nextAct, [], 0⟩ global.init
        { before with nextAct := before.nextAct + 1 } with
    | stop reason state =>
      simp only [M.bind', evaluated] at done
      cases done
    | ok value state =>
      have initializedNext := initialized.afterInitializer accepted globalAt fuel evaluated
      have rest : initGlobals fuel cfg (List.range' (first + 1) count)
          { state with store := state.store.introduce (.global first) value } = .ok () after := by
        simpa only [M.bind', evaluated, bindRoot] using done
      have final := induction (first + 1) _ after (by omega) initializedNext rest
      have total : first + (count + 1) = (first + 1) + count := by omega
      rw [total]
      exact final

theorem initializedGlobals_of_success {cfg : Cfg} {state : St}
    (accepted : Core.validate cfg.mod = .ok ()) (fuel : Nat)
    (done : initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state) :
    InitializedGlobals cfg.mod cfg.mod.globals.size state := by
  have run : initGlobals fuel cfg (List.range' 0 cfg.mod.globals.size) St.initial = .ok () state := by
    simpa [List.range_eq_range'] using done
  simpa only [Nat.zero_add] using InitializedGlobals.afterInitializers accepted fuel cfg.mod.globals.size 0 St.initial state
    (by simp) (InitializedGlobals.initial cfg.mod) run

theorem acceptedEntryAfterGlobals {cfg : Cfg} {state : St}
    (accepted : Core.validate cfg.mod = .ok ()) (fuel : Nat)
    (done : initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state) :
    ∃ ctx impl, cfg.mod.contexts[cfg.mod.entry]? = some ctx ∧
      cfg.mod.impls[ctx.impl]? = some impl ∧ impl.params.size = 0 ∧ impl.results.toList = [] ∧
      ∃ source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩
          (impl.params.toList.zip [] |>.map (fun item => (item.1.var, item.2))) impl.body
          { state with nextAct := state.nextAct + 1 },
        source.typingEnv = { implEnv cfg.mod impl with visible := [] } ∧
        source.rootsEnv = ⟨cfg.mod, impl, ctx, []⟩ :=
  acceptedEntrySource accepted (initializedGlobals_of_success accepted fuel done).invariant

theorem StmtSource.expressionChildSource {cfg : Cfg} {env : Env} {stmt : Stmt}
    {initial state : St} (source : StmtSource cfg env stmt initial)
    (index : Nat) (expr : Expr)
    (childAt : (DemandNode.statement stmt).child? index = some (.expression expr))
    (visible : ∀ x, x ∈ source.typingEnv.visible ↔
      x ∈ (DemandNode.statement stmt).visibleForChild source.typingEnv.visible index)
    (typingStart typingEnd : Nat) (ty : Ty) (rootsStart rootsEnd : RState) (roots : List RootRef)
    (typed : tyExpr source.typingEnv expr typingStart = .ok (ty, typingEnd))
    (rooted : rpExpr source.rootsEnv expr rootsStart = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E)
    (frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (source.context.child rfl index (.expression expr) .expression childAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture)
    (observed : ObservedSafe cfg.mod source.world
      (source.context.mayShrink source.world.ownerP source.observation) source.observation state.store)
    (classified : cfg.mod.profile = .shrink →
      ClassifiedParameters cfg.mod source.world.P source.world.D source.observation state.store) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = ty ∧ child.world = source.world ∧
      child.observation = source.observation ∧
      child.context.outputFuture =
        (source.context.child rfl index (.expression expr) .expression childAt
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.retained =
        (source.context.child rfl index (.expression expr) .expression childAt
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).retained ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
  have phase : DemandNodeHasPhase (.expression expr) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let context := source.context.child rfl index (.expression expr) .expression childAt phase
  have may : context.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl index (.expression expr) .expression
      childAt phase source.world.ownerP source.observation root)
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [index],
    context := context, observation := source.observation, world := source.world,
    typingEnv := source.typingEnv, rootsEnv := source.rootsEnv, typingStart := typingStart,
    typingEnd := typingEnd, ty := ty, rootsStart := rootsStart, rootsEnd := rootsEnd, roots := roots,
    active := source.context.child_activeMatches rfl index (.expression expr) .expression childAt phase
      source.typingEnv source.typingEnv source.active visible,
    access := (source.context.child_accessMatches_iff rfl index (.expression expr) .expression
      childAt phase _ _).mpr source.access,
    protection := may ▸ source.protection, observed := may ▸ observed, classified := classified,
    permission := source.permission, frame := frame, typed := typed, rooted := rooted,
    effects := effects }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, may⟩

theorem StmtSource.firstExpressionChildSource {cfg : Cfg} {env : Env} {stmt : Stmt} {state : St}
    (source : StmtSource cfg env stmt state) (expr : Expr)
    (childAt : (DemandNode.statement stmt).child? 0 = some (.expression expr))
    (visible : ∀ x, x ∈ source.typingEnv.visible ↔
      x ∈ (DemandNode.statement stmt).visibleForChild source.typingEnv.visible 0)
    (variables : ∀ x, x ∈ expr.variables → x ∈ stmt.variables)
    (futureVariables : DemandPoint → List VarId)
    (futureSubset : ∀ parent x, x ∈ futureVariables parent → x ∈ stmt.variables ++ parent.future)
    (future : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 0 =
      some ⟨(DemandNode.statement stmt).visibleForChild parent.active 0, futureVariables parent⟩)
    (typingStart typingEnd : Nat) (ty : Ty) (rootsStart rootsEnd : RState) (roots : List RootRef)
    (typed : tyExpr source.typingEnv expr typingStart = .ok (ty, typingEnd))
    (rooted : rpExpr source.rootsEnv expr rootsStart = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = ty ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.context.outputFuture =
        (source.context.child rfl 0 (.expression expr) .expression childAt
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
  let ec := source.context
  have phase : DemandNodeHasPhase (.expression expr) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let child := ec.child rfl 0 (.expression expr) .expression childAt phase
  have may : child.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.expression expr) .expression childAt phase
      source.world.ownerP source.observation root)
  have input : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state child.inputFuture := by
    apply source.frame.narrowFuture
    intro x member
    change x ∈ ec.inputFuture
    change x ∈ (ec.child rfl 0 (.expression expr) .expression childAt phase).inputFuture at member
    cases hcontext : ec with
    | pilot profile active =>
      rw [hcontext] at member
      change x ∈ expr.variables ++ (DemandNode.statement stmt).visibleForChild active 0 at member
      have activeEq : (DemandNode.statement stmt).visibleForChild active 0 = active := by
        cases stmt <;> simp [DemandNode.visibleForChild]
      rw [activeEq] at member
      change x ∈ stmt.variables ++ active
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (variables x h)) (List.mem_append_right _)
    | shrink profile context =>
      rw [hcontext] at member
      let transition := context.child rfl 0 (.expression expr) .expression childAt phase
      change x ∈ expr.variables ++ transition.context.expected.frame.future at member
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        DemandNode.childFrame_future transition.childFrameEq (future _ _)] at member
      change x ∈ stmt.variables ++ context.expected.frame.future
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (variables x h)) (futureSubset _ x)
  obtain ⟨result, typingEq, rootsEq, typeEq, worldEq, observationEq, futureEq, _, shrinkEq⟩ :=
    source.expressionChildSource 0 expr childAt visible typingStart typingEnd ty rootsStart rootsEnd
      roots typed rooted effects input source.observed source.classified
  exact ⟨result, typingEq, rootsEq, typeEq, worldEq, observationEq, futureEq, shrinkEq⟩

theorem StmtSource.exprChild {cfg : Cfg} {env : Env} {state : St} {expr : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.expr expr origin) state) :
    ∃ child : ExprSource cfg env expr state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, ty, finish, typed, _⟩ := typed
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨roots, rooted⟩ := rooted
  have childAt : (DemandNode.statement (.expr expr origin)).child? 0 = some (.expression expr) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨child, typingEq, rootsEq, _, _⟩ := source.firstExpressionChildSource expr childAt
    (by simp [DemandNode.visibleForChild]) (by simp [Stmt.variables])
    (fun parent => parent.future) (by intro parent x member; exact List.mem_append_right _ member)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
    source.typingStart finish ty source.rootsStart source.rootsEnd roots typed rooted source.effects
  exact ⟨child, typingEq, rootsEq⟩

theorem StmtSource.letChild {cfg : Cfg} {env : Env} {state : St} {slot : VarId}
    {expr : Expr} {origin : OriginId} (source : StmtSource cfg env (.letS slot expr origin) state) :
    ∃ child : ExprSource cfg env expr state, ∃ declaration : LocalVar,
      env.vars[slot]? = some declaration ∧ child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty.passableTo declaration.ty = true := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, declaration, start, declared, ty, finish, typed, _, _, passable, _⟩ := typed
  have variableAt := (declare_ok _ _ _ _ _ declared).2.1
  rw [source.frame.vars_t] at variableAt
  have rootVariableAt : source.rootsEnv.impl.vars[slot]? = some declaration := by
    rw [source.frame.vars_p]
    exact variableAt
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨_, roots, finishRoots, rooted, tail⟩ := rooted
  have endEq : source.rootsEnd = finishRoots := by
    simp only [rootVariableAt] at tail
    by_cases reference : declaration.ty.isRefLike = true
    · simp only [reference, if_true] at tail
      inv at tail
      exact tail.2
    · simp only [reference, if_false] at tail
      inv at tail
      exact tail
  have childAt : (DemandNode.statement (.letS slot expr origin)).child? 0 = some (.expression expr) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨child, typingEq, rootsEq, typeEq, _⟩ := source.firstExpressionChildSource expr childAt
    (by simp [DemandNode.visibleForChild]) (by simp [Stmt.variables])
    (fun parent => parent.future) (by intro parent x member; exact List.mem_append_right _ member)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
    start finish ty { source.rootsStart with nextVar := source.rootsStart.nextVar + 1 }
    finishRoots roots typed rooted (by simpa [endEq] using source.effects)
  exact ⟨child, declaration, variableAt, typingEq, rootsEq, by simpa [typeEq] using passable⟩

theorem StmtSource.rebindChild {cfg : Cfg} {env : Env} {state : St} {slot : VarId}
    {expr : Expr} {origin : OriginId} (source : StmtSource cfg env (.rebind slot expr origin) state) :
    ∃ child : ExprSource cfg env expr state, ∃ declaration : LocalVar,
      env.vars[slot]? = some declaration ∧ child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty.passableTo declaration.ty = true := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, _, declaration, variableAt, _, _, ty, finish, typed, passable, _⟩ := typed
  rw [source.frame.vars_t] at variableAt
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨roots, finishRoots, rooted, _, final⟩ := rooted
  have effects : EffLe finishRoots.eff source.world.E := by
    refine EffLe.trans ?_ source.effects
    rcases final with ⟨_, endEq⟩ | ⟨_, endEq⟩
    · rw [endEq]
      exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩
    · rw [endEq]
      exact EffLe.refl _
  have childAt : (DemandNode.statement (.rebind slot expr origin)).child? 0 = some (.expression expr) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨child, typingEq, rootsEq, typeEq, _⟩ := source.firstExpressionChildSource expr childAt
    (by simp [DemandNode.visibleForChild]) (by simp [Stmt.variables])
    (fun parent => parent.future) (by intro parent x member; exact List.mem_append_right _ member)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
    source.typingStart finish ty source.rootsStart finishRoots roots typed rooted effects
  exact ⟨child, declaration, variableAt, typingEq, rootsEq, by simpa [typeEq] using passable⟩

theorem StmtSource.retChild {cfg : Cfg} {env : Env} {state : St}
    {expr : Expr} {origin : OriginId} (source : StmtSource cfg env (.ret (some expr) origin) state) :
    ∃ child : ExprSource cfg env expr state, ∃ implementation target,
      source.typingEnv.impl = some implementation ∧ implementation.results.toList = [target] ∧
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
      child.ty.passableTo target = true := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, target, start, returnType, ty, finish, typed, passable, _⟩ := typed
  obtain ⟨startEq, _, implementation, implementationAt, resultType⟩ := retTy_ok _ _ _ returnType
  simp only at startEq resultType
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨roots, finishRoots, rooted, _, endEq⟩ := rooted
  have childAt : (DemandNode.statement (.ret (some expr) origin)).child? 0 = some (.expression expr) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨child, typingEq, rootsEq, typeEq, _⟩ := source.firstExpressionChildSource expr childAt
    (by simp [DemandNode.visibleForChild]) (by simp [Stmt.variables])
    (fun parent => parent.future) (by intro parent x member; exact List.mem_append_right _ member)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
    start finish ty source.rootsStart finishRoots roots typed rooted
    (by simpa [endEq] using source.effects)
  exact ⟨child, implementation, target, implementationAt, resultType, typingEq, rootsEq,
    by simpa [typeEq] using passable⟩

private theorem ifConditionData {cfg : Cfg} {env : Env} {state : St} {condition : Expr}
    {yes : Block} {no : Option Block} {origin : OriginId}
    (source : StmtSource cfg env (.ifS condition yes no origin) state) :
    ∃ child : ExprSource cfg env condition state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = .bool ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.context.outputFuture =
        (source.context.child rfl 0 (.expression condition) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
  have typed := source.typed
  have rooted := source.rooted
  have childAt : (DemandNode.statement (.ifS condition yes no origin)).child? 0 = some (.expression condition) := by
    simp [DemandNode.child?, DemandNode.children]
  have build : ∀ finish roots finishRoots,
      tyExpr source.typingEnv condition source.typingStart = .ok (.bool, finish) →
      rpExpr source.rootsEnv condition source.rootsStart = .ok (roots, finishRoots) →
      EffLe finishRoots.eff source.world.E →
      (∃ child : ExprSource cfg env condition state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = .bool ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.context.outputFuture =
        (source.context.child rfl 0 (.expression condition) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation) := by
    intro finish roots finishRoots typed rooted effects
    apply source.firstExpressionChildSource condition childAt
      (by simp [DemandNode.visibleForChild])
      (by intro x member; cases no <;> simp [Stmt.variables, member])
      (fun parent => yes.variables ++ no.toList.flatMap Block.variables ++ parent.future)
      (by
        intro parent x member
        have included := List.mem_append_right condition.variables member
        cases no <;> simpa [Stmt.variables, List.append_assoc] using included)
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
      source.typingStart finish .bool source.rootsStart finishRoots roots typed rooted effects
  cases no with
  | none =>
    simp only [tyStmt] at typed
    inv at typed
    obtain ⟨_, ty, finish, conditionTyped, typeEq, _, _, _, _⟩ := typed
    simp only [rpStmt] at rooted
    inv at rooted
    obtain ⟨roots, finishRoots, conditionRooted, _, _, _, branchRooted⟩ := rooted
    have typeEq : ty = .bool := by simpa using typeEq
    subst ty
    exact build finish roots finishRoots conditionTyped conditionRooted
      ((rpBlockValue_mono branchRooted).2.trans source.effects)
  | some no =>
    simp only [tyStmt] at typed
    inv at typed
    obtain ⟨_, ty, finish, conditionTyped, typeEq, _, _, _, _, _, _, _⟩ := typed
    simp only [rpStmt] at rooted
    inv at rooted
    obtain ⟨roots, finishRoots, conditionRooted, _, _, _, _, yesRooted, _, _, _, noRooted⟩ := rooted
    have typeEq : ty = .bool := by simpa using typeEq
    subst ty
    exact build finish roots finishRoots conditionTyped conditionRooted
      ((rpBlockValue_mono yesRooted).2.trans ((rpBlockValue_mono noRooted).2.trans source.effects))

theorem StmtSource.ifConditionChild {cfg : Cfg} {env : Env} {state : St} {condition : Expr}
    {yes : Block} {no : Option Block} {origin : OriginId}
    (source : StmtSource cfg env (.ifS condition yes no origin) state) :
    ∃ child : ExprSource cfg env condition state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = .bool := by
  obtain ⟨child, typingEq, rootsEq, typeEq, _⟩ := ifConditionData source
  exact ⟨child, typingEq, rootsEq, typeEq⟩

private theorem blockGam_scope {env : Env} {scope : Nat} {newScope : ScopeInst}
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

theorem blockSource_reserved {cfg : Cfg} {env : Env} {state : St}
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
      source.context.outputFuture = context.outputFuture ∧
      source.context.retained = context.retained ∧
      source.context.mayShrink world.ownerP observation = context.mayShrink world.ownerP observation ∧
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
    exact ⟨annotation, located, blockGam_scope (frame.scopes_t ▸ fresh) gam,
      fun ownerType => blockGam_scope (frame.scopes_t ▸ fresh) (owner ownerType)⟩
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
    effects := effects, rootsEscape := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩
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

private theorem blockSourceAt {cfg : Cfg} {env : Env} {stmt : Stmt} {before state : St}
    (source : StmtSource cfg env stmt before) (block : Block) (typingEnv : TEnv)
    (path : List Nat) (context : EvaluationContext cfg.mod source.plans path (.block block) .block)
    (active : context.ActiveMatches typingEnv) (access : context.AccessMatches typingEnv source.rootsEnv)
    (protection : ShrinkProtected source.world.D source.world.A (context.mayShrink source.world.ownerP source.observation))
    (observed : ObservedSafe cfg.mod source.world (context.mayShrink source.world.ownerP source.observation) source.observation state.store)
    (classified : cfg.mod.profile = .shrink → ClassifiedParameters cfg.mod source.world.P source.world.D source.observation state.store)
    (frame : Core.Sound.Frame cfg.mod source.world typingEnv source.rootsEnv env state context.inputFuture)
    (typingStart typingEnd : Nat) (ty : Ty) (rootsStart rootsEnd : RState) (roots : List RootRef) (range : Nat × Nat)
    (typed : tyBlock typingEnv [] block typingStart = .ok (ty, typingEnd))
    (rooted : rpBlockValue source.rootsEnv [] block rootsStart = .ok ((roots, range), rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E) :
    ∃ child : BlockSource cfg env [] block state, child.typingEnv = typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧ child.observation = source.observation ∧ child.context.outputFuture = context.outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation = context.mayShrink source.world.ownerP source.observation := by
  cases block with
  | mk scope stmts value =>
    obtain ⟨fresh, inner, start, final, middle, declared, typedStmts, typedValue⟩ :=
      tyBlock_ok _ _ _ _ _ _ _ _ typed
    obtain ⟨same, visible, _, _⟩ := declarePre_ok _ _ _ _ _ _ declared
    obtain ⟨_, rootMiddle, rootedStmts, rootedValue, escaped, _⟩ := rpBlockValue_ok _ _ _ _ _ _ _ _ _ rooted
    have innerActive : context.ActiveMatches inner := by
      cases context <;> intro x
      all_goals exact (active x).trans (by simpa using (visible x).symm)
    refine ⟨{
      accepted := source.accepted, plans := source.plans, path := path, context := context,
      observation := source.observation, world := source.world, typingEnv := typingEnv,
      typingInner := inner, typingAfter := final, rootsEnv := source.rootsEnv,
      typingStart := start, typingValue := middle, typingEnd := typingEnd, ty := ty,
      rootsStart := rootsStart, rootsValue := rootMiddle, rootsEnd := rootsEnd, roots := roots,
      lowerBound := rootsStart.nextVar, active := innerActive, access := access,
      protection := protection, observed := observed, classified := classified, permission := source.permission,
      frame := frame, fresh := fresh, same := same, visible := visible,
      pretyped := ⟨List.nodup_nil, by intro slot v member; cases member⟩,
      bounded := Nat.le_refl _, typed := typedStmts, typedValue := ?_, rooted := rootedStmts,
      rootedValue := ?_, effects := effects, rootsEscape := escaped }, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases value with
      | none => exact typedValue.1
      | some expr => exact typedValue
    · cases value <;> exact rootedValue

private theorem conditionBlockInput {cfg : Cfg} {env : Env} {stmt : Stmt} {before state : St}
    (source : StmtSource cfg env stmt before) (condition : Expr) (block : Block) (index : Nat)
    (conditionAt : (DemandNode.statement stmt).child? 0 = some (.expression condition))
    (blockAt : (DemandNode.statement stmt).child? index = some (.block block))
    (conditionFuture blockFuture : DemandPoint → List VarId)
    (conditionExpectation : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 0 =
      some ⟨(DemandNode.statement stmt).visibleForChild parent.active 0, conditionFuture parent⟩)
    (blockExpectation : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent index =
      some ⟨(DemandNode.statement stmt).visibleForChild parent.active index, blockFuture parent⟩)
    (visible : ∀ active, (DemandNode.statement stmt).visibleForChild active 0 = active ∧
      (DemandNode.statement stmt).visibleForChild active index = active)
    (needed : ∀ parent, (∀ x, x ∈ parent.active ↔ x ∈ source.typingEnv.visible) →
      ∀ x, x ∈ source.typingEnv.visible → x ∈ block.variables ++ blockFuture parent → x ∈ conditionFuture parent)
    (frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (source.context.child rfl 0 (.expression condition) .expression conditionAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (source.context.child rfl index (.block block) .block blockAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  cases hcontext : source.context with
  | pilot profile active =>
    rw [hcontext] at frame
    have condActive : (DemandNode.statement stmt).visibleForChild active 0 = active := (visible active).1
    have bodyActive : (DemandNode.statement stmt).visibleForChild active index = active := (visible active).2
    change Core.Sound.Frame _ _ _ _ _ _ (block.variables ++ (DemandNode.statement stmt).visibleForChild active index)
    rw [bodyActive]
    change Core.Sound.Frame _ _ _ _ _ _ ((DemandNode.statement stmt).visibleForChild active 0) at frame
    rw [condActive] at frame
    apply frame.changeFuture
    intro x member _
    have activeMatches := source.active
    rw [hcontext] at activeMatches
    exact (activeMatches x).mpr member
  | shrink profile context =>
    rw [hcontext] at frame
    let cond := context.child rfl 0 (.expression condition) .expression conditionAt
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    let body := context.child rfl index (.block block) .block blockAt
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    change Core.Sound.Frame _ _ _ _ _ _ cond.context.expected.frame.future at frame
    change Core.Sound.Frame _ _ _ _ _ _ (block.variables ++ body.context.expected.frame.future)
    rw [cond.expectedFrameEq, DemandNode.phaseFrame_future cond.phaseFrameEq,
      DemandNode.childFrame_future cond.childFrameEq (conditionExpectation _ _)] at frame
    rw [body.expectedFrameEq, DemandNode.phaseFrame_future body.phaseFrameEq,
      DemandNode.childFrame_future body.childFrameEq (blockExpectation _ _)]
    apply frame.changeFuture
    intro x member future
    apply needed _ ?_ x member future
    intro y
    have activeMatches := source.active
    rw [hcontext] at activeMatches
    exact activeMatches y

private theorem ifBlockAt {cfg : Cfg} {env : Env} {state after : St} {condition : Expr}
    {yes : Block} {no : Option Block} {origin : OriginId}
    (source : StmtSource cfg env (.ifS condition yes no origin) state)
    (fuel : Nat) (value : Bool)
    (done : evalExpr fuel cfg env condition state = .ok (.bool value) after)
    (block : Block) (index : Nat)
    (blockAt : (DemandNode.statement (.ifS condition yes no origin)).child? index = some (.block block))
    (visible : ∀ active, (DemandNode.statement (.ifS condition yes no origin)).visibleForChild active index = active)
    (expectation : ∀ access parent,
      (DemandNode.statement (.ifS condition yes no origin)).childExpectation? access parent index =
        some ⟨parent.active, parent.future⟩)
    (included : ∀ x, x ∈ block.variables → x ∈ yes.variables ++ no.toList.flatMap Block.variables)
    (start finish : Nat) (ty : Ty) (rootStart rootFinish : RState) (roots : List RootRef) (range : Nat × Nat)
    (typed : tyBlock source.typingEnv [] block start = .ok (ty, finish))
    (rooted : rpBlockValue source.rootsEnv [] block rootStart = .ok ((roots, range), rootFinish))
    (effects : EffLe rootFinish.eff source.world.E) :
    ∃ child : BlockSource cfg env [] block after, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧ child.observation = source.observation := by
  obtain ⟨conditionSource, typingEq, rootsEq, _, worldEq, observationEq, outputEq, mayEq⟩ := ifConditionData source
  have result := conditionSource.result fuel (.bool value) done
  have frame := result.frame
  rw [typingEq, rootsEq, worldEq, outputEq] at frame
  have observed := result.observed
  rw [worldEq, observationEq, mayEq] at observed
  have classified := result.classified
  rw [worldEq, observationEq] at classified
  have conditionAt : (DemandNode.statement (.ifS condition yes no origin)).child? 0 = some (.expression condition) := by
    simp [DemandNode.child?, DemandNode.children]
  have phase : DemandNodeHasPhase (.block block) .block := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let context := source.context.child rfl index (.block block) .block blockAt phase
  have input := conditionBlockInput source condition block index conditionAt blockAt
    (fun parent => yes.variables ++ no.toList.flatMap Block.variables ++ parent.future)
    (fun parent => parent.future)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, conditionAt])
    (by intro access parent; rw [expectation, visible])
    (by intro active; exact ⟨by simp [DemandNode.visibleForChild], visible active⟩)
    (by
      intro parent _ x _ member
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (included x h)) (List.mem_append_right _)) frame
  have may : context.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl index (.block block) .block blockAt phase
      source.world.ownerP source.observation root)
  obtain ⟨child, typingEq, rootsEq, worldEq, observationEq, _⟩ := blockSourceAt source block source.typingEnv (source.path ++ [index]) context
    (source.context.child_activeMatches rfl index (.block block) .block blockAt phase
      source.typingEnv source.typingEnv source.active (by intro x; rw [visible]))
    ((source.context.child_accessMatches_iff rfl index (.block block) .block blockAt phase _ _).mpr source.access)
    (may ▸ source.protection) (may ▸ observed) classified input start finish ty rootStart rootFinish roots range typed rooted effects
  exact ⟨child, typingEq, rootsEq, worldEq, observationEq⟩

theorem StmtSource.ifThenChild {cfg : Cfg} {env : Env} {state after : St} {condition : Expr}
    {yes : Block} {no : Option Block} {origin : OriginId}
    (source : StmtSource cfg env (.ifS condition yes no origin) state)
    (fuel : Nat) (done : evalExpr fuel cfg env condition state = .ok (.bool true) after) :
    ∃ child : BlockSource cfg env [] yes after, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧ child.observation = source.observation := by
  have typed := source.typed
  have rooted := source.rooted
  cases no with
  | none =>
    simp only [tyStmt] at typed
    inv at typed
    obtain ⟨_, _, conditionEnd, _, _, yesTy, yesEnd, yesTyped, _, _⟩ := typed
    simp only [rpStmt] at rooted
    inv at rooted
    obtain ⟨_, conditionRoots, _, yesRoots, yesLow, yesHigh, yesRooted⟩ := rooted
    apply ifBlockAt source fuel true done yes 1
      (by simp [DemandNode.child?, DemandNode.children])
      (by intro active; simp [DemandNode.visibleForChild])
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
      (by intro x member; simp [member])
      conditionEnd yesEnd yesTy conditionRoots source.rootsEnd
      yesRoots (yesLow, yesHigh) yesTyped yesRooted
      source.effects
  | some no =>
    simp only [tyStmt] at typed
    inv at typed
    obtain ⟨_, _, conditionEnd, _, _, yesTy, yesEnd, yesTyped, noTy, noEnd, noTyped, _, _⟩ := typed
    simp only [rpStmt] at rooted
    inv at rooted
    obtain ⟨_, conditionRoots, _, yesRoots, yesLow, yesHigh, yesFinish, yesRooted, noRoots, noLow, noHigh, noRooted⟩ := rooted
    apply ifBlockAt source fuel true done yes 1
      (by simp [DemandNode.child?, DemandNode.children])
      (by intro active; simp [DemandNode.visibleForChild])
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
      (by intro x member; simp [member])
      conditionEnd yesEnd yesTy conditionRoots yesFinish
      yesRoots (yesLow, yesHigh) yesTyped yesRooted
      ((rpBlockValue_mono noRooted).2.trans source.effects)
theorem StmtSource.ifElseChild {cfg : Cfg} {env : Env} {state after : St} {condition : Expr}
    {yes : Block} {no : Block} {origin : OriginId}
    (source : StmtSource cfg env (.ifS condition yes (some no) origin) state)
    (fuel : Nat) (done : evalExpr fuel cfg env condition state = .ok (.bool false) after) :
    ∃ child : BlockSource cfg env [] no after, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧ child.observation = source.observation := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, _, conditionEnd, _, _, yesTy, yesEnd, yesTyped, noTy, noEnd, noTyped, _, _⟩ := typed
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨_, conditionRoots, _, yesRoots, yesLow, yesHigh, yesFinish, yesRooted, noRoots, noLow, noHigh, noRooted⟩ := rooted
  apply ifBlockAt source fuel false done no 2
    (by simp [DemandNode.child?, DemandNode.children])
    (by intro active; simp [DemandNode.visibleForChild])
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    (by intro x member; simp [member])
    yesEnd noEnd noTy yesFinish source.rootsEnd
    noRoots (noLow, noHigh) noTyped noRooted
    source.effects

private theorem whileConditionData {cfg : Cfg} {env : Env} {state : St} {condition : Expr}
    {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.while condition body origin) state) :
    ∃ child : ExprSource cfg env condition state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = .bool ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.context.outputFuture =
        (source.context.child rfl 0 (.expression condition) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
  have typed := source.typed
  have rooted := source.rooted
  have childAt : (DemandNode.statement (.while condition body origin)).child? 0 = some (.expression condition) := by
    simp [DemandNode.child?, DemandNode.children]
  have build : ∀ finish roots finishRoots,
      tyExpr source.typingEnv condition source.typingStart = .ok (.bool, finish) →
      rpExpr source.rootsEnv condition source.rootsStart = .ok (roots, finishRoots) →
      EffLe finishRoots.eff source.world.E →
      (∃ child : ExprSource cfg env condition state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = .bool ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.context.outputFuture =
        (source.context.child rfl 0 (.expression condition) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation) := by
    intro finish roots finishRoots typed rooted effects
    apply source.firstExpressionChildSource condition childAt
      (by simp [DemandNode.visibleForChild])
      (by intro x member; simp [Stmt.variables, member])
      (fun parent => parent.active.filter (condition.variables ++ body.variables).contains ++ parent.future)
      (by
        intro parent x member
        cases List.mem_append.mp member with
        | inl filtered =>
          have used : x ∈ condition.variables ++ body.variables := by
            simpa [List.mem_filter, List.contains_iff_mem] using (List.mem_filter.mp filtered).2
          simpa [Stmt.variables] using List.mem_append_left parent.future used
        | inr future => exact List.mem_append_right _ future)
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
      source.typingStart finish .bool source.rootsStart finishRoots roots typed rooted effects
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, ty, finish, conditionTyped, typeEq, _, _, _, _, _⟩ := typed
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨roots, finishRoots, conditionRooted, _, _, _, branchRooted⟩ := rooted
  have typeEq : ty = .bool := by simpa using typeEq
  subst ty
  exact build finish roots finishRoots conditionTyped conditionRooted
    ((rpBlockValue_mono branchRooted).2.trans source.effects)

theorem StmtSource.whileConditionChild {cfg : Cfg} {env : Env} {state : St} {condition : Expr}
    {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.while condition body origin) state) :
    ∃ child : ExprSource cfg env condition state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = .bool := by
  obtain ⟨child, typingEq, rootsEq, typeEq, _⟩ := whileConditionData source
  exact ⟨child, typingEq, rootsEq, typeEq⟩

private theorem whileBodyData {cfg : Cfg} {env : Env} {state after : St} {condition : Expr}
    {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.while condition body origin) state)
    (fuel : Nat) (done : evalExpr fuel cfg env condition state = .ok (.bool true) after) :
    ∃ child : BlockSource cfg env [] body after,
      child.typingEnv = { source.typingEnv with loops := source.typingEnv.loops + 1 } ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧ child.observation = source.observation ∧
      child.context.outputFuture =
        (source.context.child rfl 1 (.block body) .block
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
  obtain ⟨conditionSource, typingEq, rootsEq, _, worldEq, observationEq, outputEq, mayEq⟩ := whileConditionData source
  have result := conditionSource.result fuel (.bool true) done
  have frame := result.frame
  rw [typingEq, rootsEq, worldEq, outputEq] at frame
  have observed := result.observed
  rw [worldEq, observationEq, mayEq] at observed
  have classified := result.classified
  rw [worldEq, observationEq] at classified
  have conditionAt : (DemandNode.statement (.while condition body origin)).child? 0 = some (.expression condition) := by
    simp [DemandNode.child?, DemandNode.children]
  have bodyAt : (DemandNode.statement (.while condition body origin)).child? 1 = some (.block body) := by
    simp [DemandNode.child?, DemandNode.children]
  have phase : DemandNodeHasPhase (.block body) .block := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let context := source.context.child rfl 1 (.block body) .block bodyAt phase
  have input := conditionBlockInput source condition body 1 conditionAt bodyAt
    (fun parent => parent.active.filter (condition.variables ++ body.variables).contains ++ parent.future)
    (fun parent => parent.active.filter (condition.variables ++ body.variables).contains ++ parent.future)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, conditionAt])
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, bodyAt])
    (by intro active; simp [DemandNode.visibleForChild])
    (by
      intro parent activeEq x visible member
      cases List.mem_append.mp member with
      | inl used =>
        apply List.mem_append_left
        apply List.mem_filter.mpr
        exact ⟨(activeEq x).mpr visible, by simpa [List.contains_iff_mem] using List.mem_append_right condition.variables used⟩
      | inr future => exact future) frame
  have may : context.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl 1 (.block body) .block bodyAt phase
      source.world.ownerP source.observation root)
  have typed := source.typed
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, _, conditionEnd, _, _, bodyTy, bodyEnd, bodyTyped, _, _⟩ := typed
  have rooted := source.rooted
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨_, conditionRoots, _, bodyRoots, low, high, bodyRooted⟩ := rooted
  obtain ⟨child, typingEq, rootsEq, worldEq, observationEq, outputEq, shrinkEq⟩ := blockSourceAt source body
    { source.typingEnv with loops := source.typingEnv.loops + 1 } (source.path ++ [1]) context
    (source.context.child_activeMatches rfl 1 (.block body) .block bodyAt phase
      source.typingEnv { source.typingEnv with loops := source.typingEnv.loops + 1 }
      source.active (by intro x; simp [DemandNode.visibleForChild]))
    ((source.context.child_accessMatches_iff rfl 1 (.block body) .block bodyAt phase _ _).mpr source.access)
    (may ▸ source.protection) (may ▸ observed) classified
    (input.tenv_congr rfl rfl rfl (fun _ member => member)) conditionEnd bodyEnd bodyTy
    conditionRoots source.rootsEnd bodyRoots (low, high) bodyTyped bodyRooted source.effects
  exact ⟨child, typingEq, rootsEq, worldEq, observationEq, outputEq, shrinkEq.trans may⟩

theorem StmtSource.whileBodyChild {cfg : Cfg} {env : Env} {state after : St} {condition : Expr}
    {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.while condition body origin) state)
    (fuel : Nat) (done : evalExpr fuel cfg env condition state = .ok (.bool true) after) :
    ∃ child : BlockSource cfg env [] body after,
      child.typingEnv = { source.typingEnv with loops := source.typingEnv.loops + 1 } ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧ child.observation = source.observation := by
  obtain ⟨child, typingEq, rootsEq, worldEq, observationEq, _⟩ := whileBodyData source fuel done
  exact ⟨child, typingEq, rootsEq, worldEq, observationEq⟩

theorem StmtSource.whileAfterBody {cfg : Cfg} {env : Env} {state afterCondition after : St}
    {condition : Expr} {body : Block} {origin : OriginId}
    (source : StmtSource cfg env (.while condition body origin) state)
    (conditionFuel bodyFuel : Nat) (flow : Flow)
    (conditionDone : evalExpr conditionFuel cfg env condition state = .ok (.bool true) afterCondition)
    (bodyDone : execBlock bodyFuel cfg env [] body afterCondition = .ok flow after)
    (_reentry : (∃ value, flow = .normal value) ∨ flow = .cont) :
    ∃ next : StmtSource cfg env (.while condition body origin) after,
      next.typingEnv = source.typingEnv ∧ next.rootsEnv = source.rootsEnv ∧
      next.world = source.world ∧ next.observation = source.observation := by
  obtain ⟨conditionSource, conditionTyping, conditionRoots, _, conditionWorld, _, _, _⟩ := whileConditionData source
  have conditionResult := conditionSource.result conditionFuel (.bool true) conditionDone
  obtain ⟨bodySource, bodyTyping, bodyRoots, bodyWorld, bodyObservation, bodyOutput, bodyMay⟩ := whileBodyData source conditionFuel conditionDone
  have bodyResult := bodySource.result bodyFuel flow bodyDone
  have frame := bodyResult.frame
  rw [bodyTyping, bodyRoots, bodyWorld, bodyOutput] at frame
  have frame := frame.tenv_congr (t2 := source.typingEnv) rfl rfl rfl (fun _ member => member)
  have bodyAt : (DemandNode.statement (.while condition body origin)).child? 1 = some (.block body) := by
    simp [DemandNode.child?, DemandNode.children]
  have input : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after source.context.inputFuture := by
    cases hcontext : source.context with
    | pilot profile active =>
      rw [hcontext] at frame
      change Core.Sound.Frame _ _ _ _ _ _ active at frame
      simp only [EvaluationContext.inputFuture, DemandNode.variables, Stmt.variables]
      change Core.Sound.Frame _ _ _ _ _ _ ((condition.variables ++ body.variables) ++ active)
      apply frame.changeFuture
      intro x member _
      have activeEq := source.active
      rw [hcontext] at activeEq
      exact (activeEq x).mpr member
    | shrink profile context =>
      rw [hcontext] at frame
      let child := context.child rfl 1 (.block body) .block bodyAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      change Core.Sound.Frame _ _ _ _ _ _ child.context.expected.frame.future at frame
      rw [child.expectedFrameEq, DemandNode.phaseFrame_future child.phaseFrameEq,
        DemandNode.childFrame_future child.childFrameEq (show
          (DemandNode.statement (.while condition body origin)).childExpectation? _
            ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩ 1 =
            some ⟨context.expected.frame.active, context.expected.frame.active.filter (condition.variables ++ body.variables).contains ++ context.expected.frame.future⟩ from by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.visibleForChild, bodyAt])] at frame
      simp only [EvaluationContext.inputFuture, NodeContext.inputFuture, DemandNode.variables, Stmt.variables]
      change Core.Sound.Frame _ _ _ _ _ _ ((condition.variables ++ body.variables) ++ context.expected.frame.future)
      apply frame.changeFuture
      intro x visible member
      cases List.mem_append.mp member with
      | inl used =>
        apply List.mem_append_left
        apply List.mem_filter.mpr
        have activeEq := source.active
        rw [hcontext] at activeEq
        exact ⟨(activeEq x).mpr visible, by simpa [List.contains_iff_mem] using used⟩
      | inr future => exact List.mem_append_right _ future
  have observed := bodyResult.observed
  rw [bodyWorld, bodyObservation, bodyMay] at observed
  have classified := bodyResult.classified
  rw [bodyWorld, bodyObservation] at classified
  have top := source.top.ext (cur' := source.rootsStart.nextVar)
    (fun root member => conditionResult.footprint.dom root (bodyResult.footprint.dom root member)) (Nat.le_refl _)
  exact ⟨{ source with frame := input, observed := observed, classified := classified, top := top }, rfl, rfl, rfl, rfl⟩

theorem StmtSource.assertChild {cfg : Cfg} {env : Env} {state : St} {expr : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assertS expr origin) state) :
    ∃ child : ExprSource cfg env expr state,
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
      child.ty = .bool := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, ty, finish, typed, typeEq, _, _⟩ := typed
  have typeEq : ty = .bool := by simpa using typeEq
  subst ty
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨roots, finishRoots, rooted, aborts⟩ := rooted
  have childAt : (DemandNode.statement (.assertS expr origin)).child? 0 = some (.expression expr) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨child, typingEq, rootsEq, typeEq, _⟩ := source.firstExpressionChildSource expr childAt
    (by simp [DemandNode.visibleForChild]) (by simp [Stmt.variables])
    (fun parent => parent.future) (by intro parent x member; exact List.mem_append_right _ member)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
    source.typingStart finish .bool source.rootsStart finishRoots roots typed rooted
    ((PMono.noteAborts _ _ _ aborts).2.trans source.effects)
  exact ⟨child, typingEq, rootsEq, typeEq⟩

theorem StmtSource.exitChild {cfg : Cfg} {env : Env} {state : St} {expr : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.exit expr origin) state) :
    ∃ child : ExprSource cfg env expr state, ∃ integer : IntTy,
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
      child.ty = .int integer := by
  have typed := source.typed
  have rooted := source.rooted
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, ty, finish, typed, integer, typeEq, _, _⟩ := typed
  have typeEq : ty = .int integer := by simpa using typeEq
  subst ty
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨roots, finishRoots, rooted, aborts⟩ := rooted
  have childAt : (DemandNode.statement (.exit expr origin)).child? 0 = some (.expression expr) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨child, typingEq, rootsEq, typeEq, _⟩ := source.firstExpressionChildSource expr childAt
    (by simp [DemandNode.visibleForChild]) (by simp [Stmt.variables])
    (fun parent => parent.future) (by intro parent x member; exact List.mem_append_right _ member)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, childAt])
    source.typingStart finish (.int integer) source.rootsStart finishRoots roots typed rooted
    ((PMono.noteAborts _ _ _ aborts).2.trans source.effects)
  exact ⟨child, integer, typingEq, rootsEq, typeEq⟩

theorem StmtSource.placeChildSource {cfg : Cfg} {env : Env} {stmt : Stmt} {state : St}
    (source : StmtSource cfg env stmt state) (place : Place)
    (childAt : (DemandNode.statement stmt).child? 0 = some (.place place))
    (visible : ∀ x, x ∈ source.typingEnv.visible ↔
      x ∈ (DemandNode.statement stmt).visibleForChild source.typingEnv.visible 0)
    (variables : ∀ x, x ∈ place.variables → x ∈ stmt.variables)
    (futureVariables : DemandPoint → List VarId)
    (futureSubset : ∀ parent x, x ∈ futureVariables parent → x ∈ stmt.variables ++ parent.future)
    (future : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 0 =
      some ⟨(DemandNode.statement stmt).visibleForChild parent.active 0, futureVariables parent⟩)
    (typingStart typingEnd : Nat) (ty : Ty) (mutable contents : Bool) (rootsStart rootsEnd : RState) (roots : List RootRef)
    (typed : tyPlace source.typingEnv place typingStart = .ok (⟨ty, mutable, contents⟩, typingEnd))
    (rooted : rpPlace source.rootsEnv place rootsStart = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E) :
    ∃ child : PlaceSource cfg env place state, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.ty = ty ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.context.outputFuture =
        (source.context.child rfl 0 (.place place) .place childAt
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation ∧
      child.mutable = mutable ∧ child.contents = contents ∧ child.roots = roots := by
  let ec := source.context
  have phase : DemandNodeHasPhase (.place place) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let child := ec.child rfl 0 (.place place) .place childAt phase
  have may : child.mayShrink source.world.ownerP source.observation =
      ec.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.place place) .place childAt phase
      source.world.ownerP source.observation root)
  have input : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state child.inputFuture := by
    apply source.frame.narrowFuture
    intro x member
    change x ∈ ec.inputFuture
    change x ∈ (ec.child rfl 0 (.place place) .place childAt phase).inputFuture at member
    cases hcontext : ec with
    | pilot profile active =>
      rw [hcontext] at member
      change x ∈ place.variables ++ (DemandNode.statement stmt).visibleForChild active 0 at member
      have activeEq : (DemandNode.statement stmt).visibleForChild active 0 = active := by
        cases stmt <;> simp [DemandNode.visibleForChild]
      rw [activeEq] at member
      change x ∈ stmt.variables ++ active
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (variables x h)) (List.mem_append_right _)
    | shrink profile context =>
      rw [hcontext] at member
      let transition := context.child rfl 0 (.place place) .place childAt phase
      change x ∈ place.variables ++ transition.context.expected.frame.future at member
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        DemandNode.childFrame_future transition.childFrameEq (future _ _)] at member
      change x ∈ stmt.variables ++ context.expected.frame.future
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (variables x h)) (futureSubset _ x)
  refine ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [0], context := child,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := typingStart, typingEnd := typingEnd, ty := ty, mutable := mutable, contents := contents,
    rootsStart := rootsStart, rootsEnd := rootsEnd, roots := roots,
    active := ec.child_activeMatches rfl 0 (.place place) .place childAt phase
      source.typingEnv source.typingEnv source.active visible,
    access := (ec.child_accessMatches_iff rfl 0 (.place place) .place childAt phase _ _).mpr source.access,
    protection := may ▸ source.protection, observed := may ▸ source.observed,
    classified := source.classified, permission := source.permission, frame := input,
    typed := typed, rooted := rooted, effects := effects }, rfl, rfl, rfl, rfl, rfl, rfl, may, rfl, rfl, rfl⟩

private theorem afterPlaceExpression {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {expr : Expr} {stmt : Stmt}
    (source : StmtSource cfg env stmt state)
    (placeAt : (DemandNode.statement stmt).child? 0 = some (.place place))
    (expressionAt : (DemandNode.statement stmt).child? 1 = some (.expression expr))
    (visible : ∀ active, (DemandNode.statement stmt).visibleForChild active 0 = active ∧
      (DemandNode.statement stmt).visibleForChild active 1 = active)
    (futureVariables : DemandPoint → List VarId)
    (placeExpectation : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 0 =
      some ⟨parent.active, expr.variables ++ futureVariables parent⟩)
    (expressionExpectation : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 1 =
      some ⟨parent.active, futureVariables parent⟩)
    (destination : PlaceSource cfg env place state)
    (typingEq : destination.typingEnv = source.typingEnv) (rootsEq : destination.rootsEnv = source.rootsEnv)
    (worldEq : destination.world = source.world) (observationEq : destination.observation = source.observation)
    (outputEq : destination.context.outputFuture =
      (source.context.child rfl 0 (.place place) .place
        placeAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture)
    (mayEq : destination.context.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation)
    (typingStart typingEnd : Nat) (ty : Ty) (rootsStart rootsEnd : RState) (roots : List RootRef)
    (typed : tyExpr source.typingEnv expr typingStart = .ok (ty, typingEnd))
    (rooted : rpExpr source.rootsEnv expr rootsStart = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E)
    (fuel : Nat) (location : Loc) (done : evalPlace fuel cfg env place state = .ok location after) :
    ∃ child : ExprSource cfg env expr after, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧
      child.observation = source.observation ∧ child.ty = ty ∧
      child.context.outputFuture = (source.context.child rfl 1 (.expression expr) .expression expressionAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
  have result := destination.result fuel location done
  have frame := result.frame
  rw [typingEq, rootsEq, worldEq, outputEq] at frame
  have observed := result.observed
  rw [worldEq, observationEq, mayEq] at observed
  have classified := result.classified
  rw [worldEq, observationEq] at classified
  have phase : DemandNodeHasPhase (.expression expr) .expression := by simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let context := source.context.child rfl 1 (.expression expr) .expression expressionAt phase
  have input : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after context.inputFuture := by
    change Core.Sound.Frame _ _ _ _ _ _ (source.context.child rfl 1 (.expression expr) .expression expressionAt phase).inputFuture
    cases hcontext : source.context with
    | pilot profile active =>
      rw [hcontext] at frame
      change Core.Sound.Frame _ _ _ _ _ _ ((DemandNode.statement stmt).visibleForChild active 0) at frame
      rw [(visible active).1] at frame
      change Core.Sound.Frame _ _ _ _ _ _ (expr.variables ++ (DemandNode.statement stmt).visibleForChild active 1)
      rw [(visible active).2]
      apply frame.changeFuture
      intro x member _
      have activeEq := source.active
      rw [hcontext] at activeEq
      exact (activeEq x).mpr member
    | shrink profile context =>
      rw [hcontext] at frame
      let first := context.child rfl 0 (.place place) .place placeAt (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      let next := context.child rfl 1 (.expression expr) .expression expressionAt phase
      change Core.Sound.Frame _ _ _ _ _ _ first.context.expected.frame.future at frame
      change Core.Sound.Frame _ _ _ _ _ _ (expr.variables ++ next.context.expected.frame.future)
      rw [first.expectedFrameEq, DemandNode.phaseFrame_future first.phaseFrameEq,
        DemandNode.childFrame_future first.childFrameEq (show
          (DemandNode.statement stmt).childExpectation? _
            ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩ 0 =
            some ⟨context.expected.frame.active, expr.variables ++ futureVariables ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩⟩ from by
          exact placeExpectation _ _)] at frame
      rw [next.expectedFrameEq, DemandNode.phaseFrame_future next.phaseFrameEq,
        DemandNode.childFrame_future next.childFrameEq (show
          (DemandNode.statement stmt).childExpectation? _
            ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩ 1 =
            some ⟨context.expected.frame.active, futureVariables ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩⟩ from by
          exact expressionExpectation _ _)]
      exact frame
  have may : context.mayShrink source.world.ownerP source.observation = source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl 1 (.expression expr) .expression expressionAt phase source.world.ownerP source.observation root)
  exact ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [1], context := context,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := typingStart, typingEnd := typingEnd, ty := ty,
    rootsStart := rootsStart, rootsEnd := rootsEnd, roots := roots,
    active := source.context.child_activeMatches rfl 1 (.expression expr) .expression expressionAt phase
      source.typingEnv source.typingEnv source.active (by intro x; rw [(visible source.typingEnv.visible).2]),
    access := (source.context.child_accessMatches_iff rfl 1 (.expression expr) .expression expressionAt phase _ _).mpr source.access,
    protection := may ▸ source.protection, observed := may ▸ observed, classified := classified,
    permission := source.permission, frame := input, typed := typed, rooted := rooted, effects := effects }, rfl, rfl, rfl, rfl, rfl, rfl, may⟩

theorem StmtSource.assignChildren {cfg : Cfg} {env : Env} {state : St}
    {place : Place} {expr : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place expr origin) state) :
    ∃ destination : PlaceSource cfg env place state,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      destination.world = source.world ∧ destination.observation = source.observation ∧
      ∀ fuel location after, evalPlace fuel cfg env place state = .ok location after →
        ∃ child : ExprSource cfg env expr after, child.typingEnv = source.typingEnv ∧
          child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧
          child.observation = source.observation ∧ child.ty = destination.ty := by
  have typed := source.typed
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, ty, mutable, contents, placeEnd, placeTyped, _, exprTy, exprEnd, exprTyped, typeEq, _, _, _⟩ := typed
  have typeEq : exprTy = ty := by simpa using typeEq
  subst exprTy
  have rooted := source.rooted
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨placeRoots, placeFinish, placeRooted, exprRoots, exprFinish, exprRooted, _, writesFinish, writes, endEq⟩ := rooted
  have effects : EffLe exprFinish.eff source.world.E := by
    have writeEffects := (PMono.addWrites _ _ _ _ writes).2
    have finalEffects : EffLe writesFinish.eff source.rootsEnd.eff := by
      rw [endEq]
      exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩
    exact writeEffects.trans (finalEffects.trans source.effects)
  have placeAt : (DemandNode.statement (.assign place expr origin)).child? 0 = some (.place place) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨destination, typingEq, rootsEq, destinationTy, worldEq, observationEq, outputEq, mayEq, _⟩ :=
    source.placeChildSource place placeAt (by simp [DemandNode.visibleForChild])
      (by intro x member; simp [Stmt.variables, member])
      (fun parent => expr.variables ++ parent.future)
      (by intro parent x member; simpa [Stmt.variables, List.append_assoc] using List.mem_append_right place.variables member)
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, placeAt])
      source.typingStart placeEnd ty mutable contents source.rootsStart placeFinish placeRoots placeTyped placeRooted
      ((rpExpr_mono exprRooted).2.trans effects)
  refine ⟨destination, typingEq, rootsEq, worldEq, observationEq, ?_⟩
  intro fuel location after done
  obtain ⟨child, childTyping, childRoots, childWorld, childObservation, childTy, _⟩ := afterPlaceExpression source placeAt
    (by simp [DemandNode.child?, DemandNode.children])
    (by intro active; simp [DemandNode.visibleForChild]) (fun parent => parent.future)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild]) destination
    typingEq rootsEq worldEq observationEq outputEq mayEq placeEnd exprEnd ty placeFinish exprFinish exprRoots exprTyped exprRooted effects fuel location done
  exact ⟨child, childTyping, childRoots, childWorld, childObservation, childTy.trans destinationTy.symm⟩

theorem StmtSource.clearChild {cfg : Cfg} {env : Env} {state : St} {place : Place} {origin : OriginId}
    (source : StmtSource cfg env (.clear place origin) state) :
    ∃ child : PlaceSource cfg env place state, ∃ element : Ty,
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
      child.world = source.world ∧ child.observation = source.observation ∧
      child.ty.ownerElem? = some element ∧ child.contents = true := by
  have typed := source.typed
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨start, _, _, ty, mutable, contents, placeEnd, placeTyped, element, elementEnd, elementTyped, writable, _, _⟩ := typed
  have contentsEq : contents = true := by simpa using writable
  have elementEq := (ownerElement_ok _ _ _ _ _ elementTyped).2.1
  have rooted := source.rooted
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨roots, placeFinish, placeRooted, readFinish, reads, shrinks⟩ := rooted
  have effects := (PMono.addReads _ _ _ _ reads).2.trans ((PMono.addShrinks _ _ _ _ shrinks).2.trans source.effects)
  have placeAt : (DemandNode.statement (.clear place origin)).child? 0 = some (.place place) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨child, typingEq, rootsEq, typeEq, worldEq, observationEq, _, _, _, contentsEqChild, _⟩ :=
    source.placeChildSource place placeAt (by simp [DemandNode.visibleForChild])
      (by simp [Stmt.variables]) (fun parent => parent.future)
      (by intro parent x member; exact List.mem_append_right _ member)
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, placeAt])
      start placeEnd ty mutable contents source.rootsStart placeFinish roots placeTyped placeRooted effects
  exact ⟨child, element, typingEq, rootsEq, worldEq, observationEq, by rw [typeEq]; exact elementEq, contentsEqChild.trans contentsEq⟩

theorem StmtSource.popNChildren {cfg : Cfg} {env : Env} {state : St}
    {place : Place} {expr : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.popN place expr origin) state) :
    ∃ destination : PlaceSource cfg env place state, ∃ element : Ty,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      destination.world = source.world ∧ destination.observation = source.observation ∧
      destination.ty.ownerElem? = some element ∧ destination.contents = true ∧
      ∀ fuel location after, evalPlace fuel cfg env place state = .ok location after →
        ∃ child : ExprSource cfg env expr after, ∃ integer : IntTy,
          child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
          child.world = source.world ∧ child.observation = source.observation ∧ child.ty = .int integer := by
  have typed := source.typed
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨start, _, _, ty, mutable, contents, placeEnd, placeTyped, element, elementEnd, elementTyped,
    exprTy, exprEnd, exprTyped, integer, integerEq, writable, _, _⟩ := typed
  have elementEq := (ownerElement_ok _ _ _ _ _ elementTyped).2.1
  have contentsEq : contents = true := by simpa using writable
  have rooted := source.rooted
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨placeRoots, placeFinish, placeRooted, exprRoots, exprFinish, exprRooted, readFinish, reads,
    shrinkFinish, shrinks, aborts⟩ := rooted
  have effects := (PMono.addReads _ _ _ _ reads).2.trans
    ((PMono.addShrinks _ _ _ _ shrinks).2.trans ((PMono.noteAborts _ _ _ aborts).2.trans source.effects))
  have placeAt : (DemandNode.statement (.popN place expr origin)).child? 0 = some (.place place) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨destination, typingEq, rootsEq, destinationTy, worldEq, observationEq, outputEq, mayEq, _, destinationContents, _⟩ :=
    source.placeChildSource place placeAt (by simp [DemandNode.visibleForChild])
      (by intro x member; simp [Stmt.variables, member])
      (fun parent => expr.variables ++ parent.future)
      (by intro parent x member; simpa [Stmt.variables, List.append_assoc] using List.mem_append_right place.variables member)
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, placeAt])
      start placeEnd ty mutable contents source.rootsStart placeFinish placeRoots placeTyped placeRooted
      ((rpExpr_mono exprRooted).2.trans effects)
  refine ⟨destination, element, typingEq, rootsEq, worldEq, observationEq,
    by rw [destinationTy]; exact elementEq, destinationContents.trans contentsEq, ?_⟩
  intro fuel location after done
  obtain ⟨child, childTyping, childRoots, childWorld, childObservation, childTy, _⟩ := afterPlaceExpression source placeAt
    (by simp [DemandNode.child?, DemandNode.children])
    (by intro active; simp [DemandNode.visibleForChild]) (fun parent => parent.future)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    destination typingEq rootsEq worldEq observationEq outputEq mayEq elementEnd exprEnd _
    placeFinish exprFinish exprRoots exprTyped exprRooted effects fuel location done
  exact ⟨child, _, childTyping, childRoots, childWorld, childObservation, childTy.trans integerEq⟩

private theorem resizeSizeAt {cfg : Cfg} {env : Env} {state : St}
    {place : Place} {expr : Expr} {fill : Option Expr} {origin : OriginId}
    (source : StmtSource cfg env (.resize place expr fill origin) state)
    (start placeEnd sizeStart sizeEnd : Nat) (ty element : Ty) (mutable contents : Bool)
    (integer : IntTy) (placeTyped : tyPlace source.typingEnv place start = .ok (⟨ty, mutable, contents⟩, placeEnd))
    (sizeTyped : tyExpr source.typingEnv expr sizeStart = .ok (.int integer, sizeEnd))
    (elementEq : ty.ownerElem? = some element) (contentsEq : contents = true)
    (placeRoots sizeRoots : List RootRef) (placeFinish sizeFinish : RState)
    (placeRooted : rpPlace source.rootsEnv place source.rootsStart = .ok (placeRoots, placeFinish))
    (sizeRooted : rpExpr source.rootsEnv expr placeFinish = .ok (sizeRoots, sizeFinish))
    (effects : EffLe sizeFinish.eff source.world.E) :
    ∃ destination : PlaceSource cfg env place state, ∃ element : Ty,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      destination.world = source.world ∧ destination.observation = source.observation ∧
      destination.ty.ownerElem? = some element ∧ destination.contents = true ∧
      ∀ fuel location after, evalPlace fuel cfg env place state = .ok location after →
        ∃ child : ExprSource cfg env expr after, ∃ integer : IntTy,
          child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
          child.world = source.world ∧ child.observation = source.observation ∧ child.ty = .int integer ∧
          child.context.outputFuture = (source.context.child rfl 1 (.expression expr) .expression
            (by simp [DemandNode.child?, DemandNode.children])
            (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
          child.context.mayShrink source.world.ownerP source.observation = source.context.mayShrink source.world.ownerP source.observation := by
  have placeAt : (DemandNode.statement (.resize place expr fill origin)).child? 0 = some (.place place) := by simp [DemandNode.child?, DemandNode.children]
  obtain ⟨destination, typingEq, rootsEq, destinationTy, worldEq, observationEq, outputEq, mayEq, _, destinationContents, _⟩ :=
    source.placeChildSource place placeAt (by simp [DemandNode.visibleForChild])
      (by intro x member; cases fill <;> simp [Stmt.variables, member])
      (fun parent => expr.variables ++ fill.toList.flatMap Expr.variables ++ parent.future)
      (by
        intro parent x member
        cases fill <;> simpa [Stmt.variables, List.append_assoc] using List.mem_append_right place.variables member)
      (by intro access parent; cases fill <;> simp [DemandNode.childExpectation?, DemandNode.childFuture, placeAt, List.append_assoc])
      start placeEnd ty mutable contents source.rootsStart placeFinish placeRoots placeTyped placeRooted
      ((rpExpr_mono sizeRooted).2.trans effects)
  refine ⟨destination, element, typingEq, rootsEq, worldEq, observationEq,
    by rw [destinationTy]; exact elementEq, destinationContents.trans contentsEq, ?_⟩
  intro fuel location after done
  obtain ⟨child, childTyping, childRoots, childWorld, childObservation, childTy, childOutput, childMay⟩ := afterPlaceExpression source placeAt
    (by simp [DemandNode.child?, DemandNode.children])
    (by intro active; simp [DemandNode.visibleForChild])
    (fun parent => fill.toList.flatMap Expr.variables ++ parent.future)
    (by intro access parent; cases fill <;> simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild, List.append_assoc])
    (by intro access parent; cases fill <;> simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    destination typingEq rootsEq worldEq observationEq outputEq mayEq sizeStart sizeEnd (.int integer)
    placeFinish sizeFinish sizeRoots sizeTyped sizeRooted effects fuel location done
  exact ⟨child, integer, childTyping, childRoots, childWorld, childObservation, childTy, childOutput, childMay⟩

private theorem resizeSizeData {cfg : Cfg} {env : Env} {state : St}
    {place : Place} {expr : Expr} {fill : Option Expr} {origin : OriginId}
    (source : StmtSource cfg env (.resize place expr fill origin) state) :
    ∃ destination : PlaceSource cfg env place state, ∃ element : Ty,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      destination.world = source.world ∧ destination.observation = source.observation ∧
      destination.ty.ownerElem? = some element ∧ destination.contents = true ∧
      ∀ fuel location after, evalPlace fuel cfg env place state = .ok location after →
        ∃ child : ExprSource cfg env expr after, ∃ integer : IntTy,
          child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
          child.world = source.world ∧ child.observation = source.observation ∧ child.ty = .int integer ∧
          child.context.outputFuture = (source.context.child rfl 1 (.expression expr) .expression
            (by simp [DemandNode.child?, DemandNode.children])
            (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
          child.context.mayShrink source.world.ownerP source.observation = source.context.mayShrink source.world.ownerP source.observation := by
  have typed := source.typed
  rw [tyStmt] at typed
  obtain ⟨_, start, _, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  obtain ⟨_, ownerStart, _, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  obtain ⟨info, placeEnd, placeTyped, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  obtain ⟨ty, mutable, contents⟩ := info
  obtain ⟨element, sizeStart, elementTyped, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  obtain ⟨sizeTy, sizeEnd, sizeTyped, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  obtain ⟨integer, fillStart, integerTyped, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  have elementEq := (ownerElement_ok _ _ _ _ _ elementTyped).2.1
  have integerEq : sizeTy = .int integer := ((requireInt_ok _ _ _ _).1 integerTyped).1
  rw [integerEq] at sizeTyped
  have rooted := source.rooted
  rw [rpStmt] at rooted
  obtain ⟨placeRoots, placeFinish, placeRooted, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨sizeRoots, sizeFinish, sizeRooted, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  cases fill with
  | none =>
    simp only at typed rooted
    obtain ⟨_, _, writable, _⟩ := (st_bind_ok _ _ _ _).1 typed
    have contentsEq : contents = true := (requireWrite_ok _ _ _ _).1 writable |>.1
    obtain ⟨_, readFinish, reads, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
    obtain ⟨_, shrinkFinish, shrinks, aborts⟩ := (st_bind_ok _ _ _ _).1 rooted
    have effects := (PMono.addReads _ _ _ _ reads).2.trans ((PMono.addShrinks _ _ _ _ shrinks).2.trans ((PMono.noteAborts _ _ _ aborts).2.trans source.effects))
    exact resizeSizeAt source ownerStart placeEnd sizeStart sizeEnd ty element mutable contents integer
      placeTyped sizeTyped elementEq contentsEq placeRoots sizeRoots placeFinish sizeFinish placeRooted sizeRooted effects
  | some fill =>
    simp only at typed rooted
    obtain ⟨fillTy, _, _, typed⟩ := (st_bind_ok _ _ _ _).1 typed
    inv at typed
    obtain ⟨_, contentsEq, _, _⟩ := typed
    obtain ⟨fillRoots, fillFinish, fillRooted, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
    obtain ⟨_, writeFinish, writes, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
    obtain ⟨_, growFinish, grows, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
    obtain ⟨_, readFinish, reads, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
    obtain ⟨_, shrinkFinish, shrinks, aborts⟩ := (st_bind_ok _ _ _ _).1 rooted
    have effects := (rpExpr_mono fillRooted).2.trans ((PMono.addWrites _ _ _ _ writes).2.trans
      ((PMono.addGrows _ _ _ _ grows).2.trans ((PMono.addReads _ _ _ _ reads).2.trans
        ((PMono.addShrinks _ _ _ _ shrinks).2.trans ((PMono.noteAborts _ _ _ aborts).2.trans source.effects)))))
    exact resizeSizeAt source ownerStart placeEnd sizeStart sizeEnd ty element mutable contents integer
      placeTyped sizeTyped elementEq contentsEq placeRoots sizeRoots placeFinish sizeFinish placeRooted sizeRooted effects

theorem StmtSource.resizeSizeChildren {cfg : Cfg} {env : Env} {state : St}
    {place : Place} {expr : Expr} {fill : Option Expr} {origin : OriginId}
    (source : StmtSource cfg env (.resize place expr fill origin) state) :
    ∃ destination : PlaceSource cfg env place state, ∃ element : Ty,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      destination.world = source.world ∧ destination.observation = source.observation ∧
      destination.ty.ownerElem? = some element ∧ destination.contents = true ∧
      ∀ fuel location after, evalPlace fuel cfg env place state = .ok location after →
        ∃ child : ExprSource cfg env expr after, ∃ integer : IntTy,
          child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
          child.world = source.world ∧ child.observation = source.observation ∧ child.ty = .int integer := by
  obtain ⟨destination, element, typingEq, rootsEq, worldEq, observationEq, elementEq, contentsEq, children⟩ := resizeSizeData source
  refine ⟨destination, element, typingEq, rootsEq, worldEq, observationEq, elementEq, contentsEq, ?_⟩
  intro fuel location after done
  obtain ⟨child, integer, typingEq, rootsEq, worldEq, observationEq, typeEq, _⟩ := children fuel location after done
  exact ⟨child, integer, typingEq, rootsEq, worldEq, observationEq, typeEq⟩

private theorem afterExpressionExpression {cfg : Cfg} {env : Env} {state afterFirst after : St}
    {first : Expr} {expr : Expr} {stmt : Stmt}
    (source : StmtSource cfg env stmt state)
    (firstAt : (DemandNode.statement stmt).child? 1 = some (.expression first))
    (expressionAt : (DemandNode.statement stmt).child? 2 = some (.expression expr))
    (visible : ∀ active, (DemandNode.statement stmt).visibleForChild active 1 = active ∧
      (DemandNode.statement stmt).visibleForChild active 2 = active)
    (futureVariables : DemandPoint → List VarId)
    (firstExpectation : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 1 =
      some ⟨parent.active, expr.variables ++ futureVariables parent⟩)
    (expressionExpectation : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 2 =
      some ⟨parent.active, futureVariables parent⟩)
    (destination : ExprSource cfg env first afterFirst)
    (typingEq : destination.typingEnv = source.typingEnv) (rootsEq : destination.rootsEnv = source.rootsEnv)
    (worldEq : destination.world = source.world) (observationEq : destination.observation = source.observation)
    (outputEq : destination.context.outputFuture =
      (source.context.child rfl 1 (.expression first) .expression
        firstAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture)
    (mayEq : destination.context.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation)
    (typingStart typingEnd : Nat) (ty : Ty) (rootsStart rootsEnd : RState) (roots : List RootRef)
    (typed : tyExpr source.typingEnv expr typingStart = .ok (ty, typingEnd))
    (rooted : rpExpr source.rootsEnv expr rootsStart = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E)
    (fuel : Nat) (value : Val) (done : evalExpr fuel cfg env first afterFirst = .ok value after) :
    ∃ child : ExprSource cfg env expr after, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧
      child.observation = source.observation ∧ child.ty = ty ∧
      child.context.outputFuture = (source.context.child rfl 2 (.expression expr) .expression expressionAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
  have result := destination.result fuel value done
  have frame := result.frame
  rw [typingEq, rootsEq, worldEq, outputEq] at frame
  have observed := result.observed
  rw [worldEq, observationEq, mayEq] at observed
  have classified := result.classified
  rw [worldEq, observationEq] at classified
  have phase : DemandNodeHasPhase (.expression expr) .expression := by simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let context := source.context.child rfl 2 (.expression expr) .expression expressionAt phase
  have input : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after context.inputFuture := by
    change Core.Sound.Frame _ _ _ _ _ _ (source.context.child rfl 2 (.expression expr) .expression expressionAt phase).inputFuture
    cases hcontext : source.context with
    | pilot profile active =>
      rw [hcontext] at frame
      change Core.Sound.Frame _ _ _ _ _ _ ((DemandNode.statement stmt).visibleForChild active 1) at frame
      rw [(visible active).1] at frame
      change Core.Sound.Frame _ _ _ _ _ _ (expr.variables ++ (DemandNode.statement stmt).visibleForChild active 2)
      rw [(visible active).2]
      apply frame.changeFuture
      intro x member _
      have activeEq := source.active
      rw [hcontext] at activeEq
      exact (activeEq x).mpr member
    | shrink profile context =>
      rw [hcontext] at frame
      let first := context.child rfl 1 (.expression first) .expression firstAt (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      let next := context.child rfl 2 (.expression expr) .expression expressionAt phase
      change Core.Sound.Frame _ _ _ _ _ _ first.context.expected.frame.future at frame
      change Core.Sound.Frame _ _ _ _ _ _ (expr.variables ++ next.context.expected.frame.future)
      rw [first.expectedFrameEq, DemandNode.phaseFrame_future first.phaseFrameEq,
        DemandNode.childFrame_future first.childFrameEq (show
          (DemandNode.statement stmt).childExpectation? _
            ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩ 1 =
            some ⟨context.expected.frame.active, expr.variables ++ futureVariables ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩⟩ from by
          exact firstExpectation _ _)] at frame
      rw [next.expectedFrameEq, DemandNode.phaseFrame_future next.phaseFrameEq,
        DemandNode.childFrame_future next.childFrameEq (show
          (DemandNode.statement stmt).childExpectation? _
            ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩ 2 =
            some ⟨context.expected.frame.active, futureVariables ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩⟩ from by
          exact expressionExpectation _ _)]
      exact frame
  have may : context.mayShrink source.world.ownerP source.observation = source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl 2 (.expression expr) .expression expressionAt phase source.world.ownerP source.observation root)
  exact ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [2], context := context,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := typingStart, typingEnd := typingEnd, ty := ty,
    rootsStart := rootsStart, rootsEnd := rootsEnd, roots := roots,
    active := source.context.child_activeMatches rfl 2 (.expression expr) .expression expressionAt phase
      source.typingEnv source.typingEnv source.active (by intro x; rw [(visible source.typingEnv.visible).2]),
    access := (source.context.child_accessMatches_iff rfl 2 (.expression expr) .expression expressionAt phase _ _).mpr source.access,
    protection := may ▸ source.protection, observed := may ▸ observed, classified := classified,
    permission := source.permission, frame := input, typed := typed, rooted := rooted, effects := effects }, rfl, rfl, rfl, rfl, rfl, rfl, may⟩

theorem StmtSource.resizeFillChild {cfg : Cfg} {env : Env} {state afterPlace afterSize : St}
    {place : Place} {expr fill : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.resize place expr (some fill) origin) state)
    (placeFuel sizeFuel : Nat) (location : Loc) (value : Val)
    (placeDone : evalPlace placeFuel cfg env place state = .ok location afterPlace)
    (sizeDone : evalExpr sizeFuel cfg env expr afterPlace = .ok value afterSize) :
    ∃ child : ExprSource cfg env fill afterSize, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧ child.observation = source.observation := by
  obtain ⟨destination, element, _, _, _, _, _, _, children⟩ := resizeSizeData source
  obtain ⟨sizeSource, integer, typingEq, rootsEq, worldEq, observationEq, _, outputEq, mayEq⟩ := children placeFuel location afterPlace placeDone
  have typed := source.typed
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨start, _, _, ty, mutable, contents, placeEnd, _, element, elementEnd, _,
    sizeTy, sizeEnd, _, integer, _, fillTy, fillEnd, fillTyped, fillEq, _, _, _⟩ := typed
  have rooted := source.rooted
  rw [rpStmt] at rooted
  obtain ⟨placeRoots, placeFinish, _, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨sizeRoots, sizeFinish, _, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨fillRoots, fillFinish, fillRooted, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨_, writeFinish, writes, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨_, growFinish, grows, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨_, readFinish, reads, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨_, shrinkFinish, shrinks, aborts⟩ := (st_bind_ok _ _ _ _).1 rooted
  have effects := (PMono.addWrites _ _ _ _ writes).2.trans
    ((PMono.addGrows _ _ _ _ grows).2.trans ((PMono.addReads _ _ _ _ reads).2.trans
      ((PMono.addShrinks _ _ _ _ shrinks).2.trans ((PMono.noteAborts _ _ _ aborts).2.trans source.effects))))
  obtain ⟨child, childTyping, childRoots, childWorld, childObservation, _⟩ := afterExpressionExpression source
    (by simp [DemandNode.child?, DemandNode.children])
    (by simp [DemandNode.child?, DemandNode.children])
    (by intro active; simp [DemandNode.visibleForChild]) (fun parent => parent.future)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    sizeSource typingEq rootsEq worldEq observationEq outputEq mayEq sizeEnd fillEnd fillTy
    sizeFinish fillFinish fillRoots fillTyped fillRooted effects sizeFuel value sizeDone
  exact ⟨child, childTyping, childRoots, childWorld, childObservation⟩

theorem StmtSource.assignOpChildren {cfg : Cfg} {env : Env} {state : St}
    {op : BinOp} {place : Place} {expr : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assignOp op place expr origin) state) :
    ∃ destination : PlaceSource cfg env place state,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      destination.world = source.world ∧ destination.observation = source.observation ∧
      ∀ fuel location after, evalPlace fuel cfg env place state = .ok location after →
        ∃ child : ExprSource cfg env expr after, child.typingEnv = source.typingEnv ∧
          child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧
          child.observation = source.observation ∧ child.ty = destination.ty := by
  have typed := source.typed
  simp only [tyStmt] at typed
  inv at typed
  obtain ⟨_, ty, mutable, contents, placeEnd, placeTyped, integer, rfl,
    exprTy, exprEnd, exprTyped, exprInteger, rfl, rfl, _, _, _⟩ := typed
  have rooted := source.rooted
  simp only [rpStmt] at rooted
  inv at rooted
  obtain ⟨placeRoots, placeFinish, placeRooted, exprRoots, exprFinish, exprRooted,
    readFinish, reads, writeFinish, writes, final⟩ := rooted
  have finalEffects : EffLe writeFinish.eff source.world.E := by
    apply EffLe.trans _ source.effects
    cases final with
    | inl aborts => exact (PMono.noteAborts _ _ _ aborts.2).2
    | inr unchanged => exact unchanged.2 ▸ EffLe.refl _
  have effects := (PMono.addReads _ _ _ _ reads).2.trans ((PMono.addWrites _ _ _ _ writes).2.trans finalEffects)
  have placeAt : (DemandNode.statement (.assignOp op place expr origin)).child? 0 = some (.place place) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨destination, typingEq, rootsEq, destinationTy, worldEq, observationEq, outputEq, mayEq, _⟩ :=
    source.placeChildSource place placeAt (by simp [DemandNode.visibleForChild])
      (by intro x member; simp [Stmt.variables, member])
      (fun parent => expr.variables ++ parent.future)
      (by intro parent x member; simpa [Stmt.variables, List.append_assoc] using List.mem_append_right place.variables member)
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, placeAt])
      source.typingStart placeEnd (.int integer) mutable contents source.rootsStart placeFinish placeRoots placeTyped placeRooted
      ((rpExpr_mono exprRooted).2.trans effects)
  refine ⟨destination, typingEq, rootsEq, worldEq, observationEq, ?_⟩
  intro fuel location after done
  obtain ⟨child, childTyping, childRoots, childWorld, childObservation, childTy, _⟩ := afterPlaceExpression source placeAt
    (by simp [DemandNode.child?, DemandNode.children])
    (by intro active; simp [DemandNode.visibleForChild]) (fun parent => parent.future)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild]) destination
    typingEq rootsEq worldEq observationEq outputEq mayEq placeEnd exprEnd (.int integer) placeFinish exprFinish exprRoots exprTyped exprRooted effects fuel location done
  exact ⟨child, childTyping, childRoots, childWorld, childObservation, childTy.trans destinationTy.symm⟩

private theorem afterPlaceView {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {view : View} {stmt : Stmt}
    (source : StmtSource cfg env stmt state)
    (placeAt : (DemandNode.statement stmt).child? 0 = some (.place place))
    (viewAt : (DemandNode.statement stmt).child? 1 = some (.view view))
    (visible : ∀ active, (DemandNode.statement stmt).visibleForChild active 0 = active ∧
      (DemandNode.statement stmt).visibleForChild active 1 = active)
    (futureVariables : DemandPoint → List VarId)
    (placeExpectation : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 0 =
      some ⟨parent.active, view.variables ++ futureVariables parent⟩)
    (expressionExpectation : ∀ access parent, (DemandNode.statement stmt).childExpectation? access parent 1 =
      some ⟨parent.active, futureVariables parent⟩)
    (destination : PlaceSource cfg env place state)
    (typingEq : destination.typingEnv = source.typingEnv) (rootsEq : destination.rootsEnv = source.rootsEnv)
    (worldEq : destination.world = source.world) (observationEq : destination.observation = source.observation)
    (outputEq : destination.context.outputFuture =
      (source.context.child rfl 0 (.place place) .place
        placeAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture)
    (mayEq : destination.context.mayShrink source.world.ownerP source.observation =
      source.context.mayShrink source.world.ownerP source.observation)
    (typingStart typingEnd : Nat) (ty : Ty) (mutable : Bool) (rootsStart rootsEnd : RState) (roots : List RootRef)
    (typed : tyView source.typingEnv view typingStart = .ok ((ty, mutable), typingEnd))
    (rooted : rpView source.rootsEnv view rootsStart = .ok (roots, rootsEnd))
    (effects : EffLe rootsEnd.eff source.world.E)
    (fuel : Nat) (location : Loc) (done : evalPlace fuel cfg env place state = .ok location after) :
    ∃ child : ViewSource cfg env view after, child.typingEnv = source.typingEnv ∧
      child.rootsEnv = source.rootsEnv ∧ child.world = source.world ∧
      child.observation = source.observation ∧ child.element = ty ∧
      child.context.outputFuture = (source.context.child rfl 1 (.view view) .view viewAt
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      child.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation := by
  have result := destination.result fuel location done
  have frame := result.frame
  rw [typingEq, rootsEq, worldEq, outputEq] at frame
  have observed := result.observed
  rw [worldEq, observationEq, mayEq] at observed
  have classified := result.classified
  rw [worldEq, observationEq] at classified
  have phase : DemandNodeHasPhase (.view view) .view := by simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let context := source.context.child rfl 1 (.view view) .view viewAt phase
  have input : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env after context.inputFuture := by
    change Core.Sound.Frame _ _ _ _ _ _ (source.context.child rfl 1 (.view view) .view viewAt phase).inputFuture
    cases hcontext : source.context with
    | pilot profile active =>
      rw [hcontext] at frame
      change Core.Sound.Frame _ _ _ _ _ _ ((DemandNode.statement stmt).visibleForChild active 0) at frame
      rw [(visible active).1] at frame
      change Core.Sound.Frame _ _ _ _ _ _ (view.variables ++ (DemandNode.statement stmt).visibleForChild active 1)
      rw [(visible active).2]
      apply frame.changeFuture
      intro x member _
      have activeEq := source.active
      rw [hcontext] at activeEq
      exact (activeEq x).mpr member
    | shrink profile context =>
      rw [hcontext] at frame
      let first := context.child rfl 0 (.place place) .place placeAt (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
      let next := context.child rfl 1 (.view view) .view viewAt phase
      change Core.Sound.Frame _ _ _ _ _ _ first.context.expected.frame.future at frame
      change Core.Sound.Frame _ _ _ _ _ _ (view.variables ++ next.context.expected.frame.future)
      rw [first.expectedFrameEq, DemandNode.phaseFrame_future first.phaseFrameEq,
        DemandNode.childFrame_future first.childFrameEq (show
          (DemandNode.statement stmt).childExpectation? _
            ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩ 0 =
            some ⟨context.expected.frame.active, view.variables ++ futureVariables ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩⟩ from by
          exact placeExpectation _ _)] at frame
      rw [next.expectedFrameEq, DemandNode.phaseFrame_future next.phaseFrameEq,
        DemandNode.childFrame_future next.childFrameEq (show
          (DemandNode.statement stmt).childExpectation? _
            ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩ 1 =
            some ⟨context.expected.frame.active, futureVariables ⟨source.path, .expression, context.expected.frame.active, context.expected.frame.future, context.expected.frame.retained⟩⟩ from by
          exact expressionExpectation _ _)]
      exact frame
  have may : context.mayShrink source.world.ownerP source.observation = source.context.mayShrink source.world.ownerP source.observation := by
    funext root
    exact propext (source.context.child_mayShrink_iff rfl 1 (.view view) .view viewAt phase source.world.ownerP source.observation root)
  exact ⟨{
    accepted := source.accepted, plans := source.plans, path := source.path ++ [1], context := context,
    observation := source.observation, world := source.world, typingEnv := source.typingEnv,
    rootsEnv := source.rootsEnv, typingStart := typingStart, typingEnd := typingEnd, element := ty, mutable := mutable,
    rootsStart := rootsStart, rootsEnd := rootsEnd, roots := roots,
    active := source.context.child_activeMatches rfl 1 (.view view) .view viewAt phase
      source.typingEnv source.typingEnv source.active (by intro x; rw [(visible source.typingEnv.visible).2]),
    access := (source.context.child_accessMatches_iff rfl 1 (.view view) .view viewAt phase _ _).mpr source.access,
    protection := may ▸ source.protection, observed := may ▸ observed, classified := classified,
    permission := source.permission, frame := input, typed := typed, rooted := rooted, effects := effects }, rfl, rfl, rfl, rfl, rfl, rfl, may⟩

theorem StmtSource.appendChildren {cfg : Cfg} {env : Env} {state : St}
    {place : Place} {view : View} {origin : OriginId}
    (source : StmtSource cfg env (.append place view origin) state) :
    ∃ destination : PlaceSource cfg env place state,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      ∀ fuel location after, evalPlace fuel cfg env place state = .ok location after →
        ∃ child : ViewSource cfg env view after, child.typingEnv = source.typingEnv ∧
          child.rootsEnv = source.rootsEnv := by
  have typed := source.typed
  simp only [tyStmt] at typed
  obtain ⟨_, start, _, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  obtain ⟨info, placeEnd, placeTyped, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  obtain ⟨element, elementEnd, _, typed⟩ := (st_bind_ok _ _ _ _).1 typed
  obtain ⟨⟨viewElement, mutable⟩, viewEnd, viewTyped, _⟩ := (st_bind_ok _ _ _ _).1 typed
  have rooted := source.rooted
  simp only [rpStmt] at rooted
  obtain ⟨placeRoots, placeFinish, placeRooted, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨viewRoots, viewFinish, viewRooted, rest⟩ := (st_bind_ok _ _ _ _).1 rooted
  have suffix := PMono.bind (PMono.addReads viewRoots) (fun _ =>
    PMono.bind (PMono.addGrows placeRoots) (fun _ =>
      PMono.profileWriteAbort source.rootsEnv place placeRoots))
  have effects := (suffix viewFinish () source.rootsEnd rest).2.trans source.effects
  have placeAt : (DemandNode.statement (.append place view origin)).child? 0 = some (.place place) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨destination, typingEq, rootsEq, _, worldEq, observationEq, outputEq, mayEq, _⟩ :=
    source.placeChildSource place placeAt (by simp [DemandNode.visibleForChild])
      (by intro x member; simp [Stmt.variables, member])
      (fun parent => view.variables ++ parent.future)
      (by intro parent x member; simpa [Stmt.variables, List.append_assoc] using List.mem_append_right place.variables member)
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, placeAt])
      start placeEnd info.ty info.bindingWritable info.contentsWritable source.rootsStart placeFinish
      placeRoots placeTyped placeRooted ((rpView_mono viewRooted).2.trans effects)
  refine ⟨destination, typingEq, rootsEq, ?_⟩
  intro fuel location after done
  obtain ⟨child, childTyping, childRoots, _⟩ := afterPlaceView source placeAt
    (by simp [DemandNode.child?, DemandNode.children])
    (by intro active; simp [DemandNode.visibleForChild]) (fun parent => parent.future)
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild])
    (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, DemandNode.child?, DemandNode.children, DemandNode.visibleForChild]) destination
    typingEq rootsEq worldEq observationEq outputEq mayEq elementEnd viewEnd viewElement mutable
    placeFinish viewFinish viewRoots viewTyped viewRooted effects fuel location done
  exact ⟨child, childTyping, childRoots⟩

end Goose.Lower
