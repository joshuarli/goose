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


end Goose.Lower
