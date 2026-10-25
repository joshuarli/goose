import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.DemandShortCircuit
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

def demandShortCircuitFork (isAnd : Bool) (left : Expr) (le : LEnv) (before : LS) :
    (BlockId × BlockId × ValueId) × LS :=
  scFork isAnd (lowerExpr left le before).1 le (lowerExpr left le before).2

def demandShortCircuitRightBefore (isAnd : Bool) (left : Expr) (le : LEnv) (before : LS) : LS :=
  { (demandShortCircuitFork isAnd left le before).2 with
    cur := some (demandShortCircuitFork isAnd left le before).1.1 }

def demandShortCircuitRightJump (isAnd : Bool) (left right : Expr) (le : LEnv) (before : LS) : LS :=
  (emitTerm (.br (demandShortCircuitFork isAnd left le before).1.2.1
    [(lowerExpr right le (demandShortCircuitRightBefore isAnd left le before)).1]) le
    (lowerExpr right le (demandShortCircuitRightBefore isAnd left le before)).2).2

theorem generated_shortCircuit_jump_extended {isAnd : Bool} {left right : Expr} {le : LEnv}
    {before : LS} {blocks : Array GIR.Block} {point : Pt}
    (atPoint : (lowerExpr left le before).2.pp = some point)
    (extended : ExtT (lowerExpr (if isAnd then .and left right else .or left right) le before).2 blocks) :
    ExtT (demandShortCircuitRightJump isAnd left right le before) blocks := by
  obtain ⟨block, current, _, _⟩ := LS.pp_some atPoint
  cases isAnd <;>
    simpa only [Bool.false_eq_true, ite_false, ite_true, lowerExpr, bind_run,
      shortCircuit, whenLive_some _ _ _ current, setCur_run, pure_run,
      demandShortCircuitRightJump, demandShortCircuitRightBefore, demandShortCircuitFork, ExtT] using extended

theorem generated_shortCircuit_right_extended {isAnd : Bool} {left right : Expr} {le : LEnv}
    {before : LS} {blocks : Array GIR.Block} {point : Pt}
    (atPoint : (lowerExpr left le before).2.pp = some point)
    (extended : ExtT (lowerExpr (if isAnd then .and left right else .or left right) le before).2 blocks) :
    ExtT (lowerExpr right le (demandShortCircuitRightBefore isAnd left le before)).2 blocks :=
  (generated_shortCircuit_jump_extended atPoint extended).of_adv (adv_emitTerm rfl)

theorem generated_shortCircuit_fork_extended {isAnd : Bool} {left right : Expr} {le : LEnv}
    {before : LS} {blocks : Array GIR.Block} {point : Pt}
    (atPoint : (lowerExpr left le before).2.pp = some point)
    (extended : ExtT (lowerExpr (if isAnd then .and left right else .or left right) le before).2 blocks) :
    ExtT (demandShortCircuitFork isAnd left le before).2 blocks := by
  have entered := (generated_shortCircuit_right_extended atPoint extended).of_adv
    (advB_lowerExpr right le (demandShortCircuitRightBefore isAnd left le before) _ _ rfl)
  exact entered

inductive GeneratedShortCircuitSite (m : Core.Module) (access : AccessEnv) :
    Func → RetainedSsaMap → DemandSourceLabel → Pt → Inst → Prop
  | fork {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {isAnd : Bool} {left right : Expr} {required : RetainedSsaMap} {aliases : List RetainedAlias} {point : Pt}
      (occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (if isAnd then .and left right else .or left right)) before)
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasExpr (path ++ [0]) left = .ok aliases)
      (atPoint : (lowerExpr left le before).2.pp = some point)
      (extended : ExtT (demandShortCircuitFork isAnd left le before).2 function.blocks) :
      GeneratedShortCircuitSite m access function
        (required.addValues (lowerExpr left le before).1 aliases)
        ⟨path ++ [0], .expression, .exit⟩ point
        (.term (scTerm isAnd (lowerExpr left le before).1
          (demandShortCircuitFork isAnd left le before).1.1
          (demandShortCircuitFork isAnd left le before).1.2.1))
  | rightJump {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {isAnd : Bool} {left right : Expr} {required : RetainedSsaMap} {aliases : List RetainedAlias} {point : Pt}
      (occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (if isAnd then .and left right else .or left right)) before)
      (rows : GeneratedDemandRows m access occurrence required)
      (query : access.aliasExpr (path ++ [0]) left = .ok aliases)
      (live : (lowerExpr left le before).2.cur.isSome = true)
      (atPoint : (lowerExpr right le (demandShortCircuitRightBefore isAnd left le before)).2.pp = some point)
      (extended : ExtT (emitTerm
        (.br (demandShortCircuitFork isAnd left le before).1.2.1
          [(lowerExpr right le (demandShortCircuitRightBefore isAnd left le before)).1]) le
        (lowerExpr right le (demandShortCircuitRightBefore isAnd left le before)).2).2 function.blocks) :
      GeneratedShortCircuitSite m access function
        (required.addValues (lowerExpr left le before).1 aliases)
        ⟨path ++ [1], .expression, .exit⟩ point
        (.term (.br (demandShortCircuitFork isAnd left le before).1.2.1
          [(lowerExpr right le (demandShortCircuitRightBefore isAnd left le before)).1]))

theorem GeneratedShortCircuitSite.instruction {m : Core.Module} {access : AccessEnv}
    {function : Func} {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {inst : Inst}
    (site : GeneratedShortCircuitSite m access function required label point inst) :
    instAt function point = some inst := by
  cases site with
  | fork occurrence rows query atPoint extended =>
    exact (scFork_facts rfl atPoint extended).2.2.2.2.2.2.1
  | rightJump occurrence rows query live atPoint extended =>
    exact (emitTerm_facts rfl atPoint extended).2.2.2

theorem GeneratedShortCircuitSite.source {m : Core.Module} {access : AccessEnv}
    {function : Func} {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {inst : Inst}
    (site : GeneratedShortCircuitSite m access function required label point inst) :
    ∃ (le : LEnv) (root : DemandNode) (expression : Expr) (before : LS),
      GeneratedDemandOccurrence m function le root label.path (.expression expression) before ∧
        label.phase = .expression ∧ label.boundary = .exit := by
  cases site with
  | @fork le root path before isAnd left right required aliases point occurrence rows query atPoint extended =>
    refine ⟨le, root, left, before, ?_, rfl, rfl⟩
    apply GeneratedDemandOccurrence.first occurrence
    apply DemandLoweringAction.FirstChild.expression
    cases isAnd <;> rfl
  | rightJump occurrence rows query live atPoint extended =>
    exact ⟨_, _, _, _, GeneratedDemandOccurrence.shortCircuitRight occurrence live, rfl, rfl⟩

theorem GeneratedShortCircuitSite.requiredRows {m : Core.Module} {access : AccessEnv}
    {function : Func} {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {inst : Inst}
    (site : GeneratedShortCircuitSite m access function required label point inst) :
    ∃ (le : LEnv) (root : DemandNode) (expression : Expr) (before : LS)
      (occurrence : GeneratedDemandOccurrence m function le root
        (label.path.dropLast ++ [1]) (.expression expression) before),
      GeneratedDemandRows m access occurrence required := by
  cases site with
  | @fork le root path before isAnd left right parentRequired aliases point occurrence rows query atPoint extended =>
    obtain ⟨block, current, _, _⟩ := LS.pp_some atPoint
    have live : (lowerExpr left le before).2.cur.isSome = true := by simp only [current, Option.isSome_some]
    simp only [List.dropLast_concat]
    exact ⟨le, root, right, _, .shortCircuitRight occurrence live, .shortCircuitRight (live := live) rows query⟩
  | rightJump occurrence rows query live atPoint extended =>
    simp only [List.dropLast_concat]
    exact ⟨_, _, _, _, .shortCircuitRight occurrence live, .shortCircuitRight (live := live) rows query⟩

theorem shortCircuit_left_rows_realize {cfg : Cfg} {env : Env} {expression : Expr} {state after : St}
    {source : ExprSource cfg env expression state} {map : RetainedSsaMap} {cx : FnCtx}
    {before built : LS} {initial frame : GIR.Frame} {point : Pt} {id : ValueId} {value : Val}
    (boundary : ExpressionDemandBoundary source map cx before initial built id value after point frame)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasExpr source.path expression = .ok aliases) :
    (map.addValues id aliases).Realizes cfg.mod source.world env ⟨point, frame, after⟩ := by
  constructor
  · intro cell member
    change cell ∈ aliases.map (fun alias => (id, alias)) ++ map.values at member
    rcases List.mem_append.mp member with produced | retained
    · obtain ⟨alias, aliasMember, rfl⟩ := List.mem_map.mp produced
      exact boundary.canonical aliases query alias aliasMember
    · exact boundary.demanded.operands.1 cell retained
  · exact boundary.demanded.operands.2

theorem shortCircuit_join_step {cx : FnCtx} {before forked : LS} {le : LEnv}
    {isAnd : Bool} {condition rhs join result value : Nat} {forkPoint point : Pt}
    {ended : LS} {frame : GIR.Frame} {state : St} {selected : Bool}
    (fork : scFork isAnd condition le before = ((rhs, join, result), forked))
    (forkAt : before.pp = some forkPoint) (forkExtended : ExtT forked cx.fn.blocks)
    (atPoint : ended.pp = some point)
    (extended : ExtT (emitTerm (.br join [value]) le ended).2 cx.fn.blocks)
    (cell : frame.vals[value]? = some (.val (.bool selected))) (fuel : Nat) :
    DemandInstructionStep cx fuel ⟨point, frame, state⟩
      ⟨(join, 0), frame.set result (.val (.bool selected)), state⟩ := by
  obtain ⟨_, _, _, _, _, _, _, _, joinAt⟩ := scFork_facts fork forkAt forkExtended
  obtain ⟨block, blockAt, parameters⟩ := forkExtended.params joinAt
  apply DemandInstructionStep.control (branch := .jump join [value])
    (emitTerm_facts rfl atPoint extended).2.2.2
  simp [DemandBranch.enter, mapList, getCell, cell, enterBlock, blockAt, parameters,
    bindParams, setCell_eq, instsAt, bind_apply, pure_apply]


theorem shortCircuit_rows_preserved {m : Core.Module} {world : World} {env : Env}
    {cx : FnCtx} {before forked : LS} {le : LEnv} {isAnd : Bool} {condition rhs join result : Nat}
    {point : Pt} {frame : GIR.Frame} {state : St} {map : RetainedSsaMap}
    (path : ShortCircuitPath)
    (fork : scFork isAnd condition le before = ((rhs, join, result), forked))
    (atPoint : before.pp = some point) (extended : ExtT forked cx.fn.blocks)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes m world env ⟨point, frame, state⟩) :
    map.Realizes m world env
      ⟨path.target rhs join, path.frame frame result isAnd, state⟩ := by
  cases path with
  | rhs => exact realized
  | skip =>
    obtain ⟨_, _, fresh, _⟩ := scFork_facts fork atPoint extended
    have same : Same before.vals.size frame (frame.set result (.val (.bool (!isAnd)))) := by
      rw [fresh]
      exact Same.set frame (Nat.le_refl _) _
    exact realized.retained same bounded.1 bounded.2 RetainsAliases.refl

theorem shortCircuit_join_rows_preserved {m : Core.Module} {world : World} {env : Env}
    {cx : FnCtx} {before forked : LS} {le : LEnv} {isAnd : Bool} {condition rhs join result : Nat}
    {forkPoint point : Pt} {frame : GIR.Frame} {state : St} {map : RetainedSsaMap} {selected : Bool}
    (fork : scFork isAnd condition le before = ((rhs, join, result), forked))
    (atPoint : before.pp = some forkPoint) (extended : ExtT forked cx.fn.blocks)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes m world env ⟨point, frame, state⟩) :
    map.Realizes m world env ⟨(join, 0), frame.set result (.val (.bool selected)), state⟩ := by
  obtain ⟨_, _, fresh, _⟩ := scFork_facts fork atPoint extended
  have same : Same before.vals.size frame (frame.set result (.val (.bool selected))) := by
    rw [fresh]
    exact Same.set frame (Nat.le_refl _) _
  exact realized.retained same bounded.1 bounded.2 RetainsAliases.refl

theorem shortCircuit_boundary_rows_preserved {cfg : Cfg} {env : Env} {expression : Expr} {state after : St}
    {source : ExprSource cfg env expression state} {map : RetainedSsaMap} {cx : FnCtx}
    {before built forked : LS} {initial frame : GIR.Frame} {point : Pt} {id rhs join result : ValueId}
    {isAnd : Bool} {le : LEnv} {aliases : List RetainedAlias}
    (path : ShortCircuitPath)
    (boundary : ExpressionDemandBoundary source map cx before initial built id
      (.bool (path.leftValue isAnd)) after point frame)
    (query : source.rootsEnv.access.aliasExpr source.path expression = .ok aliases)
    (fork : scFork isAnd id le built = ((rhs, join, result), forked))
    (extended : ExtT forked cx.fn.blocks) :
    (map.addValues id aliases).Realizes cfg.mod source.world env
      ⟨path.target rhs join, path.frame frame result isAnd, after⟩ := by
  have bounded : (map.addValues id aliases).Bounded built.vals.size := by
    constructor
    · intro cell member
      change cell ∈ aliases.map (fun alias => (id, alias)) ++ map.values at member
      rcases List.mem_append.mp member with produced | retained
      · obtain ⟨alias, _, rfl⟩ := List.mem_map.mp produced
        exact boundary.post.lt (id, .val (.bool (path.leftValue isAnd))) (by simp)
      · exact boundary.bounded.1 cell retained
    · exact boundary.bounded.2
  exact shortCircuit_rows_preserved path fork boundary.post.pp extended bounded
    (shortCircuit_left_rows_realize boundary query)

theorem accepted_generated_shortCircuit_branch {cfg : Cfg} {env : Env} {a b : Expr} {state after : St}
    (isAnd : Bool) (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state)
    (left : ExprSource cfg env a state) (world : left.world = source.world)
    (roots : left.rootsEnv = source.rootsEnv) (leftPath : left.path = source.path ++ [0])
    (leftType : left.ty = .bool)
    {sourceFuel : Nat} (path : ShortCircuitPath)
    (leftDone : evalExpr sourceFuel cfg env a state = .ok (.bool (path.leftValue isAnd)) after)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {point : Pt}
    {initial frame : GIR.Frame} {map required : RetainedSsaMap} {aliases : List RetainedAlias}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path
      (.expression (if isAnd then .and a b else .or a b)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (query : source.rootsEnv.access.aliasExpr (source.path ++ [0]) a = .ok aliases)
    (boundary : ExpressionDemandBoundary left map cx before initial (lowerExpr a le before).2
      (lowerExpr a le before).1 (.bool (path.leftValue isAnd)) after point frame)
    (extended : ExtT (demandShortCircuitFork isAnd a le before).2 cx.fn.blocks) (fuel : Nat) :
    let fork := demandShortCircuitFork isAnd a le before
    let carried := map.addValues (lowerExpr a le before).1 aliases
    let target := (⟨path.target fork.1.1 fork.1.2.1,
      path.frame frame fork.1.2.2 isAnd, after⟩ : DemandRuntimePoint)
    GeneratedShortCircuitSite cfg.mod source.rootsEnv.access cx.fn
      (required.addValues (lowerExpr a le before).1 aliases)
      ⟨source.path ++ [0], .expression, .exit⟩ point
      (.term (scTerm isAnd (lowerExpr a le before).1 fork.1.1 fork.1.2.1)) ∧
    carried.Covers (required.addValues (lowerExpr a le before).1 aliases) ∧
    ∃ right : ExprSource cfg env b after,
      right.world = source.world ∧ right.path = source.path ++ [1] ∧ right.plans = source.plans ∧
      HEq right.context (source.context.child rfl 1 (.expression b) .expression
        (by cases isAnd <;> rfl) (by trivial)) ∧
      carried.Bounded (lowerExpr a le before).2.vals.size ∧
      carried.Bounded (demandShortCircuitRightBefore isAnd a le before).vals.size ∧
      carried.Admitted cfg.mod.profile right.context.retained ∧
      DemandInstructionStep cx fuel ⟨point, frame, after⟩ target ∧
      (match path with
      | .rhs => DemandFrameAt cfg env cx right.world right.typingEnv right.rootsEnv
          right.context.inputFuture carried.values carried.runs target
      | .skip => DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
          source.context.outputFuture carried.values carried.runs target) ∧
      carried.Realizes cfg.mod source.world env target := by
  dsimp only
  refine ⟨.fork occurrence rows query boundary.post.pp extended, ?_, ?_⟩
  · constructor
    · intro cell member
      change cell ∈ aliases.map (fun alias => ((lowerExpr a le before).1, alias)) ++ required.values at member
      change cell ∈ aliases.map (fun alias => ((lowerExpr a le before).1, alias)) ++ map.values
      rcases List.mem_append.mp member with produced | retained
      · exact List.mem_append_left _ produced
      · exact List.mem_append_right _ (coverage.1 cell retained)
    · exact coverage.2
  · have canonical : left.rootsEnv.access.aliasExpr left.path a = .ok aliases := by
      rw [roots, leftPath]
      exact query
    have lookup := tyExpr_accessType (left.frame.mod_t.trans left.frame.mod_p.symm)
      (left.frame.vars_t.trans left.frame.vars_p.symm) left.typed
    rw [leftType] at lookup
    have aliasesEmpty : aliases = [] := by
      simpa [AccessEnv.aliasExpr, lookup, Ty.interiorTarget?, pure, Except.pure] using canonical.symm
    have realized := shortCircuit_boundary_rows_preserved path boundary canonical rfl extended
    rw [world] at realized
    obtain ⟨right, rightWorld, rightPath, rightPlans, rightContext, step, target⟩ :=
      accepted_shortCircuit_demand_step isAnd source left world path leftDone admitted boundary rfl extended fuel
    have leftBounded : (map.addValues (lowerExpr a le before).1 aliases).Bounded
        (lowerExpr a le before).2.vals.size := by
      simpa only [aliasesEmpty, RetainedSsaMap.addValues, List.map_nil, List.nil_append] using boundary.bounded
    have rightBounded : (map.addValues (lowerExpr a le before).1 aliases).Bounded
        (demandShortCircuitRightBefore isAnd a le before).vals.size := by
      have size : (demandShortCircuitFork isAnd a le before).2.vals.size =
          (lowerExpr a le before).2.vals.size + 1 :=
        (scFork_facts (isAnd := isAnd) (x := (lowerExpr a le before).1)
          (le := le) rfl boundary.post.pp extended).2.2.2.1
      have larger : (lowerExpr a le before).2.vals.size ≤
          (demandShortCircuitRightBefore isAnd a le before).vals.size := by
        change (lowerExpr a le before).2.vals.size ≤ (demandShortCircuitFork isAnd a le before).2.vals.size
        rw [size]
        omega
      simpa only [aliasesEmpty, RetainedSsaMap.addValues, List.map_nil, List.nil_append] using
        boundary.bounded.mono larger
    have rightAdmitted : (map.addValues (lowerExpr a le before).1 aliases).Admitted
        cfg.mod.profile right.context.retained := by
      simpa only [aliasesEmpty, RetainedSsaMap.addValues, List.map_nil, List.nil_append] using target.admitted
    refine ⟨right, rightWorld, rightPath, rightPlans, rightContext, leftBounded, rightBounded, rightAdmitted, step, ?_, realized⟩
    cases path with
    | rhs => exact ⟨target.demanded.builder, target.demanded.source, by simpa only [RetainedSsaMap.Realizes, ShortCircuitPath.frame, rightWorld] using realized⟩
    | skip => exact ⟨target.demanded.builder, target.demanded.source, realized⟩

theorem shortCircuit_skip_traversal {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {isAnd : Bool} {condition rhs join result : Nat} {le : LEnv} {before forked : LS}
    {point : Pt} {frame : GIR.Frame} {state : St} {start after : DemandRuntimePoint}
    {leftLength continuationLength fuel : Nat}
    (fork : scFork isAnd condition le before = ((rhs, join, result), forked))
    (atPoint : before.pp = some point) (extended : ExtT forked cx.fn.blocks)
    (cell : frame.vals[condition]? = some (.val (.bool (ShortCircuitPath.skip.leftValue isAnd))))
    (left : DemandTraversal cx invariant leftLength
      (leftLength + (continuationLength + fuel + 1)) start ⟨point, frame, state⟩)
    (continuation : DemandTraversal cx invariant continuationLength (continuationLength + fuel)
      ⟨(join, 0), frame.set result (.val (.bool (!isAnd))), state⟩ after) :
    DemandTraversal cx invariant (leftLength + (continuationLength + 1))
      (leftLength + (continuationLength + fuel + 1)) start after := by
  apply left.append
  simpa only [Nat.add_sub_cancel_left] using
    (DemandTraversal.next left.last_valid
      (shortCircuit_control_step .skip fork atPoint extended cell (continuationLength + fuel)) continuation)

theorem shortCircuit_taken_traversal {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {isAnd : Bool} {condition rhs join result value : Nat} {le : LEnv} {before forked ended : LS}
    {point rightPoint : Pt} {frame rightFrame : GIR.Frame} {state rightState : St} {selected : Bool}
    {start after : DemandRuntimePoint} {leftLength rightLength continuationLength fuel : Nat}
    (fork : scFork isAnd condition le before = ((rhs, join, result), forked))
    (atPoint : before.pp = some point) (extended : ExtT forked cx.fn.blocks)
    (cell : frame.vals[condition]? = some (.val (.bool (ShortCircuitPath.rhs.leftValue isAnd))))
    (rightAt : ended.pp = some rightPoint)
    (rightExtended : ExtT (emitTerm (.br join [value]) le ended).2 cx.fn.blocks)
    (rightCell : rightFrame.vals[value]? = some (.val (.bool selected)))
    (left : DemandTraversal cx invariant leftLength
      (leftLength + (rightLength + (continuationLength + fuel + 1) + 1)) start ⟨point, frame, state⟩)
    (right : DemandTraversal cx invariant rightLength (rightLength + (continuationLength + fuel + 1))
      ⟨(rhs, 0), frame, state⟩ ⟨rightPoint, rightFrame, rightState⟩)
    (continuation : DemandTraversal cx invariant continuationLength (continuationLength + fuel)
      ⟨(join, 0), rightFrame.set result (.val (.bool selected)), rightState⟩ after) :
    DemandTraversal cx invariant (leftLength + (rightLength + (continuationLength + 1) + 1))
      (leftLength + (rightLength + (continuationLength + fuel + 1) + 1)) start after := by
  have joined : DemandTraversal cx invariant (continuationLength + 1) (continuationLength + fuel + 1)
      ⟨rightPoint, rightFrame, rightState⟩ after :=
    .next right.last_valid
      (shortCircuit_join_step fork atPoint extended rightAt rightExtended rightCell (continuationLength + fuel))
      continuation
  have tail := right.append (by simpa only [Nat.add_sub_cancel_left] using joined)
  have branched := DemandTraversal.next left.last_valid
    (shortCircuit_control_step .rhs fork atPoint extended cell (rightLength + (continuationLength + fuel + 1))) tail
  exact left.append (by simpa only [Nat.add_sub_cancel_left] using branched)

end Goose.Lower
