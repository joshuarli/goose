import Goose.Lower.DemandIndexOwnerAddress
import Goose.Lower.DemandScalarAssignmentPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_generated_index_assignment_value_entry {cfg : Cfg} {env : Env} {owner : Place} {index value : Expr}
    {origin indexOrigin : OriginId} {state viewedState indexedState after : St}
    (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state)
    (form : IndexOwnerPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.statement loop (.assign (.elem (.of owner) index indexOrigin) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0, 0]) (.of owner) = .ok aliases)
    {fuel : Nat} {sample : ViewVal} {indexValue : Val}
    (viewed : evalView fuel cfg env (.of owner) state = .ok sample viewedState)
    (indexed : evalExpr fuel cfg env index viewedState = .ok indexValue indexedState)
    {initial viewFrame frame : GIR.Frame} {start viewPoint point : Pt}
    (viewPost : Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame viewPoint
      [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (indexPost : Post cfg env cx (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).1, .val indexValue)])
    (bounded : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Bounded
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2.vals.size)
    (realized : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod source.world env ⟨point, frame, indexedState⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.elem (.of owner) index indexOrigin) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (target : ∀ {middle : St} (child : ExprSource cfg env value middle),
      source.AssignmentValueAt child → child.ty.refTarget = true)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Goose.Evidence.RuntimeStep cx.cfg cx.fn point frame indexedState next nextFrame after) :
    ∃ (location : Loc) (child : ExprSource cfg env value after) (valueAliases : List RetainedAlias),
      evalPlace (fuel + 1) cfg env (.elem (.of owner) index indexOrigin) state = .ok location after ∧
      source.AssignmentValueAt child ∧ child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.elem (.of owner) index indexOrigin) = .ok valueAliases ∧
      (map.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases).Covers
        (required.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases) ∧
      (map.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases).Bounded
        (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (map.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases).Admitted
        cfg.mod.profile child.context.retained ∧
      (map.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases).Realizes
        cfg.mod child.world env ⟨next, nextFrame, after⟩ ∧
      Post cfg env cx before initial (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [((lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
        (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2 nextFrame next := by
  obtain ⟨destination, _, roots, world, _, canonical, children⟩ := source.assignChildrenDemand
  have placeOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root destination.path (.place (.elem (.of owner) index indexOrigin)) before := by
    rw [canonical.path]
    exact .assignmentPlace occurrence
  have placeRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access placeOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.assignmentPlace occurrence) required := .assignmentPlace rows
    simpa only [roots, canonical.path] using inherited
  have viewQuery : destination.rootsEnv.access.aliasView (destination.path ++ [0]) (.of owner) = .ok aliases := by
    simpa only [roots, canonical.path, List.append_assoc, List.singleton_append] using query
  have indexRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access (.index placeOccurrence)
      (required.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases) := .index placeRows viewQuery
  have indexRealized : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod destination.world env ⟨point, frame, indexedState⟩ := by
    simpa only [world] using realized
  obtain ⟨_, _, _, _, location, _, _, placed, post, _, demanded⟩ := accepted_generated_index_runtime_step destination
    placeOccurrence indexRows (coverage.addRuns _ aliases) viewed indexed viewPost indexPost bounded indexRealized
    (generated_assignment_place_extended extended) step
  obtain ⟨child, childTyping, childRoots, _, _, typeEq, childAt⟩ := children (fuel + 1) location after placed
  have targetType : destination.ty.refTarget = true := by
    rw [← typeEq]
    exact target child childAt
  have baseCoverage : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Covers map := by
    constructor
    · intro cell member; exact member
    · intro cell member; exact List.mem_append_right _ member
  have finalRealized : map.Realizes cfg.mod source.world env ⟨next, nextFrame, after⟩ := by
    simpa only [world] using baseCoverage.realizes demanded.operands
  have finalBounded : map.Bounded (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2.vals.size :=
    (baseCoverage.bounded bounded).mono (adv_emitDef (show emitDef (.indexChecked
      (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).1
      (some indexOrigin)) (lowerEnv cfg.mod env.vars results)
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2 =
      lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before from rfl)).vals
  obtain ⟨valueAliases, valueQuery, valueCoverage, valueBounded, valueAdmitted, valueRealized, valueInput⟩ :=
    accepted_assignment_index_value_demand source (form.indexed index indexOrigin) destination roots world rfl targetType placed
      child childAt childTyping childRoots coverage admitted finalBounded input post finalRealized
  exact ⟨location, child, valueAliases, placed, childAt, childTyping, childRoots, valueQuery, valueCoverage, valueBounded, valueAdmitted, valueRealized, post, valueInput⟩

theorem accepted_generated_index_assignment_value_prefix {cfg : Cfg} {env : Env} {owner : Place} {index value : Expr}
    {origin indexOrigin : OriginId} {state viewedState indexedState after : St}
    (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state)
    (form : IndexOwnerPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.statement loop (.assign (.elem (.of owner) index indexOrigin) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0, 0]) (.of owner) = .ok aliases)
    {fuel : Nat} {sample : ViewVal} {indexValue : Val}
    (viewed : evalView fuel cfg env (.of owner) state = .ok sample viewedState)
    (indexed : evalExpr fuel cfg env index viewedState = .ok indexValue indexedState)
    {initial viewFrame frame : GIR.Frame} {start viewPoint point : Pt}
    (viewPost : Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame viewPoint
      [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (indexPost : Post cfg env cx (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).1, .val indexValue)])
    (bounded : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Bounded
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2.vals.size)
    (realized : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod source.world env ⟨point, frame, indexedState⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.elem (.of owner) index indexOrigin) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (target : ∀ {middle : St} (child : ExprSource cfg env value middle),
      source.AssignmentValueAt child → child.ty.refTarget = true)
    {rootOwner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (owned : GeneratedSourceOwner selected source.context)
    (family : GeneratedExpressionPrefixFamily cx results selected loop value (@CanonicalExpressionPrefixCursor cfg env cx))
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Goose.Evidence.RuntimeStep cx.cfg cx.fn point frame indexedState next nextFrame after)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨next, nextFrame, after⟩ reached) :
    ∃ (location : Loc) (child : ExprSource cfg env value after) (valueAliases : List RetainedAlias),
      evalPlace (fuel + 1) cfg env (.elem (.of owner) index indexOrigin) state = .ok location after ∧
      source.AssignmentValueAt child ∧
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.elem (.of owner) index indexOrigin) = .ok valueAliases ∧
      Post cfg env cx before initial (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [((lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      DemandPrefixDecomposition cx (fun fuel => evalExpr fuel cfg env value)
        (CanonicalExpressionDemand (map.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases) cx child)
        (GeneratedExpressionPrefixEnd child
          (map.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases)
          cx (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2 nextFrame
          (lowerExpr value (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2).2
          (lowerExpr value (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2).1)
        taken ⟨next, nextFrame, after⟩ reached := by
  obtain ⟨location, child, valueAliases, placed, canonical, typing, roots, valueQuery, valueCoverage,
    valueBounded, valueAdmitted, valueRealized, post, valueInput⟩ :=
    accepted_generated_index_assignment_value_entry source form occurrence rows coverage admitted query viewed indexed viewPost indexPost
      bounded realized input extended target step
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 1 (.expression value) .expression rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression value)
        (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [canonical.path]
    exact .assignmentValue occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence
      (required.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases) := by
    have inherited := GeneratedDemandRows.assignmentValue rows valueQuery
    simpa only [roots, canonical.path] using inherited
  have progress := family child childOwner childOccurrence childRows valueCoverage valueAdmitted valueBounded valueRealized valueInput
    (generated_assignment_value_extended extended) steps
  exact ⟨location, child, valueAliases, placed, canonical, valueQuery, post, progress.progress⟩

theorem accepted_generated_index_assignment_value_stopped {cfg : Cfg} {env : Env} {owner : Place} {index value : Expr}
    {origin indexOrigin : OriginId} {state viewedState indexedState after : St}
    (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state)
    (form : IndexOwnerPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.statement loop (.assign (.elem (.of owner) index indexOrigin) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0, 0]) (.of owner) = .ok aliases)
    {fuel : Nat} {sample : ViewVal} {indexValue : Val}
    (viewed : evalView fuel cfg env (.of owner) state = .ok sample viewedState)
    (indexed : evalExpr fuel cfg env index viewedState = .ok indexValue indexedState)
    {initial viewFrame frame : GIR.Frame} {start viewPoint point : Pt}
    (viewPost : Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame viewPoint
      [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (indexPost : Post cfg env cx (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).1, .val indexValue)])
    (bounded : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Bounded
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2.vals.size)
    (realized : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod source.world env ⟨point, frame, indexedState⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.elem (.of owner) index indexOrigin) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (target : ∀ {middle : St} (child : ExprSource cfg env value middle),
      source.AssignmentValueAt child → child.ty.refTarget = true)
    {rootOwner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (owned : GeneratedSourceOwner selected source.context)
    (family : GeneratedStoppedExpressionPrefixFamily cx results selected loop value)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Goose.Evidence.RuntimeStep cx.cfg cx.fn point frame indexedState next nextFrame after)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨next, nextFrame, after⟩ reached)
    {targetFuel : Nat} {stop : Stop} {final : St} (stopped : DemandInstructionStop cx targetFuel reached stop final)
    (nonTimeout : stop ≠ .timeout) :
    ∃ (location : Loc) (child : ExprSource cfg env value after) (valueAliases : List RetainedAlias),
      evalPlace (fuel + 1) cfg env (.elem (.of owner) index indexOrigin) state = .ok location after ∧
      source.AssignmentValueAt child ∧
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.elem (.of owner) index indexOrigin) = .ok valueAliases ∧
      Post cfg env cx before initial (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next [((lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      StoppedExpressionPrefix child
        (map.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases)
        cx results (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2
        nextFrame next taken reached stop final := by
  obtain ⟨location, child, valueAliases, placed, canonical, typing, roots, valueQuery, valueCoverage,
    valueBounded, valueAdmitted, valueRealized, post, valueInput⟩ :=
    accepted_generated_index_assignment_value_entry source form occurrence rows coverage admitted query viewed indexed viewPost indexPost
      bounded realized input extended target step
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 1 (.expression value) .expression rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression value)
        (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [canonical.path]
    exact .assignmentValue occurrence
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence
      (required.addValues (lowerPlace (.elem (.of owner) index indexOrigin) (lowerEnv cfg.mod env.vars results) before).1 valueAliases) := by
    have inherited := GeneratedDemandRows.assignmentValue rows valueQuery
    simpa only [roots, canonical.path] using inherited
  have progress := family child childOwner childOccurrence childRows valueCoverage valueAdmitted valueBounded valueRealized valueInput
    (generated_assignment_value_extended extended) steps stopped nonTimeout
  exact ⟨location, child, valueAliases, placed, canonical, valueQuery, post, progress⟩


theorem accepted_generated_index_assignment_store_prefix {cfg : Cfg} {env : Env} {owner : Place} {index value : Expr}
    {origin indexOrigin : OriginId} {state viewedState indexedState after : St}
    (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state)
    (form : IndexOwnerPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.statement loop (.assign (.elem (.of owner) index indexOrigin) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0, 0]) (.of owner) = .ok aliases)
    {fuel : Nat} {sample : ViewVal} {indexValue : Val}
    (viewed : evalView fuel cfg env (.of owner) state = .ok sample viewedState)
    (indexed : evalExpr fuel cfg env index viewedState = .ok indexValue indexedState)
    {initial viewFrame frame : GIR.Frame} {start viewPoint point : Pt}
    (viewPost : Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame viewPoint
      [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (indexPost : Post cfg env cx (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).1, .val indexValue)])
    (bounded : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Bounded
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2.vals.size)
    (realized : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod source.world env ⟨point, frame, indexedState⟩)
    (startBounded : map.Bounded before.vals.size)
    (startRealized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.elem (.of owner) index indexOrigin) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (target : ∀ {middle : St} (child : ExprSource cfg env value middle),
      source.AssignmentValueAt child → child.ty.refTarget = true)
    {rootOwner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (owned : GeneratedSourceOwner selected source.context)
    (family : GeneratedExpressionPrefixFamily cx results selected loop value (@CanonicalExpressionPrefixCursor cfg env cx))
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Goose.Evidence.RuntimeStep cx.cfg cx.fn point frame indexedState next nextFrame after)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨next, nextFrame, after⟩ reached) :
    DemandPrefixDecomposition cx (fun fuel _ => (execStmt fuel cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) >>= prepareLoopFlow env loop) state)
      (ScalarAssignmentPrefixCursor cx results source before
        (lowerStmt loop (.assign (.elem (.of owner) index indexOrigin) value origin) (lowerEnv cfg.mod env.vars results) before).2
        initial start map required)
      (GeneratedStatementPrefixEnd source map cx before initial
        (lowerStmt loop (.assign (.elem (.of owner) index indexOrigin) value origin) (lowerEnv cfg.mod env.vars results) before).2 loop)
      (taken + 1) ⟨point, frame, indexedState⟩ reached := by
  obtain ⟨location, child, valueAliases, placed, canonical, valueQuery, placePost, progress⟩ :=
    accepted_generated_index_assignment_value_prefix source form occurrence rows coverage admitted query viewed indexed viewPost indexPost
      bounded realized input extended target selected owned family step steps
  cases progress with
  | interior demanded => exact .interior (.value child canonical valueAliases demanded)
  | @complete rightFuel rightCount left boundary result count rightTrace residual rightDone rightBoundary =>
    let place := Place.elem (.of owner) index indexOrigin
    let le := lowerEnv cfg.mod env.vars results
    let addressed := lowerPlace place le before
    have post := placePost.comp rightBoundary.post
    have combinedPost : Post cfg env cx before initial (lowerExpr value le addressed.2).2 boundary.frame boundary.point
        [(addressed.1, .val (.ref location)), ((lowerExpr value le addressed.2).1, .val result)] := by
      simpa only [List.singleton_append] using post
    have site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn le root source.path before loop place
        value origin required boundary.point := ⟨occurrence, rows, ⟨valueAliases, valueQuery⟩, combinedPost.pp, extended⟩
    rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, final, rfl, store, afterStore⟩
    · exact .interior (.store child canonical valueAliases site rightBoundary.demanded)
    · let common := max (fuel + 1) rightFuel
      have placed' : evalPlace common cfg env place state = .ok location after :=
        ((Goose.Proofs.Fuel.monoAll (fuel + 1) common (by dsimp [common]; exact Nat.le_max_left _ _)).place cfg env place state).1 _ _ placed
      have rightDone' : evalExpr common cfg env value after = .ok result boundary.state :=
        ((Goose.Proofs.Fuel.monoAll rightFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env value after).1 _ _ rightDone
      obtain ⟨_, _, done, finalPost, finalResult, finalBounded, finalDemand⟩ :=
        accepted_generated_assignment_store_step source site admitted startBounded startRealized placed' rightDone' combinedPost store
      change execStmt (common + 1) cfg env (.assign place value origin) state = .ok (.normal .unit) final.state at done
      have prepared : (execStmt (common + 1) cfg env (.assign place value origin) >>= prepareLoopFlow env loop) state =
          .ok (.normal .unit) final.state := by
        simp only [bind_apply, done]
        cases loop <;> rfl
      exact .complete (consumed := rightCount + 2) (by omega)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (DemandRuntimePrefix.next step (rightTrace.append (.next store (.zero _))))) afterStore prepared
        (.normal finalPost finalResult finalBounded finalDemand.operands)

inductive IndexedAssignmentStoppedSuffix {cfg : Cfg} {env : Env} {statement : Stmt} {state : St}
    (source : StmtSource cfg env statement state) (map : RetainedSsaMap) (cx : FnCtx) (results : List Ty) (loop : Option LoopCtx)
    (before : LS) (initial : GIR.Frame) (start : DemandRuntimePoint) (taken : Nat)
    (reached : DemandRuntimePoint) (stop : Stop) (after : St) : Prop
  | aborted (fuel : Nat) (evaluated : (execStmt fuel cfg env statement >>= prepareLoopFlow env loop) state = .stop stop after) :
      IndexedAssignmentStoppedSuffix source map cx results loop before initial start taken reached stop after
  | complete {fuel consumed remaining : Nat} {boundary : DemandRuntimePoint} {flow : Flow}
      (count : consumed + remaining = taken) (executed : DemandRuntimePrefix cx consumed start boundary)
      (residual : DemandRuntimePrefix cx remaining boundary reached)
      (evaluated : (execStmt fuel cfg env statement >>= prepareLoopFlow env loop) state = .ok flow boundary.state)
      (post : GeneratedStatementPrefixEnd source map cx before initial
        (lowerStmt loop statement (lowerEnv cfg.mod env.vars results) before).2 loop flow boundary) :
      IndexedAssignmentStoppedSuffix source map cx results loop before initial start taken reached stop after

theorem accepted_generated_index_assignment_store_stopped {cfg : Cfg} {env : Env} {owner : Place} {index value : Expr}
    {origin indexOrigin : OriginId} {state viewedState indexedState after : St}
    (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state)
    (form : IndexOwnerPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.statement loop (.assign (.elem (.of owner) index indexOrigin) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0, 0]) (.of owner) = .ok aliases)
    {fuel : Nat} {sample : ViewVal} {indexValue : Val}
    (viewed : evalView fuel cfg env (.of owner) state = .ok sample viewedState)
    (indexed : evalExpr fuel cfg env index viewedState = .ok indexValue indexedState)
    {initial viewFrame frame : GIR.Frame} {start viewPoint point : Pt}
    (viewPost : Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame viewPoint
      [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (indexPost : Post cfg env cx (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 viewFrame
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).1, .val indexValue)])
    (bounded : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Bounded
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2).2.vals.size)
    (realized : (map.addRuns (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod source.world env ⟨point, frame, indexedState⟩)
    (startBounded : map.Bounded before.vals.size)
    (startRealized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.elem (.of owner) index indexOrigin) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (target : ∀ {middle : St} (child : ExprSource cfg env value middle),
      source.AssignmentValueAt child → child.ty.refTarget = true)
    {rootOwner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (owned : GeneratedSourceOwner selected source.context)
    (family : GeneratedStoppedExpressionPrefixFamily cx results selected loop value)
    {next : Pt} {nextFrame : GIR.Frame}
    (step : Goose.Evidence.RuntimeStep cx.cfg cx.fn point frame indexedState next nextFrame after)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨next, nextFrame, after⟩ reached)
    {targetFuel : Nat} {stop : Stop} {final : St} (stopped : DemandInstructionStop cx targetFuel reached stop final)
    (nonTimeout : stop ≠ .timeout) :
    IndexedAssignmentStoppedSuffix source map cx results loop before initial ⟨point, frame, indexedState⟩ (taken + 1) reached stop final := by
  obtain ⟨location, child, valueAliases, placed, canonical, valueQuery, placePost, progress⟩ :=
    accepted_generated_index_assignment_value_stopped source form occurrence rows coverage admitted query viewed indexed viewPost indexPost
      bounded realized input extended target selected owned family step steps stopped nonTimeout
  cases progress with
  | aborted valueFuel valueStop =>
    let common := max (fuel + 1) valueFuel
    have placed' : evalPlace common cfg env (.elem (.of owner) index indexOrigin) state = .ok location after :=
      ((monoAll (fuel + 1) common (by dsimp [common]; exact Nat.le_max_left _ _)).place cfg env _ state).1 _ _ placed
    have valueStop' : evalExpr common cfg env value after = .stop stop final := by
      rcases ((monoAll valueFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env value after).2 _ _ valueStop with timeout | done
      · cases stop <;> simp_all [Goose.Proofs.Fuel.isTimeout]
      · exact done
    refine .aborted (common + 1) ?_
    simp only [bind_apply, execStmt, placed', valueStop']
  | @complete valueFuel valueCount left boundary result count valueTrace residual valueDone valueBoundary =>
    let place := Place.elem (.of owner) index indexOrigin
    let le := lowerEnv cfg.mod env.vars results
    let addressed := lowerPlace place le before
    have post := placePost.comp valueBoundary.post
    have combinedPost : Post cfg env cx before initial (lowerExpr value le addressed.2).2 boundary.frame boundary.point
        [(addressed.1, .val (.ref location)), ((lowerExpr value le addressed.2).1, .val result)] := by
      simpa only [List.singleton_append] using post
    have site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn le root source.path before loop place
        value origin required boundary.point := ⟨occurrence, rows, ⟨valueAliases, valueQuery⟩, combinedPost.pp, extended⟩
    let common := max (fuel + 1) valueFuel
    have placed' : evalPlace common cfg env place state = .ok location after :=
      ((monoAll (fuel + 1) common (by dsimp [common]; exact Nat.le_max_left _ _)).place cfg env place state).1 _ _ placed
    have valueDone' : evalExpr common cfg env value after = .ok result boundary.state :=
      ((monoAll valueFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env value after).1 _ _ valueDone
    rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, nextFinal, rfl, store, afterStore⟩
    · have done := accepted_generated_assignment_store_stop source site placed' valueDone' combinedPost stopped nonTimeout
      refine .aborted (common + 1) ?_
      simp only [bind_apply, done]
    · obtain ⟨_, _, done, finalPost, finalResult, finalBounded, finalDemand⟩ :=
        accepted_generated_assignment_store_step source site admitted startBounded startRealized placed' valueDone' combinedPost store
      change execStmt (common + 1) cfg env (.assign place value origin) state = .ok (.normal .unit) nextFinal.state at done
      have prepared : (execStmt (common + 1) cfg env (.assign place value origin) >>= prepareLoopFlow env loop) state =
          .ok (.normal .unit) nextFinal.state := by
        simp only [bind_apply, done]
        cases loop <;> rfl
      exact .complete (consumed := valueCount + 2) (by omega)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (DemandRuntimePrefix.next step (valueTrace.append (.next store (.zero _))))) afterStore prepared
        (.normal finalPost finalResult finalBounded finalDemand.operands)

#print axioms accepted_generated_index_assignment_store_stopped

#print axioms accepted_generated_index_assignment_store_prefix

#print axioms accepted_generated_index_assignment_value_stopped
#print axioms accepted_generated_index_assignment_value_prefix

#print axioms accepted_generated_index_assignment_value_entry
end Goose.Lower
