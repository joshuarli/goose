import Goose.Lower.DemandAssignmentIndexAlias
import Goose.Lower.DemandGeneratedIndexEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem PlaceSource.index_scalar_view_alias {cfg : Cfg} {env : Env} {owner : Place} {index : Expr}
    {origin : OriginId} {state : St} (source : PlaceSource cfg env (.elem (.of owner) index origin) state)
    (form : ScalarReadPlace owner) :
    ∃ aliases, source.rootsEnv.access.aliasView (source.path ++ [0]) (.of owner) = .ok aliases := by
  obtain ⟨_, view, typing, roots, canonical, _⟩ := source.elemChildren origin
  have element := tyView_accessElement (view.frame.mod_t.trans view.frame.mod_p.symm)
    (view.frame.vars_t.trans view.frame.vars_p.symm) view.typed
  rw [roots] at element
  cases form with
  | global global =>
    refine ⟨[⟨.slice .readOnly view.element, [.global global], .operand (source.path ++ [0])⟩], ?_⟩
    simp only [AccessEnv.aliasView, element, AccessEnv.viewRoots, AccessEnv.placeRoots, bind, pure]
    rfl
  | slot slot =>
    refine ⟨[⟨.slice .readOnly view.element, [.local slot], .operand (source.path ++ [0])⟩], ?_⟩
    simp only [AccessEnv.aliasView, element, AccessEnv.viewRoots, AccessEnv.placeRoots, bind, pure]
    rfl

#print axioms PlaceSource.index_scalar_view_alias

theorem accepted_generated_index_scalar_entry {cfg : Cfg} {env : Env} {owner : Place} {index : Expr}
    {origin : OriginId} {state after : St} (source : PlaceSource cfg env (.elem (.of owner) index origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem (.of owner) index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {start point : Pt} {initial frame : GIR.Frame}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {fuel : Nat} {sample : ViewVal} (evaluated : evalView fuel cfg env (.of owner) state = .ok sample after)
    (post : Post cfg env cx before initial (lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerView (.of owner) (lowerEnv cfg.mod env.vars results) before).1, .view sample)]) :
    ∃ aliases, GeneratedIndexEntry source occurrence required map aliases ⟨point, frame, after⟩ := by
  obtain ⟨aliases, query⟩ := source.index_scalar_view_alias form
  exact ⟨aliases, accepted_generated_index_entry source occurrence rows coverage admitted bounded realized query evaluated post⟩

#print axioms accepted_generated_index_scalar_entry

theorem accepted_generated_index_assignment_bounds_stop {cfg : Cfg} {env : Env} {view : View} {index value : Expr}
    {origin indexOrigin : OriginId} {state viewedState indexedState after : St}
    (source : StmtSource cfg env (.assign (.elem view index indexOrigin) value origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.statement loop (.assign (.elem view index indexOrigin) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0, 0]) view = .ok aliases)
    (coverage : (map.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases).Covers
      (required.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases))
    {fuel : Nat} {sample : ViewVal} {indexValue : Val}
    (viewed : evalView fuel cfg env view state = .ok sample viewedState)
    (indexed : evalExpr fuel cfg env index viewedState = .ok indexValue indexedState)
    {initial viewFrame frame : GIR.Frame} {viewPoint point : Pt}
    (viewPost : Post cfg env cx before initial (lowerView view (lowerEnv cfg.mod env.vars results) before).2 viewFrame viewPoint
      [((lowerView view (lowerEnv cfg.mod env.vars results) before).1, .view sample)])
    (indexPost : Post cfg env cx (lowerView view (lowerEnv cfg.mod env.vars results) before).2 viewFrame
      (lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView view (lowerEnv cfg.mod env.vars results) before).2).2 frame point
      [((lowerExpr index (lowerEnv cfg.mod env.vars results) (lowerView view (lowerEnv cfg.mod env.vars results) before).2).1, .val indexValue)])
    (realized : (map.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod source.world env ⟨point, frame, indexedState⟩)
    (extended : ExtT (lowerStmt loop (.assign (.elem view index indexOrigin) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop} (nonTimeout : stop ≠ .timeout)
    (stopped : DemandInstructionStop cx targetFuel ⟨point, frame, indexedState⟩ stop after) :
    stop = .abort .indexOob indexOrigin ∧ after = indexedState ∧
      execStmt (fuel + 2) cfg env (.assign (.elem view index indexOrigin) value origin) state = .stop stop after := by
  obtain ⟨destination, _, roots, world, _, canonical, _⟩ := source.assignChildrenDemand
  have placeOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root destination.path (.place (.elem view index indexOrigin)) before := by
    rw [canonical.path]
    exact .assignmentPlace occurrence
  have placeRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access placeOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.assignmentPlace occurrence) required := .assignmentPlace rows
    simpa only [roots, canonical.path] using inherited
  have viewQuery : destination.rootsEnv.access.aliasView (destination.path ++ [0]) view = .ok aliases := by
    simpa only [roots, canonical.path, List.append_assoc, List.singleton_append] using query
  have indexRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access (.index placeOccurrence)
      (required.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases) := .index placeRows viewQuery
  have childRealized : (map.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod destination.world env ⟨point, frame, indexedState⟩ := by
    simpa only [world] using realized
  obtain ⟨_, _, _, _, stopEq, stateEq, placeStopped⟩ := accepted_generated_index_runtime_stop destination
    placeOccurrence indexRows coverage viewed indexed viewPost indexPost childRealized
    (generated_assignment_place_extended extended) nonTimeout stopped
  refine ⟨stopEq, stateEq, ?_⟩
  simp only [execStmt, bind_apply, placeStopped]

#print axioms accepted_generated_index_assignment_bounds_stop
end Goose.Lower
