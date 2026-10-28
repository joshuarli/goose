import Goose.Lower.DemandIndexOwnerAddress
import Goose.Lower.DemandFieldScalarAddress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_index_field_owner_address {cfg : Cfg} {env : Env} {owner : Place} {field : Nat} {index : Expr}
    {origin : OriginId} {state : St} (source : PlaceSource cfg env (.elem (.of (.field owner field)) index origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem (.of (.field owner field)) index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (atPoint : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerPlace (.elem (.of (.field owner field)) index origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (middle final : DemandRuntimePoint),
      evalPlace 2 cfg env (.field owner field) state = .ok { location with path := location.path ++ [field] } state ∧
      middle.state = state ∧ final.state = state ∧
      Post cfg env cx before initial (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).2
        middle.frame middle.point [((lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨start, initial, state⟩ middle) ∧
      (∀ fuel, DemandInstructionStep cx fuel middle final) ∧
      Post cfg env cx before initial (lowerPlace (.field owner field) (lowerEnv cfg.mod env.vars results) before).2
        final.frame final.point [((lowerPlace (.field owner field) (lowerEnv cfg.mod env.vars results) before).1,
          .val (.ref { location with path := location.path ++ [field] }))] ∧
      map.Realizes cfg.mod source.world env middle ∧ map.Realizes cfg.mod source.world env final := by
  obtain ⟨_, view, viewTyping, viewRoots, viewCanonical, _⟩ := source.elemChildren origin
  obtain ⟨child, childTyping, childRoots, childCanonical⟩ := view.ofChild
  have viewOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root view.path (.view (.of (.field owner field))) before := by
    rw [viewCanonical.path]
    exact .first occurrence (.placeView rfl)
  have viewRows : GeneratedDemandRows cfg.mod view.rootsEnv.access viewOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.placeView rfl)) required :=
      .first (first := .placeView rfl) rows
    simpa only [viewRoots, viewCanonical.path] using inherited
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.place (.field owner field)) before := by
    rw [childCanonical.path]
    exact .first viewOccurrence (.viewPlace rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod view.rootsEnv.access (.first viewOccurrence (.viewPlace rfl)) required :=
      .first (first := .viewPlace rfl) viewRows
    simpa only [childRoots, childCanonical.path] using inherited
  obtain ⟨location, middle, final, placed, middleState, finalState, middlePost, first, second, finalPost⟩ :=
    accepted_generated_field_scalar_address child form childOccurrence childRows atPoint related
      (generated_view_place_extended (generated_index_view_extended extended))
  have middleRealized : map.Realizes cfg.mod source.world env middle := by
    have carried := realized.retained middlePost.same bounded.1 bounded.2 RetainsAliases.refl
    simpa only [RetainedSsaMap.Realizes, middleState] using carried
  have finalRealized : map.Realizes cfg.mod source.world env final := by
    have carried := realized.retained finalPost.same bounded.1 bounded.2 RetainsAliases.refl
    simpa only [RetainedSsaMap.Realizes, finalState] using carried
  exact ⟨location, middle, final, placed, middleState, finalState, middlePost, first, second, finalPost, middleRealized, finalRealized⟩

theorem PlaceSource.index_field_view_alias {cfg : Cfg} {env : Env} {owner : Place} {field : Nat} {index : Expr}
    {origin : OriginId} {state : St}
    (source : PlaceSource cfg env (.elem (.of (.field owner field)) index origin) state) (form : ScalarReadPlace owner) :
    ∃ aliases, source.rootsEnv.access.aliasView (source.path ++ [0]) (.of (.field owner field)) = .ok aliases := by
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

theorem accepted_generated_index_field_entry {cfg : Cfg} {env : Env} {owner : Place} {field : Nat} {index : Expr}
    {origin : OriginId} {state after : St} (source : PlaceSource cfg env (.elem (.of (.field owner field)) index origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem (.of (.field owner field)) index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {start point : Pt} {initial frame : GIR.Frame}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {fuel : Nat} {sample : ViewVal} (evaluated : evalView fuel cfg env (.of (.field owner field)) state = .ok sample after)
    (post : Post cfg env cx before initial (lowerView (.of (.field owner field)) (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerView (.of (.field owner field)) (lowerEnv cfg.mod env.vars results) before).1, .view sample)]) :
    ∃ aliases, GeneratedIndexEntry source occurrence required map aliases ⟨point, frame, after⟩ := by
  obtain ⟨aliases, query⟩ := source.index_field_view_alias form
  exact ⟨aliases, accepted_generated_index_entry source occurrence rows coverage admitted bounded realized query evaluated post⟩

#print axioms PlaceSource.index_field_view_alias
#print axioms accepted_generated_index_field_entry
#print axioms accepted_generated_index_field_owner_address
end Goose.Lower

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_index_field_assignment_snapshot_stop {cfg : Cfg} {env : Env} {owner : Place} {field : Nat} {index value : Expr}
    {origin indexOrigin : OriginId} {state after : St}
    (source : StmtSource cfg env (.assign (.elem (.of (.field owner field)) index indexOrigin) value origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.statement loop (.assign (.elem (.of (.field owner field)) index indexOrigin) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (atPoint : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerStmt loop (.assign (.elem (.of (.field owner field)) index indexOrigin) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx 2 ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} (nonTimeout : stop ≠ .timeout)
    (stopped : DemandInstructionStop cx targetFuel reached stop after) :
    execStmt 5 cfg env (.assign (.elem (.of (.field owner field)) index indexOrigin) value origin) state = .stop stop after := by
  obtain ⟨destination, _, roots, world, _, canonical, _⟩ := source.assignChildrenDemand
  have placeOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root destination.path (.place (.elem (.of (.field owner field)) index indexOrigin)) before := by
    rw [canonical.path]
    exact .assignmentPlace occurrence
  have placeRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access placeOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.assignmentPlace occurrence) required := .assignmentPlace rows
    simpa only [roots, canonical.path] using inherited
  have placeRealized : map.Realizes cfg.mod destination.world env ⟨start, initial, state⟩ := by
    simpa only [world] using realized
  have placeExtended := generated_assignment_place_extended extended
  obtain ⟨location, middle, final, placed, middleState, finalState, middlePost, firstStep, secondStep, post, _, _⟩ :=
    accepted_generated_index_field_owner_address destination form placeOccurrence placeRows bounded placeRealized atPoint related placeExtended
  rcases steps.uncons with impossible | ⟨remaining, current, count, first, tail⟩
  · omega
  · obtain ⟨fuel, actual⟩ := runtimeStep_demandInstructionStep first
    have same := actual.deterministic (firstStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with impossible | ⟨remaining, current, nextCount, second, rest⟩
    · omega
    · obtain ⟨fuel, actual⟩ := runtimeStep_demandInstructionStep second
      have same := actual.deterministic (secondStep fuel)
      have currentEq : current = final := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
      subst current
      have remainingZero : remaining = 0 := by omega
      subst remaining
      rcases rest.uncons with ⟨_, samePoint⟩ | ⟨n, point, impossible, _, _⟩
      · subst reached
        have stopped' : DemandInstructionStop cx targetFuel ⟨final.point, final.frame, state⟩ stop after := by
          cases final
          simp_all
        obtain ⟨_, view, viewTyping, viewRoots, viewCanonical, _⟩ := destination.elemChildren indexOrigin
        have viewOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
            root view.path (.view (.of (.field owner field))) before := by
          rw [viewCanonical.path]
          exact .first placeOccurrence (.placeView rfl)
        have viewRows : GeneratedDemandRows cfg.mod view.rootsEnv.access viewOccurrence required := by
          have inherited : GeneratedDemandRows cfg.mod destination.rootsEnv.access (.first placeOccurrence (.placeView rfl)) required :=
            .first (first := .placeView rfl) placeRows
          simpa only [viewRoots, viewCanonical.path] using inherited
        have viewStop := accepted_generated_snapshot_runtime_stop view viewOccurrence viewRows placed post
          (generated_index_view_extended placeExtended) nonTimeout stopped'
        simp only [execStmt, evalPlace, bind_apply, viewStop]
      · omega

#print axioms accepted_generated_index_field_assignment_snapshot_stop
end Goose.Lower
