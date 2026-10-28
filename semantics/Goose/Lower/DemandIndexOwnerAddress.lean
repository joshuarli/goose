import Goose.Lower.DemandIndexSnapshotEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_index_owner_address {cfg : Cfg} {env : Env} {owner : Place} {index : Expr}
    {origin : OriginId} {state : St} (source : PlaceSource cfg env (.elem (.of owner) index origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem (.of owner) index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (atPoint : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerPlace (.elem (.of owner) index origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ location : Loc,
      evalPlace 1 cfg env owner state = .ok location state ∧
      Post cfg env cx before initial (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).2
        (initial.set (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1 (.val (.ref location)))
        (start.1, start.2 + 1) [((lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨start, initial, state⟩
        ⟨(start.1, start.2 + 1), initial.set (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1
          (.val (.ref location)), state⟩) ∧
      map.Realizes cfg.mod source.world env ⟨(start.1, start.2 + 1),
        initial.set (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1 (.val (.ref location)), state⟩ := by
  obtain ⟨_, view, viewTyping, viewRoots, viewCanonical, _⟩ := source.elemChildren origin
  obtain ⟨child, childTyping, childRoots, childCanonical⟩ := view.ofChild
  have viewOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root view.path (.view (.of owner)) before := by
    rw [viewCanonical.path]
    exact .first occurrence (.placeView rfl)
  have viewRows : GeneratedDemandRows cfg.mod view.rootsEnv.access viewOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.placeView rfl)) required :=
      .first (first := .placeView rfl) rows
    simpa only [viewRoots, viewCanonical.path] using inherited
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.place owner) before := by
    rw [childCanonical.path]
    exact .first viewOccurrence (.viewPlace rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod view.rootsEnv.access (.first viewOccurrence (.viewPlace rfl)) required :=
      .first (first := .viewPlace rfl) viewRows
    simpa only [childRoots, childCanonical.path] using inherited
  obtain ⟨location, placed, post, step⟩ := accepted_generated_scalar_place_address child form childOccurrence childRows atPoint related
    (generated_view_place_extended (generated_index_view_extended extended))
  exact ⟨location, placed, post, step, realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl⟩

#print axioms accepted_generated_index_owner_address
end Goose.Lower

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_index_assignment_snapshot_stop {cfg : Cfg} {env : Env} {owner : Place} {index value : Expr}
    {origin indexOrigin : OriginId} {state after : St}
    (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state)
    (form : ScalarReadPlace owner) {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.statement loop (.assign (.elem (.of owner) index indexOrigin) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (atPoint : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerStmt loop (.assign (.elem (.of owner) index indexOrigin) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx 1 ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} (nonTimeout : stop ≠ .timeout)
    (stopped : DemandInstructionStop cx targetFuel reached stop after) :
    execStmt 4 cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state = .stop stop after := by
  obtain ⟨destination, _, roots, world, _, canonical, _⟩ := source.assignChildrenDemand
  have placeOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root destination.path (.place (.elem (.of owner) index indexOrigin)) before := by
    rw [canonical.path]
    exact .assignmentPlace occurrence
  have placeRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access placeOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.assignmentPlace occurrence) required := .assignmentPlace rows
    simpa only [roots, canonical.path] using inherited
  have placeRealized : map.Realizes cfg.mod destination.world env ⟨start, initial, state⟩ := by
    simpa only [world] using realized
  have placeExtended := generated_assignment_place_extended extended
  obtain ⟨location, placed, post, addressStep, carried⟩ := accepted_generated_index_owner_address destination form
    placeOccurrence placeRows bounded placeRealized atPoint related placeExtended
  rcases steps.uncons with impossible | ⟨remaining, current, count, first, tail⟩
  · omega
  · have remainingZero : remaining = 0 := by omega
    subst remaining
    rcases tail.uncons with ⟨_, samePoint⟩ | ⟨n, p, impossible, _, _⟩
    · subst current
      obtain ⟨fuel, actual⟩ := runtimeStep_demandInstructionStep first
      have same := actual.deterministic (addressStep fuel)
      have reachedEq : reached = ⟨(start.1, start.2 + 1),
          initial.set (lowerPlace owner (lowerEnv cfg.mod env.vars results) before).1 (.val (.ref location)), state⟩ := by
        cases reached
        exact same
      subst reached
      obtain ⟨_, view, viewTyping, viewRoots, viewCanonical, _⟩ := destination.elemChildren indexOrigin
      have viewOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root view.path (.view (.of owner)) before := by
        rw [viewCanonical.path]
        exact .first placeOccurrence (.placeView rfl)
      have viewRows : GeneratedDemandRows cfg.mod view.rootsEnv.access viewOccurrence required := by
        have inherited : GeneratedDemandRows cfg.mod destination.rootsEnv.access (.first placeOccurrence (.placeView rfl)) required :=
          .first (first := .placeView rfl) placeRows
        simpa only [viewRoots, viewCanonical.path] using inherited
      have viewStop := accepted_generated_snapshot_runtime_stop view viewOccurrence viewRows placed post
        (generated_index_view_extended placeExtended) nonTimeout stopped
      simp only [execStmt, evalPlace, bind_apply, viewStop]
    · omega

#print axioms accepted_generated_index_assignment_snapshot_stop
end Goose.Lower
