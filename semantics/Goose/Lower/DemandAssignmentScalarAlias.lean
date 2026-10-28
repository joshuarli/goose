import Goose.Lower.DemandAssignmentSource
import Goose.Lower.DemandGeneratedScalarPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_assignment_scalar_place_roots {cfg : Cfg} {env : Env} {state : St} {place : Place}
    (destination : PlaceSource cfg env place state) (form : ScalarReadPlace place) :
    destination.rootsEnv.access.placeRoots place = .ok destination.roots := by
  cases form with
  | global global =>
    have rooted := destination.rooted
    change Except.ok ([RootRef.global global], destination.rootsStart) =
      Except.ok (destination.roots, destination.rootsEnd) at rooted
    have shape : destination.roots = [.global global] := (congrArg Prod.fst (Except.ok.inj rooted)).symm
    simp [AccessEnv.placeRoots, shape, pure] <;> rfl
  | slot slot =>
    have rooted := destination.rooted
    change Except.ok ([RootRef.local slot], destination.rootsStart) =
      Except.ok (destination.roots, destination.rootsEnd) at rooted
    have shape : destination.roots = [.local slot] := (congrArg Prod.fst (Except.ok.inj rooted)).symm
    simp [AccessEnv.placeRoots, shape, pure] <;> rfl

theorem PlaceSource.operandAlias {cfg : Cfg} {env : Env} {state after : St} {place : Place}
    (destination : PlaceSource cfg env place state) {path : List Nat}
    (placeRoots : destination.rootsEnv.access.placeRoots place = .ok destination.roots)
    (target : destination.ty.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after) :
    ∃ alias : RetainedAlias,
      destination.rootsEnv.access.aliasPlace path place = .ok [alias] ∧
      AliasAt cfg.mod destination.world env after.store alias (.ref location) := by
  have result := destination.result fuel location placed
  have valid := result.typed
  have locationType : HasTy cfg.mod destination.world.G after.store (.ref location) (.ref .mutable destination.ty) := by
    rcases valid with valid | invalid | invalid
    · exact ⟨location, rfl, Or.inl valid⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, impossible, _⟩ := invalid
      cases typeEq : destination.ty <;> simp_all [Ty.refTarget, Ty.isRefLike]
    · obtain ⟨_, _, _, _, _, _, _, _, _, impossible, _⟩ := invalid
      cases typeEq : destination.ty <;> simp_all [Ty.refTarget]
  have lookup := tyPlace_accessType (destination.frame.mod_t.trans destination.frame.mod_p.symm)
    (destination.frame.vars_t.trans destination.frame.vars_p.symm) destination.typed
  let alias : RetainedAlias := ⟨.ref .mutable destination.ty, destination.roots, .operand path⟩
  refine ⟨alias, ?_, locationType, ?_⟩
  · cases owner : destination.ty.ownerElem?.isSome <;>
      simp [AccessEnv.aliasPlace, lookup, placeRoots, Ty.interiorTarget?, owner, alias] <;> rfl
  · intro root target
    have rootEq : location.root = root := target
    rw [← rootEq]
    exact result.rooted

theorem accepted_assignment_destination_alias {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world)
    (placeRoots : source.rootsEnv.access.placeRoots place = .ok destination.roots) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after) :
    ∃ alias : RetainedAlias,
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok [alias] ∧
      AliasAt cfg.mod source.world env after.store alias (.ref location) := by
  have result := destination.operandAlias (path := source.path ++ [0])
    (by simpa only [roots] using placeRoots) (by simpa only [destinationType] using target) placed
  simpa only [roots, world] using result


theorem accepted_assignment_scalar_destination_alias {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : ScalarReadPlace place)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after) :
    ∃ alias : RetainedAlias,
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok [alias] ∧
      AliasAt cfg.mod source.world env after.store alias (.ref location) :=
  accepted_assignment_destination_alias source destination roots world (by simpa only [roots] using accepted_assignment_scalar_place_roots destination form) destinationType target placed

theorem accepted_assignment_destination_retained {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world)
    (placeRoots : source.rootsEnv.access.placeRoots place = .ok destination.roots) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {point : Pt} {id : ValueId}
    (post : Post cfg env cx before initial built frame point [(id, .val (.ref location))])
    {map : RetainedSsaMap} (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    ∃ aliases, source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases ∧
      (map.addValues id aliases).Realizes cfg.mod source.world env ⟨point, frame, after⟩ := by
  obtain ⟨alias, query, valid⟩ :=
    accepted_assignment_destination_alias source destination roots world placeRoots destinationType target placed
  refine ⟨[alias], query, RetainedSsaMap.addValues_realizes realized ?_⟩
  intro other member
  simp only [List.mem_singleton] at member
  subst other
  exact ValueAliasAt.of_post post (v := .ref location) (by simp) valid


theorem accepted_assignment_scalar_destination_retained {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : ScalarReadPlace place)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {point : Pt} {id : ValueId}
    (post : Post cfg env cx before initial built frame point [(id, .val (.ref location))])
    {map : RetainedSsaMap} (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    ∃ aliases, source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases ∧
      (map.addValues id aliases).Realizes cfg.mod source.world env ⟨point, frame, after⟩ :=
  accepted_assignment_destination_retained source destination roots world (by simpa only [roots] using accepted_assignment_scalar_place_roots destination form) destinationType target placed post realized

theorem StmtSource.AssignmentValueAt.retains_generated {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    {source : StmtSource cfg env (.assign place value origin) state} {child : ExprSource cfg env value after}
    (canonical : source.AssignmentValueAt child) {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases)
    (shrink : cfg.mod.profile = .shrink) : ∀ alias ∈ aliases, alias ∈ child.context.retained := by
  have retainedEq := demandContextRetainedEq canonical.plans canonical.path rfl canonical.context
  rw [retainedEq]
  have access := source.access
  cases contextEq : source.context with
  | pilot profile active => exact False.elim (by rw [shrink] at profile; cases profile)
  | @shrink planContext profile context =>
    rw [contextEq] at access
    have accessEq : planContext.approvals.access = source.rootsEnv.access := by
      have moduleEq := access.2.2.1
      have implementationEq := access.2.2.2.1
      have contextEq := access.2.2.2.2
      cases accessAt : planContext.approvals.access
      rw [accessAt] at moduleEq implementationEq contextEq
      unfold PEnv.access
      congr 1
    let transition := context.child rfl 1 (.expression value) .expression rfl (by trivial)
    have generated : (DemandNode.statement (.assign place value origin)).retainedForChild
        planContext.approvals.access source.path 1 = .ok aliases := by
      simpa [DemandNode.retainedForChild, accessEq] using query
    intro alias member
    have included := DemandNode.childFrame_newAlias transition.childFrameEq generated member
    change alias ∈ transition.context.expected.frame.retained
    rw [transition.expectedFrameEq]
    exact DemandNode.phaseFrame_retains transition.phaseFrameEq included

theorem RetainedSsaMap.Covers.addValues {map required : RetainedSsaMap} (coverage : map.Covers required)
    (id : ValueId) (aliases : List RetainedAlias) :
    (map.addValues id aliases).Covers (required.addValues id aliases) := by
  constructor
  · intro cell member
    rcases List.mem_append.mp member with added | old
    · exact List.mem_append_left _ added
    · exact List.mem_append_right _ (coverage.1 cell old)
  · exact coverage.2

theorem RetainedSsaMap.addValues_admitted {map : RetainedSsaMap} {profile : ArtifactProfile}
    {retained : List RetainedAlias} (admitted : map.Admitted profile retained)
    {id : ValueId} {aliases : List RetainedAlias}
    (produced : profile = .shrink → ∀ alias ∈ aliases, alias ∈ retained) :
    (map.addValues id aliases).Admitted profile retained := by
  intro shrink alias member
  change alias ∈ (aliases.map (fun alias => (id, alias)) ++ map.values).map Prod.snd ++ map.runs.map Prod.snd at member
  simp only [List.map_append, List.map_map, Function.comp_def, List.mem_append] at member
  rcases member with (added | old) | old
  · exact produced shrink alias (by simpa using added)
  · exact admitted shrink alias (List.mem_append_left _ old)
  · exact admitted shrink alias (List.mem_append_right _ old)

theorem RetainedSsaMap.addValues_bounded {map : RetainedSsaMap} {frontier id : ValueId}
    (bounded : map.Bounded frontier) (fresh : id < frontier) (aliases : List RetainedAlias) :
    (map.addValues id aliases).Bounded frontier := by
  constructor
  · intro cell member
    rcases List.mem_append.mp member with added | old
    · obtain ⟨alias, _, equal⟩ := List.mem_map.mp added
      cases equal
      exact fresh
    · exact bounded.1 cell old
  · exact bounded.2


theorem accepted_assignment_value_demand_of_retained {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state)
    (child : ExprSource cfg env value after) (childAt : source.AssignmentValueAt child)
    (childTyping : child.typingEnv = source.typingEnv) (childRoots : child.rootsEnv = source.rootsEnv)
    {cx : FnCtx} {results : List Ty} {before : LS} {initial frame : GIR.Frame} {start point : Pt} {loop : Option LoopCtx}
    {map required : RetainedSsaMap} (coverage : map.Covers required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    {location : Loc} (post : Post cfg env cx before initial (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    {aliases : List RetainedAlias} (query : source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases)
    (realizedNext : (map.addValues (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
      cfg.mod source.world env ⟨point, frame, after⟩) :
    let id := (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1
    let next := map.addValues id aliases
    next.Covers (required.addValues id aliases) ∧
    next.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
    next.Admitted cfg.mod.profile child.context.retained ∧
    next.Realizes cfg.mod child.world env ⟨point, frame, after⟩ ∧
    GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
      (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  let id := (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
    rw [demandContextRetainedEq childAt.plans childAt.path rfl childAt.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 1 (.expression value) .expression rfl (by trivial)
      (admitted profile alias member)
  have nextAdmitted : (map.addValues id aliases).Admitted cfg.mod.profile child.context.retained :=
    RetainedSsaMap.addValues_admitted childAdmitted (fun profile => childAt.retains_generated query profile)
  have idBound : id < (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size :=
    post.lt (id, .val (.ref location)) (by simp [id])
  have nextBounded := RetainedSsaMap.addValues_bounded bounded idBound aliases
  have nextRealized : (map.addValues id aliases).Realizes cfg.mod child.world env ⟨point, frame, after⟩ := by
    simpa only [childAt.world] using realizedNext
  have placeAdv := advB_lowerPlace place (lowerEnv cfg.mod env.vars results) before
    (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1
    (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 rfl
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
      (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point := by
    refine ⟨?_, ?_, post.pp, post.rel, input.moduleEq, input.resultsEq, input.depth,
      (by cases loop <;> exact input.targets), input.counter.afterPost (post.sub (by simp)),
      input.generated.lowerPlace place rfl, input.frames.mono placeAdv.ext⟩
    · simpa only [childTyping, childRoots] using input.metadata
    · simpa only [childTyping] using input.loops
  exact ⟨coverage.addValues id aliases, nextBounded, nextAdmitted, nextRealized, childInput⟩

#print axioms accepted_assignment_value_demand_of_retained

theorem accepted_assignment_value_demand {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world)
    (placeRoots : source.rootsEnv.access.placeRoots place = .ok destination.roots) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after)
    (child : ExprSource cfg env value after) (childAt : source.AssignmentValueAt child)
    (childTyping : child.typingEnv = source.typingEnv) (childRoots : child.rootsEnv = source.rootsEnv)
    {cx : FnCtx} {results : List Ty} {before : LS} {initial frame : GIR.Frame} {start point : Pt} {loop : Option LoopCtx}
    {map required : RetainedSsaMap} (coverage : map.Covers required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (post : Post cfg env cx before initial (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    ∃ aliases,
      let id := (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1
      let next := map.addValues id aliases
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases ∧
      next.Covers (required.addValues id aliases) ∧
      next.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      next.Admitted cfg.mod.profile child.context.retained ∧
      next.Realizes cfg.mod child.world env ⟨point, frame, after⟩ ∧
      GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
        (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point := by
  let id := (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1
  obtain ⟨aliases, query, realizedNext⟩ := accepted_assignment_destination_retained
    source destination roots world placeRoots destinationType target placed post realized
  obtain ⟨nextCoverage, nextBounded, nextAdmitted, nextRealized, nextInput⟩ :=
    accepted_assignment_value_demand_of_retained source child childAt childTyping childRoots coverage admitted bounded input post query realizedNext
  exact ⟨aliases, query, nextCoverage, nextBounded, nextAdmitted, nextRealized, nextInput⟩


theorem accepted_assignment_scalar_value_demand {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : ScalarReadPlace place)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after)
    (child : ExprSource cfg env value after) (childAt : source.AssignmentValueAt child)
    (childTyping : child.typingEnv = source.typingEnv) (childRoots : child.rootsEnv = source.rootsEnv)
    {cx : FnCtx} {results : List Ty} {before : LS} {initial frame : GIR.Frame} {start point : Pt} {loop : Option LoopCtx}
    {map required : RetainedSsaMap} (coverage : map.Covers required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (post : Post cfg env cx before initial (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    ∃ aliases,
      let id := (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1
      let next := map.addValues id aliases
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases ∧
      next.Covers (required.addValues id aliases) ∧
      next.Bounded (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      next.Admitted cfg.mod.profile child.context.retained ∧
      next.Realizes cfg.mod child.world env ⟨point, frame, after⟩ ∧
      GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
        (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 frame point :=
  accepted_assignment_value_demand source destination roots world (by simpa only [roots] using accepted_assignment_scalar_place_roots destination form) destinationType target placed child childAt childTyping childRoots coverage admitted bounded input post realized

#print axioms accepted_assignment_destination_alias
#print axioms accepted_assignment_destination_retained
#print axioms accepted_assignment_value_demand
#print axioms accepted_assignment_scalar_value_demand
#print axioms StmtSource.AssignmentValueAt.retains_generated
#print axioms RetainedSsaMap.addValues_admitted
#print axioms accepted_assignment_scalar_destination_alias
#print axioms accepted_assignment_scalar_destination_retained

end Goose.Lower
