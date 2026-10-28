import Goose.Lower.DemandAssignmentScalarAlias
import Goose.Lower.DemandGeneratedIndexAbort

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive IndexedScalarPlace : Place → Prop
  | element {owner : Place} (index : Expr) (origin : OriginId) (form : ScalarReadPlace owner) :
      IndexedScalarPlace (.elem (.of owner) index origin)

private theorem accepted_assignment_index_place_roots {cfg : Cfg} {env : Env} {state : St} {place : Place}
    (destination : PlaceSource cfg env place state) (form : IndexedScalarPlace place) :
    destination.rootsEnv.access.placeRoots place = .ok destination.roots := by
  cases form with
  | element index origin ownerForm =>
    have rooted := destination.rooted
    simp only [rpPlace, rpView] at rooted
    cases ownerForm with
    | global global =>
      simp only [rpPlace] at rooted
      inv at rooted
      obtain ⟨a, s1, ⟨reads, shape⟩, other, s2, expr, aborted, roots⟩ := rooted
      rw [roots.2.1, shape.2.1]
      rfl
    | slot slot =>
      simp only [rpPlace] at rooted
      inv at rooted
      obtain ⟨a, s1, ⟨reads, shape⟩, other, s2, expr, aborted, roots⟩ := rooted
      rw [roots.2.1, shape.2.1]
      rfl

theorem accepted_assignment_index_destination_alias {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : IndexedScalarPlace place)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after) :
    ∃ alias : RetainedAlias,
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok [alias] ∧
      AliasAt cfg.mod source.world env after.store alias (.ref location) :=
  accepted_assignment_destination_alias source destination roots world (by simpa only [roots] using accepted_assignment_index_place_roots destination form) destinationType target placed

theorem accepted_assignment_index_destination_retained {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : IndexedScalarPlace place)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {point : Pt} {id : ValueId}
    (post : Post cfg env cx before initial built frame point [(id, .val (.ref location))])
    {map : RetainedSsaMap} (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    ∃ aliases, source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases ∧
      (map.addValues id aliases).Realizes cfg.mod source.world env ⟨point, frame, after⟩ :=
  accepted_assignment_destination_retained source destination roots world (by simpa only [roots] using accepted_assignment_index_place_roots destination form) destinationType target placed post realized

theorem accepted_assignment_index_value_demand {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : IndexedScalarPlace place)
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
  accepted_assignment_value_demand source destination roots world (by simpa only [roots] using accepted_assignment_index_place_roots destination form) destinationType target placed child childAt childTyping childRoots coverage admitted bounded input post realized

#print axioms accepted_assignment_index_value_demand
end Goose.Lower
