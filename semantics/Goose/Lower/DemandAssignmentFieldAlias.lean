import Goose.Lower.DemandAssignmentScalarAlias
import Goose.Lower.DemandFieldScalarAddress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive FieldScalarPlace : Place → Prop
  | field {owner : Place} (index : Nat) (form : ScalarReadPlace owner) : FieldScalarPlace (.field owner index)

private theorem accepted_assignment_field_place_roots {cfg : Cfg} {env : Env} {state : St} {place : Place}
    (destination : PlaceSource cfg env place state) (form : FieldScalarPlace place) :
    destination.rootsEnv.access.placeRoots place = .ok destination.roots := by
  cases form with
  | field index ownerForm =>
    cases ownerForm with
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

theorem accepted_assignment_field_destination_alias {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : FieldScalarPlace place)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after) :
    ∃ alias : RetainedAlias,
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok [alias] ∧
      AliasAt cfg.mod source.world env after.store alias (.ref location) :=
  accepted_assignment_destination_alias source destination roots world (by simpa only [roots] using accepted_assignment_field_place_roots destination form) destinationType target placed

theorem accepted_assignment_field_destination_retained {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : FieldScalarPlace place)
    (destination : PlaceSource cfg env place state) (roots : destination.rootsEnv = source.rootsEnv)
    (world : destination.world = source.world) {type : Ty} (destinationType : destination.ty = type)
    (target : type.refTarget = true)
    {fuel : Nat} {location : Loc} (placed : evalPlace fuel cfg env place state = .ok location after)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {point : Pt} {id : ValueId}
    (post : Post cfg env cx before initial built frame point [(id, .val (.ref location))])
    {map : RetainedSsaMap} (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    ∃ aliases, source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases ∧
      (map.addValues id aliases).Realizes cfg.mod source.world env ⟨point, frame, after⟩ :=
  accepted_assignment_destination_retained source destination roots world (by simpa only [roots] using accepted_assignment_field_place_roots destination form) destinationType target placed post realized

theorem accepted_assignment_field_value_demand {cfg : Cfg} {env : Env} {state after : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state) (form : FieldScalarPlace place)
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
  accepted_assignment_value_demand source destination roots world (by simpa only [roots] using accepted_assignment_field_place_roots destination form) destinationType target placed child childAt childTyping childRoots coverage admitted bounded input post realized

#print axioms accepted_assignment_field_value_demand
end Goose.Lower
