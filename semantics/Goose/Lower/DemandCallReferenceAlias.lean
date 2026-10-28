import Goose.Lower.DemandAssignmentScalarAlias
import Goose.Lower.DemandCallReferenceAddress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_call_reference_alias {cfg : Cfg} {env : Env} {initialState state after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {mutability : Mutability} {place : Place}
    (found : arguments[index]? = some (.byRef mutability place)) (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true)
    (canonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef mutability place) found))
    (form : ScalarReadPlace place) {fuel : Nat} {location : Loc}
    (placed : evalPlace fuel cfg env place state = .ok location after) :
    ∃ alias : RetainedAlias,
      source.rootsEnv.access.aliasArg (source.path ++ [index]) (.byRef mutability place) = .ok [alias] ∧
      AliasAt cfg.mod source.world env after.store alias (.ref location) := by
  obtain ⟨plans, path, world, typing, roots, childContext⟩ := canonical
  obtain ⟨alias, query, valid⟩ := child.operandAlias (path := source.path ++ [index])
    (accepted_assignment_scalar_place_roots child form) target placed
  have accessType := tyPlace_accessType (child.frame.mod_t.trans child.frame.mod_p.symm)
    (child.frame.vars_t.trans child.frame.vars_p.symm) child.typed
  have argQuery : child.rootsEnv.access.aliasArg (source.path ++ [index]) (.byRef mutability place) = .ok [alias] := by
    cases typeEq : child.ty <;> simp_all [AccessEnv.aliasArg, Ty.refTarget]
  exact ⟨alias, by simpa only [roots] using argQuery, by simpa only [world] using valid⟩

theorem accepted_call_reference_retained {cfg : Cfg} {env : Env} {initialState state after : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {mutability : Mutability} {place : Place}
    (found : arguments[index]? = some (.byRef mutability place)) (child : PlaceSource cfg env place state)
    (target : child.ty.refTarget = true)
    (canonical : (ArgSource.byRef mutability child (Or.inl target)).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef mutability place) found))
    (form : ScalarReadPlace place) {fuel : Nat} {location : Loc}
    (placed : evalPlace fuel cfg env place state = .ok location after)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {point : Pt} {id : ValueId}
    (post : Post cfg env cx before initial built frame point [(id, .val (.ref location))])
    {map : RetainedSsaMap} (realized : map.Realizes cfg.mod source.world env ⟨point, frame, after⟩) :
    ∃ aliases, source.rootsEnv.access.aliasArg (source.path ++ [index]) (.byRef mutability place) = .ok aliases ∧
      (map.addValues id aliases).Realizes cfg.mod source.world env ⟨point, frame, after⟩ := by
  obtain ⟨alias, query, valid⟩ := accepted_call_reference_alias source found child target canonical form placed
  refine ⟨[alias], query, RetainedSsaMap.addValues_realizes realized ?_⟩
  intro other member
  simp only [List.mem_singleton] at member
  subst other
  exact ValueAliasAt.of_post post (v := .ref location) (by simp) valid

#print axioms PlaceSource.operandAlias
#print axioms accepted_call_reference_retained
#print axioms accepted_call_reference_alias
end Goose.Lower
