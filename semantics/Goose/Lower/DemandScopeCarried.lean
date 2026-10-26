import Goose.Lower.DemandParameterPrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

private theorem alias_enter_scope {module : Core.Module} {world : World} {env : Env}
    {typing : TEnv} {roots : PEnv} {state : St} {future : List VarId}
    (source : Core.Sound.Frame module world typing roots env state future)
    {scope : ScopeId} (fresh : scope ∉ typing.scopes) (instanceId : ScopeInst)
    {alias : RetainedAlias} {value : Val} (realized : AliasAt module world env state.store alias value) :
    AliasAt module world { env with scopes := (scope, instanceId) :: env.scopes } state.store alias value :=
  ⟨realized.1, fun root target => gam_push source fresh instanceId (realized.2 root target)⟩

theorem RetainedSsaMap.enter_scope {module : Core.Module} {world : World} {env : Env}
    {typing : TEnv} {roots : PEnv} {state : St} {future : List VarId}
    (source : Core.Sound.Frame module world typing roots env state future)
    {scope : ScopeId} (fresh : scope ∉ typing.scopes) {map : RetainedSsaMap}
    {point : Pt} {frame : GIR.Frame} (realized : map.Realizes module world env ⟨point, frame, state⟩) :
    map.Realizes module world { env with scopes := (scope, state.nextScope) :: env.scopes }
      ⟨point, { frame with scopes := (scope, state.nextScope) :: frame.scopes },
        { state with nextScope := state.nextScope + 1 }⟩ := by
  constructor
  · intro cell member
    obtain ⟨value, valueAt, aliasAt⟩ := realized.1 cell member
    exact ⟨value, valueAt, alias_enter_scope source fresh _ aliasAt⟩
  · intro cell member
    rcases realized.2 cell member with slice | limited
    · obtain ⟨sample, mutability, element, valueAt, typeEq, aliasAt⟩ := slice
      exact Or.inl ⟨sample, mutability, element, valueAt, typeEq, alias_enter_scope source fresh _ aliasAt⟩
    · obtain ⟨sample, mutability, element, capacity, valueAt, typeEq, aliasAt, physical⟩ := limited
      exact Or.inr ⟨sample, mutability, element, capacity, valueAt, typeEq,
        alias_enter_scope source fresh _ aliasAt, physical⟩

theorem ParameterPrefixCursor.retained_inner {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} {source : BlockSource cfg env pre block state} {count : Nat}
    (cursor : ParameterPrefixCursor source count) {map : RetainedSsaMap} {frame : GIR.Frame} {point : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨point, frame, state⟩) :
    map.Realizes cfg.mod source.world { env with scopes := (block.scope, state.nextScope) :: env.scopes }
      ⟨point, { frame with scopes := (block.scope, state.nextScope) :: frame.scopes },
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope (pre.take count) state.store }⟩ := by
  have entered := RetainedSsaMap.enter_scope source.frame source.fresh realized
  exact cursor.retained entered

end Goose.Lower
