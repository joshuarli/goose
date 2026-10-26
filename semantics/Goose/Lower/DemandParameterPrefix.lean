import Goose.Lower.SourceContexts
import Goose.Lower.DemandCarried

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

structure ParameterPrefixCursor {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state) (count : Nat) where
  typing : TEnv
  frame : Core.Sound.Frame cfg.mod source.world typing
    { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes }
    { env with scopes := (block.scope, state.nextScope) :: env.scopes }
    { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope (pre.take count) state.store }
    ((pre.take count).map Prod.fst ++ source.context.inputFuture)
  same : TSame { source.typingEnv with scopes := block.scope :: source.typingEnv.scopes } typing
  visible : ∀ varId, varId ∈ typing.visible ↔
    varId ∈ (pre.take count).map Prod.fst ∨ varId ∈ source.typingEnv.visible
  growth : Goose.Proofs.Memory.StoreLe state.store
    (preStore env.act state.nextScope (pre.take count) state.store)
  oldRoots : ∀ (root : RootInst) (value : Val), state.store.roots[root]? = some value →
    (preStore env.act state.nextScope (pre.take count) state.store).roots[root]? = some value
  newRoots : ∀ (root : RootInst) (value : Val),
    (preStore env.act state.nextScope (pre.take count) state.store).roots[root]? = some value →
      state.store.roots[root]? = some value ∨
        ∃ varId, varId ∈ (pre.take count).map Prod.fst ∧
          root = .local env.act state.nextScope varId

theorem BlockSource.parameterPrefix {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state) (count : Nat) :
    Nonempty (ParameterPrefixCursor source count) := by
  have pushed := source.frame.push source.fresh
  have fresh : ∀ varId,
      state.store.roots[RootInst.local env.act state.nextScope varId]? = none := by
    intro varId
    cases found : state.store.roots[RootInst.local env.act state.nextScope varId]? with
    | none => rfl
    | some value =>
      exact absurd (source.frame.inv.fresh _ _ _ (by rw [found]; simp)) (Nat.lt_irrefl _)
  obtain ⟨unique, typed⟩ := source.pretyped
  have prefixUnique : ((pre.take count).map Prod.fst).Nodup := by
    rw [List.map_take]
    exact unique.take
  obtain ⟨typing, frame, same, visible, growth, oldRoots, newRoots⟩ :=
    frame_pre (future := source.context.inputFuture)
      (penv := { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes })
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      (rest0 := env.scopes) rfl (pre.take count) _
      { state with nextScope := state.nextScope + 1 } pushed prefixUnique (by
        intro varId value member
        obtain ⟨_, _, localVar, lookup, scope, parameter, valueType, roots⟩ :=
          typed varId value (List.mem_of_mem_take member)
        refine ⟨fresh varId, localVar, lookup, scope, parameter, valueType, ?_, ?_⟩
        · intro root target
          obtain ⟨annotation, annotated, denotes, _⟩ := roots root target
          refine ⟨⟨annotation, annotated, denotes⟩, ?_⟩
          rcases hasTy_target_dom valueType target with ⟨global, rfl⟩ | present
          · trivial
          · cases root with
            | global global => trivial
            | «local» activation instanceId variableId =>
              exact Nat.le_of_lt (source.frame.inv.fresh _ _ _ present)
        · intro owner root target
          obtain ⟨annotation, annotated, _, denotes⟩ := roots root target
          exact ⟨annotation, annotated, denotes owner⟩)
  exact ⟨⟨typing, frame, same, visible, growth, oldRoots, newRoots⟩⟩

theorem ParameterPrefixCursor.retained {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} {source : BlockSource cfg env pre block state} {count : Nat}
    (cursor : ParameterPrefixCursor source count) {map : RetainedSsaMap} {targetFrame : GIR.Frame}
    {point : Pt} {world : World} {caller : Env}
    (realized : map.Realizes cfg.mod world caller ⟨point, targetFrame, state⟩) :
    map.Realizes cfg.mod world caller ⟨point, targetFrame,
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope (pre.take count) state.store }⟩ := by
  have retention : RetainsAliases cfg.mod world caller state.store
      (preStore env.act state.nextScope (pre.take count) state.store)
      (map.values.map Prod.snd ++ map.runs.map Prod.snd) := retainedAliases_of_storeLe cursor.growth _
  constructor
  · intro cell member
    apply (realized.1 cell member).retained (frontier := cell.1 + 1)
      (fun _ _ => rfl) (Nat.lt_succ_self _)
    exact retention cell.2 (List.mem_append_left _ (List.mem_map.mpr ⟨cell, member, rfl⟩))
  · intro cell member
    apply (realized.2 cell member).retained (frontier := cell.1 + 1)
      (fun _ _ => rfl) (Nat.lt_succ_self _)
    exact retention cell.2 (List.mem_append_right _ (List.mem_map.mpr ⟨cell, member, rfl⟩))

end Goose.Lower
