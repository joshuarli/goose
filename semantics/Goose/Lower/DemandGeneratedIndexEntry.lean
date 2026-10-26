import Goose.Lower.DemandGeneratedTransfer

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

def GeneratedIndexEntry {cfg : Cfg} {env : Env} {view : View} {index : Expr} {origin : OriginId}
    {state : St} (source : PlaceSource cfg env (.elem view index origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem view index origin)) before)
    (required map : RetainedSsaMap) (aliases : List RetainedAlias) (runtime : DemandRuntimePoint) : Prop :=
  ∃ child : ExprSource cfg env index runtime.state,
  source.ExpressionChildAt child 1 rfl ∧ child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
  (∃ type, child.ty = .int type) ∧ GeneratedDemandRows cfg.mod source.rootsEnv.access (.index occurrence)
    (required.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases) ∧
  (map.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases).Covers
    (required.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases) ∧
  (map.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases).Admitted
    cfg.mod.profile child.context.retained ∧
  (map.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases).Bounded
    (lowerView view (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
  (lowerView view (lowerEnv cfg.mod env.vars results) before).2.pp = some runtime.point ∧
  DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
    (map.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases).values
    (map.addRuns (lowerView view (lowerEnv cfg.mod env.vars results) before).1 aliases).runs runtime

theorem accepted_generated_index_entry {cfg : Cfg} {env : Env} {view : View} {index : Expr}
    {origin : OriginId} {state after : St} (source : PlaceSource cfg env (.elem view index origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.place (.elem view index origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {start point : Pt} {initial frame : GIR.Frame}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasView (source.path ++ [0]) view = .ok aliases)
    {fuel : Nat} {sample : ViewVal} (evaluated : evalView fuel cfg env view state = .ok sample after)
    (post : Post cfg env cx before initial
      (lowerView view (lowerEnv cfg.mod env.vars results) before).2 frame point
      [((lowerView view (lowerEnv cfg.mod env.vars results) before).1, .view sample)]) :
    GeneratedIndexEntry source occurrence required map aliases ⟨point, frame, after⟩ := by
  obtain ⟨type, left, leftTyping, leftRoots, leftCanonical, next⟩ := source.elemChildren origin
  obtain ⟨child, childTyping, childRoots, childType, childCanonical⟩ := next fuel sample after evaluated
  have result := left.result fuel sample evaluated
  have retained : RetainsAliases cfg.mod source.world env state.store after.store
      (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
    cases profile : cfg.mod.profile with
    | pilot =>
      have growth := result.pilotStore profile
      exact retainedAliases_of_storeLe growth _
    | shrink =>
      have oldIncluded : ∀ alias ∈ map.values.map Prod.snd ++ map.runs.map Prod.snd,
          alias ∈ left.context.retained := fun alias member => leftCanonical.retained alias (admitted profile alias member)
      simpa only [leftCanonical.world] using result.aliases.subset oldIncluded
  have carried := realized.retained post.same bounded.1 bounded.2 retained
  have leftQuery : left.rootsEnv.access.aliasView left.path view = .ok aliases := by
    simpa only [leftRoots, leftCanonical.path] using query
  have cell := post.has ((lowerView view (lowerEnv cfg.mod env.vars results) before).1, .view sample) (by simp)
  have extended := result.extend_generated_runs (point := point) leftQuery
    (by simpa only [leftCanonical.world, RetainedSsaMap.Realizes] using carried) cell
  have childAdmission : map.Admitted cfg.mod.profile child.context.retained := by
    intro shrink alias member
    exact childCanonical.retained alias (admitted shrink alias member)
  refine ⟨child, childCanonical, childTyping, childRoots, ⟨type, childType⟩, .index rows query, coverage.addRuns _ aliases,
    RetainedSsaMap.addRuns_admitted childAdmission (childCanonical.index_retains_generated query),
    RetainedSsaMap.addRuns_bounded (bounded.mono post.mono) (post.lt ((lowerView view (lowerEnv cfg.mod env.vars results) before).1, .view sample) (by simp)) aliases, post.pp,
    ⟨⟨_, post.pp, post.rel⟩, child.frame, ?_⟩⟩
  simpa only [leftCanonical.world, childCanonical.world, RetainedSsaMap.Realizes] using extended

end Goose.Lower
