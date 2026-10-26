import Goose.Lower.DemandCarried

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

structure ExpressionDemandBoundary {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    (source : ExprSource cfg env expression state) (map : RetainedSsaMap) (cx : FnCtx)
    (before : LS) (initial : GIR.Frame) (built : LS) (id : ValueId)
    (value : Val) (after : St) (point : Pt) (frame : GIR.Frame) : Prop where
  post : Post cfg env cx before initial built frame point [(id, .val value)]
  demanded : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv
    source.context.outputFuture map.values map.runs ⟨point, frame, after⟩
  bounded : map.Bounded built.vals.size
  produced : ValueAliasAt cfg.mod source.world env after.store frame id
    ⟨source.ty, source.roots, .operand source.path⟩
  canonical : ∀ aliases, source.rootsEnv.access.aliasExpr source.path expression = .ok aliases →
    ∀ alias ∈ aliases, ValueAliasAt cfg.mod source.world env after.store frame id alias

private theorem sourceRetention {m : Core.Module} {world : World} {env : Env}
    {before after : Store} (growth : Goose.Proofs.Memory.StoreLe before after)
    (aliases : List RetainedAlias) : RetainsAliases m world env before after aliases := by
  intro alias member
  constructor
  · intro value realized
    exact ⟨HasTy.mono growth realized.1, realized.2⟩
  · intro mutability element capacity location start length typeEq realized typed
    exact SliceTy.mono growth typed

theorem ExprResult.generated_value {cfg : Cfg} {env : Env} {expression : Expr} {state after : St}
    {source : ExprSource cfg env expression state} {value : Val} (result : ExprResult source value after)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {point : Pt} {id : ValueId}
    (post : Post cfg env cx before initial built frame point [(id, .val value)])
    {aliases : List RetainedAlias}
    (query : source.rootsEnv.access.aliasExpr source.path expression = .ok aliases)
    {alias : RetainedAlias} (member : alias ∈ aliases) :
    ValueAliasAt cfg.mod source.world env after.store frame id alias := by
  have lookup := tyExpr_accessType (source.frame.mod_t.trans source.frame.mod_p.symm)
    (source.frame.vars_t.trans source.frame.vars_p.symm) source.typed
  cases interior : source.ty.interiorTarget?.isSome with
  | false =>
    simp only [AccessEnv.aliasExpr, lookup, interior, Bool.false_eq_true, ite_false] at query
    have empty : aliases = [] := (ex_pure_ok _ _).mp query
    rw [empty] at member
    cases member
  | true =>
    simp only [AccessEnv.aliasExpr, lookup, interior, ite_true] at query
    obtain ⟨roots, rootsChecked, aliasesChecked⟩ := (ex_bind_ok _ _ _).mp query
    have shape : aliases = [⟨source.ty, roots, .operand source.path⟩] :=
      (ex_pure_ok _ _).mp aliasesChecked
    rw [shape] at member
    simp only [List.mem_singleton] at member
    subst alias
    have included := rpExpr_accessRoots source.rootsEnv expression source.rootsStart
      source.roots source.rootsEnd roots source.rooted rootsChecked
    apply ValueAliasAt.of_post post (v := value) (by simp)
    exact ⟨result.typed, fun root target => (result.rooted root target).subset included⟩

theorem ExpressionDemandBoundary.of_result {cfg : Cfg} {env : Env} {expression : Expr} {state after : St}
    {source : ExprSource cfg env expression state} {value : Val} (result : ExprResult source value after)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {point start : Pt} {id : ValueId}
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (post : Post cfg env cx before initial built frame point [(id, .val value)]) :
    ExpressionDemandBoundary source map cx before initial built id value after point frame := by
  have retained : RetainsAliases cfg.mod source.world env state.store after.store
      (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
    cases profile : cfg.mod.profile with
    | pilot => exact sourceRetention (result.pilotStore profile) _
    | shrink => exact result.aliases.subset (admitted profile)
  have carried := realized.retained post.same bounded.1 bounded.2 retained
  exact ⟨post, ⟨⟨built, post.pp, post.rel⟩, result.frame, carried⟩, bounded.mono post.mono,
    ValueAliasAt.of_post post (v := value) (by simp) ⟨result.typed, result.rooted⟩,
    fun aliases query alias member => result.generated_value post query member⟩

end Goose.Lower
