import Goose.Lower.DemandGeneratedBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure ParameterizedBlockBodyAt {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    (body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }) : Prop where
  typing : body.typingEnv = source.typingInner
  typingAfter : body.typingAfter = source.typingAfter
  roots : body.rootsEnv = { source.rootsEnv with scopes := block.scope :: source.rootsEnv.scopes }
  world : body.world = source.world
  plans : body.plans = source.plans
  path : body.path = source.path
  scope : body.scope = block.scope
  all : body.all = block.stmts
  value : body.value = block.value
  offset : body.offset = 0
  context : HEq body.context source.context
  typingEnd : body.typingEnd = source.typingValue
  rootsEnd : body.rootsEnd = source.rootsValue

theorem accepted_generated_parameterized_body_at {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {want : Bool}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop bindings want block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {frame : GIR.Frame} (cells : PreRel frame bindings pre)
    {initialPoint : Pt} (realized : map.Realizes cfg.mod source.world env ⟨initialPoint, frame, state⟩)
    {point : Pt} (atPoint : (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block).pp = some point)
    (related : Rel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx
      { frame with scopes := (block.scope, state.nextScope) :: frame.scopes }
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)) :
    ∃ body : StmtsSource cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
        { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store },
      ParameterizedBlockBodyAt source body ∧
      ∃ bodyOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root body.path (.block loop bindings want block) before,
        GeneratedDemandRows cfg.mod body.rootsEnv.access bodyOccurrence required ∧
        map.Admitted cfg.mod.profile body.context.retained ∧
        DemandFrameAt cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx body.world
          body.typingEnv body.rootsEnv (blockSuffixFuture body.context body.offset) map.values map.runs
          ⟨point, { frame with scopes := (block.scope, state.nextScope) :: frame.scopes },
            { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store }⟩ := by
  obtain ⟨body, typing, typingAfter, roots, world, _, _, typingEnd, _, rootsEnd, plans, path,
    scope, all, value, offset, context, bodyOccurrence, bodyRows, _, bodyAdmitted, _, bodyDemand⟩ :=
    accepted_generated_body_entry source occurrence rows coverage admitted cells realized atPoint related
  exact ⟨body, ⟨typing, typingAfter, roots, world, plans, path, scope, all, value, offset, context, typingEnd, rootsEnd⟩,
    bodyOccurrence, bodyRows, bodyAdmitted, bodyDemand⟩

#print axioms accepted_generated_parameterized_body_at
end Goose.Lower
