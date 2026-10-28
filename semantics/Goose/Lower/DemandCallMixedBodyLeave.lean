import Goose.Lower.DemandCallMixedBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_parameterized_body_leave {cfg : Cfg} {env : Env} {pre : List (VarId × Val)}
    {block : Core.Block} {state : St} (source : BlockSource cfg env pre block state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS}
    {bindings : List (SlotId × ValueId × OriginId)}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block none bindings false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (cells : PreRel initial bindings pre)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results none source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock none bindings false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (entry : RuntimePoint cx.cfg cx.fn start initial state) (noValue : block.value = none)
    {sourceFuel : Nat} {current : DemandRuntimePoint}
    (statements : execStmts sourceFuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts
      { state with nextScope := state.nextScope + 1, store := preStore env.act state.nextScope pre state.store } =
        .ok (.normal .unit) current.state)
    (post : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx
      (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)
      { initial with scopes := (block.scope, state.nextScope) :: initial.scopes }
      (lowerStmts none block.stmts (lowerEnv cfg.mod env.vars results)
        (demandBlockStatementsBefore (lowerEnv cfg.mod env.vars results) before bindings block)).2 current.frame current.point [])
    {next : DemandRuntimePoint}
    (step : RuntimeStep cx.cfg cx.fn current.point current.frame current.state next.point next.frame next.state) :
    execBlock (sourceFuel + 1) cfg env pre block state = .ok (.normal .unit) next.state ∧
    Post cfg env cx before initial (lowerBlock none bindings false block (lowerEnv cfg.mod env.vars results) before).2 next.frame next.point [] ∧
    BlockResult source (.normal .unit) next.state ∧
    map.Bounded (lowerBlock none bindings false block (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
    map.Realizes cfg.mod source.world env next := by
  obtain ⟨body, bodyAll, bodyScope, bodyValue, bodyOffset, bodyOccurrence, bodyRows, bodyOwned, bodyAdmitted,
    bodyBounded, bodyRealized, bodyInput, prologuePost, bodyReached⟩ :=
    accepted_generated_post_prologue source selected owned occurrence rows coverage admitted bounded cells realized input extended entry
  have wholePost := prologuePost.comp post
  have valuePost : Post cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } cx before initial
      (lowerBlockValue false block.value (lowerEnv cfg.mod env.vars results)
        (demandBlockValueBefore (lowerEnv cfg.mod env.vars results) before none bindings block)).2 current.frame current.point [] := by
    simpa [noValue, lowerBlockValue, demandBlockValueBefore, pure_run] using wholePost
  have valueDone : valueFlow sourceFuel cfg block.value
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } (.normal .unit) current.state =
        .ok (.normal .unit) current.state := by rw [noValue]; rfl
  obtain ⟨_, _, _, _, evaluated, finalPost, result, finalBounded, finalDemand⟩ :=
    accepted_generated_block_leave_runtime_step source occurrence rows coverage admitted bounded realized
      statements valueDone valuePost extended step
  exact ⟨evaluated, finalPost, result, finalBounded, finalDemand.operands⟩

#print axioms accepted_generated_parameterized_body_leave
end Goose.Lower
