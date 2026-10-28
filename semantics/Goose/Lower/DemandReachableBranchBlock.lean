import Goose.Lower.DemandReachableSequence
import Goose.Lower.DemandBranchBlockStopped

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_reachable_branch_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (cursor : ∀ {statement : Stmt} {innerState : St}, StmtSource cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } statement innerState →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop)
    (bodyFamily : ReachableSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] false block block.stmts cursor)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit)
    (noValue : block.value = none) (entry : RuntimePoint cx.cfg cx.fn start initial state)
    {taken : Nat} {reached : DemandRuntimePoint} (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedGenericBranchBlockDecomposition source selected map required before loop initial start cursor taken reached := by
  exact accepted_generated_invariant_branch_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended
    cursor (fun point => RuntimePoint cx.cfg cx.fn point.point point.frame point.state)
    (fun valid steps => steps.reachable valid) entry bodyFamily normal noValue steps

theorem accepted_generated_reachable_loop_branch_block_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state) {cx : FnCtx} {results : List Ty} {root : DemandNode}
    {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    (bodyFamily : ReachableStoppedSequencePrefixFamily
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before loop [] false block block.stmts)
    (normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit) (noValue : block.value = none)
    (entry : RuntimePoint cx.cfg cx.fn start initial state) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedLoopBranchBlockPrefix source map required cx results before loop initial start taken reached stop after := by
  exact accepted_generated_invariant_loop_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
    (fun point => RuntimePoint cx.cfg cx.fn point.point point.frame point.state) (fun valid steps => steps.reachable valid)
    entry bodyFamily normal noValue steps stopped nonTimeout

#print axioms accepted_generated_reachable_branch_block_prefix
#print axioms accepted_generated_reachable_loop_branch_block_stopped
end Goose.Lower
