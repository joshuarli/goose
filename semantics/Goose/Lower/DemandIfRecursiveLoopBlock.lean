import Goose.Lower.DemandIfRecursiveLoopStatements

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_recursive_loop_branch_block_prefix {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (fragment : RecursiveIfStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
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
    (noValue : block.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedGenericBranchBlockDecomposition source selected map required before loop initial start
      (@RecursiveLoopIfCursor cfg cx results root owner loop (Place._sizeOf_11 block.stmts) { env with scopes := (block.scope, state.nextScope) :: env.scopes } selected)
      taken reached := by
  have bodyFamily : GeneratedSequencePrefixFamily (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes })
      cx results selected before loop [] false block block.stmts
      (@RecursiveLoopIfCursor cfg cx results root owner loop (Place._sizeOf_11 block.stmts) { env with scopes := (block.scope, state.nextScope) :: env.scopes } selected) :=
    (accepted_generated_recursive_loop_if_statements
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) selected loop before [] false block fragment).1
  exact accepted_generated_generic_branch_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended
    _ bodyFamily (fun done => fragment.normal done) noValue steps

theorem accepted_generated_recursive_loop_branch_block_stopped {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
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
    (fragment : RecursiveIfStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    (noValue : block.value = none) {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached)
    {targetFuel : Nat} {stop : Stop} {after : St}
    (stopped : DemandInstructionStop cx targetFuel reached stop after) (nonTimeout : stop ≠ .timeout) :
    StoppedLoopBranchBlockPrefix source map required cx results before loop initial start taken reached stop after := by
  have bodyFamily : GeneratedStoppedSequencePrefixFamily
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) cx results selected before loop [] false block block.stmts :=
    (accepted_generated_recursive_loop_if_statements
      (env := { env with scopes := (block.scope, state.nextScope) :: env.scopes }) selected loop before [] false block fragment).2
  exact accepted_generated_loop_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
    bodyFamily (fun done => fragment.normal done) noValue steps stopped nonTimeout

#print axioms accepted_generated_recursive_loop_branch_block_prefix
#print axioms accepted_generated_recursive_loop_branch_block_stopped
#print axioms accepted_generated_generic_branch_block_prefix
#print axioms accepted_generated_generic_branch_block_stopped
end Goose.Lower
