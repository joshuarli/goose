import Goose.Lower.DemandNestedCallLoopFamilies
import Goose.Lower.DemandNestedCallLoopBoundedBody
import Goose.Lower.DemandCallLoopBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_recursive_nested_call_loop_body {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (fragment : NestedCallLoopStatements cfg
      { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts)
    (noValue : block.value = none)
    {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod caller (lowerEnv cfg.mod env.vars results)
      root source.path (.block loop [] false block) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerBlock loop [] false block (lowerEnv cfg.mod env.vars results) before).2 caller.blocks)
    (entry : RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller start initial state) :
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      GeneratedGenericBranchBlockDecomposition source (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) (results := results) selected map required before loop initial start
        (@NestedCallLoopCursor cfg caller results root owner (Place._sizeOf_11 block.stmts) { env with scopes := (block.scope, state.nextScope) :: env.scopes } loop selected)
        taken reached) ∧
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      ∀ {targetFuel : Nat} {stop : Stop} {after : St},
        DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after → stop ≠ .timeout →
        StoppedLoopBranchBlockPrefix source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop initial start taken reached stop after) := by
  exact accepted_generated_bounded_nested_call_loop_body source fragment.bounded noValue selected
    (accepted_generated_bounded_nested_call_loop_statements fragment.bounded selected before loop [] false block)
    owned occurrence rows coverage admitted bounded realized input extended entry


theorem GeneratedGenericBlockPrefixDemand.recursiveNestedCall_excludes_maximal_terminal
    {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {runtime : DemandRuntimePoint}
    (demanded : GeneratedGenericBlockPrefixDemand (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) source selected map required before loop initial
      (@NestedCallLoopCursor cfg caller results root owner (Place._sizeOf_11 block.stmts)
        { env with scopes := (block.scope, state.nextScope) :: env.scopes } loop selected)
      (GeneratedBranchBlockEffectDemand source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop initial) runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  apply demanded.excludes_maximal_terminal ?_ terminal maximal
  intro statement innerState child before built initial start map required runtime cursor term terminal fuel maximal
  exact NestedCallLoopCursor.excludes_maximal_terminal (Place._sizeOf_11 block.stmts) cursor terminal maximal

#print axioms GeneratedGenericBlockPrefixDemand.recursiveNestedCall_excludes_maximal_terminal

#print axioms accepted_generated_recursive_nested_call_loop_body
end Goose.Lower
