import Goose.Lower.DemandCallLoopMixedSequence
import Goose.Lower.DemandCallLoopBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_scalar_call_loop_body {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (fragment : ReachableScalarCallStatements cfg
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
        (@ReachableScalarCallCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results loop)
        taken reached) ∧
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      ∀ {targetFuel : Nat} {stop : Stop} {after : St},
        DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after → stop ≠ .timeout →
        StoppedLoopBranchBlockPrefix source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop initial start taken reached stop after) := by
  have families := accepted_generated_reachable_scalar_call_statements fragment selected before loop [] false block
  have normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit := by
    intro fuel innerState after flow done
    exact fragment.normal done
  constructor
  · intro taken reached steps
    apply accepted_generated_reachable_branch_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended _
      (fun {state} => families.1 (state := state)) normal noValue entry steps
  · intro taken reached steps targetFuel stop after stopped nonTimeout
    exact accepted_generated_reachable_loop_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
      (fun {state} => families.2 (state := state)) normal noValue entry steps stopped nonTimeout


#print axioms accepted_generated_scalar_call_loop_body
end Goose.Lower
