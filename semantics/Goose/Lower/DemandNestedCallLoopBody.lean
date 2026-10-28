import Goose.Lower.DemandNestedCallLoopSequence
import Goose.Lower.DemandCallLoopBody
import Goose.Lower.DemandBranchTerminal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_nested_call_loop_body {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    (source : BlockSource cfg env [] block state)
    (condition : Expr) (body : Core.Block) (origin : OriginId) (conditionForm : ControlPrefixExpression condition)
    {later : List Stmt} (statements : block.stmts = .while condition body origin :: later)
    (fragment : ∀ middle : St, ReachableScalarCallStatements cfg
      { env with scopes := (body.scope, middle.nextScope) :: (block.scope, state.nextScope) :: env.scopes } body.stmts)
    (bodyNoValue : body.value = none)
    (tail : ReachableScalarCallStatements cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } later)
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
        (@ReachableNestedCallLoopCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results loop root owner selected)
        taken reached) ∧
    (∀ {taken : Nat} {reached : DemandRuntimePoint},
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ taken ⟨start, initial, state⟩ reached →
      ∀ {targetFuel : Nat} {stop : Stop} {after : St},
        DemandInstructionStop ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ targetFuel reached stop after → stop ≠ .timeout →
        StoppedLoopBranchBlockPrefix source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop initial start taken reached stop after) := by
  have families := accepted_generated_reachable_nested_call_loop_sequence condition body origin conditionForm fragment bodyNoValue tail selected before loop [] false block
  have normal : ∀ {fuel : Nat} {innerState after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } block.stmts innerState = .ok flow after →
      flow = .normal .unit := by
    intro fuel innerState after flow done
    rw [statements] at done
    exact nested_call_loop_sequence_normal fragment bodyNoValue tail done
  constructor
  · intro taken reached steps
    apply accepted_generated_reachable_branch_block_prefix source selected owned occurrence rows coverage admitted bounded realized input extended _
      (by rw [statements]; exact fun {state} => families.1 (state := state)) normal noValue entry steps
  · intro taken reached steps targetFuel stop after stopped nonTimeout
    exact accepted_generated_reachable_loop_branch_block_stopped source selected owned occurrence rows coverage admitted bounded realized input extended
      (by rw [statements]; exact fun {state} => families.2 (state := state)) normal noValue entry steps stopped nonTimeout


theorem GeneratedGenericBlockPrefixDemand.nestedCall_excludes_maximal_terminal
    {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {runtime : DemandRuntimePoint}
    (demanded : GeneratedGenericBlockPrefixDemand (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) source selected map required before loop initial
      (@ReachableNestedCallLoopCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results loop root owner selected)
      (GeneratedBranchBlockEffectDemand source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop initial) runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  apply demanded.excludes_maximal_terminal ?_ terminal maximal
  intro statement innerState child before built initial start map required runtime cursor term terminal fuel maximal
  exact cursor.excludes_maximal_terminal terminal maximal

#print axioms GeneratedGenericBlockPrefixDemand.nestedCall_excludes_maximal_terminal

#print axioms accepted_generated_nested_call_loop_body
end Goose.Lower
