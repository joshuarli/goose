import Goose.Lower.DemandCallLoopMixedBody
import Goose.Lower.DemandCallLoopTerminal
import Goose.Lower.DemandBranchTerminal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem ReachableScalarCallCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {caller : Func} {results : List Ty} {loop : Option LoopCtx} {before built : LS} {initial : GIR.Frame} {start : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ReachableScalarCallCursor caller results loop source before built initial start map required runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  cases cursor with
  | scalar cursor => exact ScalarAssignmentStatementPrefixCursor.excludes_maximal_terminal cursor terminal maximal
  | call cursor => exact cursor.excludes_maximal_terminal terminal maximal
  | conditional selected cursor =>
    cases cursor with
    | scalar cursor => exact ScalarAssignmentStatementPrefixCursor.excludes_maximal_terminal cursor terminal maximal
    | recursive depth cursor => exact RecursiveLoopIfCursor.excludes_maximal_terminal depth cursor terminal maximal

theorem GeneratedGenericBlockPrefixDemand.scalarCall_excludes_maximal_terminal
    {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {runtime : DemandRuntimePoint}
    (demanded : GeneratedGenericBlockPrefixDemand (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) source selected map required before loop initial
      (@ReachableScalarCallCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results loop)
      (GeneratedBranchBlockEffectDemand source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop initial) runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  apply demanded.excludes_maximal_terminal ?_ terminal maximal
  intro statement innerState child before built initial start map required runtime cursor term terminal fuel maximal
  exact cursor.excludes_maximal_terminal terminal maximal

#print axioms ReachableScalarCallCursor.excludes_maximal_terminal
#print axioms GeneratedGenericBlockPrefixDemand.scalarCall_excludes_maximal_terminal
end Goose.Lower
