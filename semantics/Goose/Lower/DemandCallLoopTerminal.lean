import Goose.Lower.DemandCallLoopBody
import Goose.Lower.DemandBranchTerminal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem ReachableCallStatementFamilyCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {caller : Func} {results : List Ty} {loop : Option LoopCtx} {before built : LS} {initial : GIR.Frame} {start : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ReachableCallStatementFamilyCursor caller results loop source before built initial start map required runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  rcases cursor.progress with ⟨id, op, instruction⟩ | ⟨next, step⟩
  · cases instruction.symm.trans terminal
  · exact maximal next (step fuel)

theorem GeneratedGenericBlockPrefixDemand.call_excludes_maximal_terminal
    {cfg : Cfg} {env : Env} {block : Core.Block} {state : St}
    {source : BlockSource cfg env [] block state} {caller : Func} {results : List Ty} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {runtime : DemandRuntimePoint}
    (demanded : GeneratedGenericBlockPrefixDemand (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩) source selected map required before loop initial
      (@ReachableCallStatementFamilyCursor cfg { env with scopes := (block.scope, state.nextScope) :: env.scopes } caller results loop)
      (GeneratedBranchBlockEffectDemand source map required ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results before loop initial) runtime)
    {term : Term} (terminal : instAt caller runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ fuel runtime next) : False := by
  apply demanded.excludes_maximal_terminal ?_ terminal maximal
  intro statement innerState child before built initial start map required runtime cursor term terminal fuel maximal
  exact cursor.excludes_maximal_terminal terminal maximal

#print axioms ReachableCallStatementFamilyCursor.excludes_maximal_terminal
#print axioms GeneratedGenericBlockPrefixDemand.call_excludes_maximal_terminal
end Goose.Lower
