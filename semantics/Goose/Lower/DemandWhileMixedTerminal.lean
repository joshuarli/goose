import Goose.Lower.DemandBranchTerminal
import Goose.Lower.DemandWhileMixedStatements

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem WhileMixedStatementCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : WhileMixedStatementCursor cx results selected source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor with
  | scalar cursor => exact cursor.excludes_maximal_terminal terminal maximal
  | recursive depth cursor => exact RecursiveIfCursor.excludes_maximal_terminal depth cursor terminal maximal
  | loop cursor => exact cursor.excludes_maximal_terminal terminal maximal

theorem GeneratedSequencePrefixCursor.whileMixed_excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {map required : RetainedSsaMap} {before : LS} {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {initial runtime : DemandRuntimePoint}
    (cursor : GeneratedSequencePrefixCursor (@WhileMixedStatementCursor cfg env cx results root owner selected)
      map required cx results before none bindings block selected source initial runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  apply cursor.excludes_maximal_terminal ?_ terminal maximal
  intro statement state source before built initial start map required runtime cursor term terminal fuel maximal
  exact cursor.excludes_maximal_terminal terminal maximal

#print axioms WhileMixedStatementCursor.excludes_maximal_terminal
#print axioms GeneratedSequencePrefixCursor.whileMixed_excludes_maximal_terminal
end Goose.Lower
