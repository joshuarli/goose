import Goose.Lower.DemandWhileRecursiveBody

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_while_reentry_context {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {state after : St}
    (source : StmtSource cfg env (.while condition body origin) state)
    (next : StmtSource cfg env (.while condition body origin) after)
    (roots : next.rootsEnv = source.rootsEnv) (plans : next.plans = source.plans)
    (path : next.path = source.path) (context : HEq next.context source.context)
    {cx : FnCtx} {results : List Ty} {loop : Option LoopCtx} {root : DemandNode} {owner : Nat} {before : LS}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.while condition body origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) :
    GeneratedSourceOwner selected next.context ∧ map.Admitted cfg.mod.profile next.context.retained ∧
    ∃ nextOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root next.path (.statement loop (.while condition body origin)) before,
      GeneratedDemandRows cfg.mod next.rootsEnv.access nextOccurrence required := by
  have nextOwned := owned.transport plans.symm path.symm rfl context.symm
  have nextAdmitted : map.Admitted cfg.mod.profile next.context.retained := by
    rw [demandContextRetainedEq plans path rfl context]
    exact admitted
  have nextRows : ∃ nextOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root next.path (.statement loop (.while condition body origin)) before,
      GeneratedDemandRows cfg.mod next.rootsEnv.access nextOccurrence required := by
    rw [path, roots]
    exact ⟨occurrence, rows⟩
  exact ⟨nextOwned, nextAdmitted, nextRows⟩

#print axioms generated_while_reentry_context
end Goose.Lower
