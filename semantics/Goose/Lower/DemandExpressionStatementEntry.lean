import Goose.Lower.DemandGeneratedExpressionPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_expression_statement_entry {cfg : Cfg} {env : Env} {expression : Expr} {origin : OriginId} {state : St}
    (source : StmtSource cfg env (.expr expression origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.expr expression origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.expr expression origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ child : ExprSource cfg env expression state,
      child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧ source.ExpressionChildAt child rfl ∧
      ∃ childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root child.path (.expression expression) before,
        GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required ∧
        GeneratedSourceOwner selected child.context ∧ map.Admitted cfg.mod.profile child.context.retained ∧
        map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ ∧
        GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv before initial start ∧
        ExtT (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks ∧
        (lowerStmt loop (.expr expression origin) (lowerEnv cfg.mod env.vars results) before).2 =
          (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 := by
  obtain ⟨child, typing, roots, canonical⟩ := source.exprChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression expression) before := by
    rw [canonical.path]
    exact .first occurrence (.discard loop expression origin)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.discard loop expression origin)) required := .first (first := .discard loop expression origin) rows
    simpa only [roots, canonical.path] using inherited
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 0 (.expression expression) .expression rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have childAdmitted : map.Admitted cfg.mod.profile child.context.retained := by
    rw [demandContextRetainedEq canonical.plans canonical.path rfl canonical.context]
    intro profile alias member
    exact source.context.child_retained_subset rfl 0 (.expression expression) .expression rfl (by trivial)
      (admitted profile alias member)
  have childRealized : map.Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  have childInput : GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv before initial start := by
    rw [typing, roots]
    exact input
  have lowered : (lowerStmt loop (.expr expression origin) (lowerEnv cfg.mod env.vars results) before).2 =
      (lowerExpr expression (lowerEnv cfg.mod env.vars results) before).2 := by
    simp only [lowerStmt, bind_run, pure_run]
  have childExtended := extended
  rw [lowered] at childExtended
  exact ⟨child, typing, roots, canonical, childOccurrence, childRows, childOwner, childAdmitted, childRealized, childInput, childExtended, lowered⟩

#print axioms accepted_generated_expression_statement_entry
end Goose.Lower
