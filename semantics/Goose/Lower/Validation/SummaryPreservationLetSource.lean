import Goose.Lower.Validation.SummaryPreservationRebindSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_reference_let_contract {env : PEnv} {varId : VarId} {expression : Expr}
    {org : OriginId} {localVar : LocalVar} {roots : List RootRef}
    {initial before after : RState}
    (variableRow : env.impl.vars[varId]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (operand : rpExpr env expression { initial with nextVar := initial.nextVar + 1 } = .ok (roots, before))
    (source : rpStmt env (.letS varId expression org) initial = .ok ((), after)) :
    bindRootsV env env.scopes varId roots = .ok () ∧ after = before := by
  simp only [rpStmt] at source
  inv at source
  obtain ⟨_, returned, middle, replay, tail⟩ := source
  rw [operand] at replay
  cases replay
  simp only [variableRow, reference, ite_true] at tail
  inv at tail
  exact tail

end Goose.Lower.Validation.SummaryPreservation
