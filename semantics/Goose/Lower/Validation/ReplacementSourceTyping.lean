import Goose.Lower.Validation.ReplacementSource
import Goose.Lower.Validation.SourceStatementTypingStorage

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem tyStmt_assignWhole_fresh {env output : TEnv} {owner : Place} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole owner expr origin) start = .ok (output, finish)) :
    expr.freshOwner = true := by
  have profile := tyStmt_assignWhole_profile source
  simp only [Core.tyStmt] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨info, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨type, binding, contents⟩ := info
  cases type <;> simp only at source
  all_goals try { inv at source }
  all_goals
    rename_i element
    obtain ⟨childType, childFinish, child, source⟩ := (st_bind_ok _ _ _ _).mp source
    inv at source
    simp only [beq_iff_eq] at source
    obtain ⟨childTypeEq, ownerFinish, ownerRun, writable, outputEq, finishEq⟩ := source
    exact checkOwnerRun_fresh ownerRun profile rfl

end Goose.Lower.Validation
