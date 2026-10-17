import Goose.Lower.Validation.ExpressionTypingFreshContents
import Goose.Lower.Validation.ExpressionTypingBorrowOps

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem FreshContentsEvidence.borrowTo_mutable {le : LEnv} {before after : LS}
    {owner value : ValueId} {target : Ty} {first : Nat} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (typed : before.vals[owner]? = some (some (.data (.ref .mutable target))))
    (checked : before.DenseDefinitions) (bounded : LiveBound before) (live : before.cur = some current)
    (run : borrowTo .mutable owner le before = (value, after)) :
    FreshContentsEvidence le first after value := by
  rcases borrowTo_cases run with frozen | borrowed
  · have unchanged : freezeTo .mutable owner le before = (owner, before) := by
      simp only [freezeTo, bind_run, valTy_of_recorded typed, pure_run]
    rw [unchanged] at frozen
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj frozen
    exact evidence
  · apply evidence.emitDef_dependency checked bounded live borrowed
    intro authorized allowed
    exact allowed

#print axioms FreshContentsEvidence.borrowTo_mutable

end Goose.Lower.Validation
