import Goose.Lower.Validation.CfgSourceDominanceFork

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SSAResult.close_join {before child : LS} {beforeImports childImports : ImportedValues}
    {childValues : List ValueId} (result : SSAResult before child beforeImports childImports childValues)
    (beforeBound : LiveBound before) (beforeLive : before.cur.isSome = true)
    {join : BlockId} (joinBound : join < child.blocks.size) (joinFresh : before.blocks.size ≤ join)
    {body : BlockB} (joinRow : child.blocks[join]? = some body) (joinOpen : OpenBlock body)
    (notCurrent : child.cur ≠ some join)
    (joinImports : childImports join = currentValues before beforeImports)
    (arguments : List ValueId) (available : AvailableValues child childImports arguments) (env : LEnv) :
    let action : B Unit := do
      emitTerm (.br join arguments)
      setCur (some join)
    SSAResult before (action env child).2 beforeImports childImports [] := by
  dsimp only
  let closed := (emitTerm (.br join arguments) env child).2
  have values := result.frame _ (currentValues_available beforeBound)
  have closedChecked := result.checked.emitTerm (.br join arguments) env available
    (by
      intro target member
      have same : target = join := by simpa [Term.successors] using member
      exact same.symm ▸ joinBound)
    (by
      intro target member
      have same : target = join := by simpa [Term.successors] using member
      subst target
      simpa only [joinImports] using values)
  have closing := advB_emitTerm (.br join arguments) env child _ _ rfl
  have closedRow := closing.keep join body notCurrent joinRow
  have selected := SSAResult.select_imports closedChecked (result.advance.trans closing)
    result.imports beforeLive (Nat.lt_of_lt_of_le joinBound closing.ext.1) joinFresh
    ⟨body, closedRow, joinOpen⟩ joinImports env
  exact selected

end Goose.Lower.Validation
