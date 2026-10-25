import Goose.Lower.Validation.ViewTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem joinLive_typed {le : LEnv} {before : LS} {live : List (BlockId × ValueId)} {ty : VTy}
    (typed : before.vals[(live.headD (0, 0)).2]? = some (some ty)) :
    let action : B ValueId := do
      let valueTy ← valTy (live.headD (0, 0)).2
      let (join, params) ← newBlock [valueTy]
      patchBrs join live
      setCur (some join)
      pure (params.headD 0)
    let (value, after) := action le before
    after.vals[value]? = some (some ty) := by
  simp only [bind_run, valTy_of_recorded typed, newBlock1_run]
  let initial : LS :=
    { before with
      blocks := before.blocks.push ⟨[(before.vals.size, ty)], #[]⟩
      vals := before.vals.push (some ty) }
  cases patched : patchBrs before.blocks.size live le initial with
  | mk patchedResult middle =>
    have fresh : initial.vals[before.vals.size]? = some (some ty) := by simp [initial]
    have retained := types_patchBrs before.blocks.size live le initial patchedResult middle patched
      before.vals.size ty fresh
    simpa only [setCur_run, pure_run, List.headD_cons] using retained

theorem joinValue_typed {le : LEnv} {before : LS} {endT endF : Option BlockId}
    {valueT valueF : ValueId} {ty : VTy}
    (thenTyped : endT.isSome = true → before.vals[valueT]? = some (some ty))
    (elseTyped : endF.isSome = true → before.vals[valueF]? = some (some ty)) :
    let (value, after) := joinValue endT valueT endF valueF le before
    after.cur.isSome = true → after.vals[value]? = some (some ty) := by
  cases endT with
  | none =>
    cases endF with
    | none => simp [joinValue, bind_run, setCur_run, pure_run]
    | some elseBlock =>
      have typed := elseTyped rfl
      intro live
      exact joinLive_typed (live := [(elseBlock, valueF)]) typed
  | some thenBlock =>
    have typed := thenTyped rfl
    cases endF with
    | none =>
      intro live
      exact joinLive_typed (live := [(thenBlock, valueT)]) typed
    | some elseBlock =>
      intro live
      exact joinLive_typed (live := [(thenBlock, valueT), (elseBlock, valueF)]) typed

theorem shortCircuit_result_typed {le : LEnv} {before after : LS} {isAnd : Bool}
    {value result : ValueId} {rhs : B ValueId} (preserved : TypeRun rhs)
    (run : shortCircuit isAnd value rhs le before = (result, after))
    (live : after.cur.isSome = true) : after.vals[result]? = some (some (.data .bool)) := by
  cases current : before.cur with
  | none =>
    rw [shortCircuit, whenLive_none _ _ le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    simp [current] at live
  | some block =>
    rw [shortCircuit, whenLive_some _ _ le current] at run
    obtain ⟨pair, forked, forkRun, run⟩ := bind_eq.mp run
    obtain ⟨_, started, startRun, run⟩ := bind_eq.mp run
    obtain ⟨_, childAfter, childRun, run⟩ := bind_eq.mp run
    obtain ⟨_, closed, closeRun, run⟩ := bind_eq.mp run
    obtain ⟨_, joined, joinRun, run⟩ := bind_eq.mp run
    obtain ⟨valueEqual, stateEqual⟩ := pure_eq.mp run
    have forkTyped : forked.vals[pair.2.2]? = some (some (.data .bool)) := by
      rw [scFork_run _ _ le current] at forkRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj forkRun
      simp
    have startedType := types_setCur _ le forked _ started startRun pair.2.2 (.data .bool) forkTyped
    have childType := preserved le started _ childAfter childRun pair.2.2 (.data .bool) startedType
    have closedType := types_emitTerm _ le childAfter _ closed closeRun pair.2.2 (.data .bool) childType
    have joinedType := types_setCur _ le closed _ joined joinRun pair.2.2 (.data .bool) closedType
    rw [← stateEqual, ← valueEqual]
    exact joinedType

theorem lowerExpr_and_result_typed (left right : Expr) (le : LEnv) (before : LS) :
    let (value, after) := lowerExpr (.and left right) le before
    after.cur.isSome = true → after.vals[value]? = some (some (.data .bool)) := by
  cases leftRun : lowerExpr left le before with
  | mk leftValue middle =>
    simp only [lowerExpr, bind_run, leftRun]
    intro live
    exact shortCircuit_result_typed (types_lowerExpr right) rfl live

theorem lowerExpr_or_result_typed (left right : Expr) (le : LEnv) (before : LS) :
    let (value, after) := lowerExpr (.or left right) le before
    after.cur.isSome = true → after.vals[value]? = some (some (.data .bool)) := by
  cases leftRun : lowerExpr left le before with
  | mk leftValue middle =>
    simp only [lowerExpr, bind_run, leftRun]
    intro live
    exact shortCircuit_result_typed (types_lowerExpr right) rfl live

end Goose.Lower.Validation
