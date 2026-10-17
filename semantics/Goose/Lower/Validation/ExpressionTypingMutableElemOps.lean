import Goose.Lower.Validation.ExpressionTypingMutableViewOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyPlace_elem_writable_children {env : Core.TEnv} {view : View} {index : Expr} {origin : OriginId}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.elem view index origin) start = .ok (info, finish))
    (writable : info.referenceWritable env.mod.profile = true) :
    ∃ viewStart viewFinish indexFinish intTy,
      Core.tyView env view viewStart = .ok ((info.ty, true), viewFinish) ∧
      Core.tyExpr env index viewFinish = .ok (.int intTy, indexFinish) := by
  simp only [Core.tyPlace] at source
  obtain ⟨_, viewStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨pair, viewFinish, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨indexTy, indexFinish, indexSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨intTy, afterInt, intChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have integer := (requireInt_ok _ _ _ _).mp intChecked
  rw [integer.1] at indexSource
  have result := (st_pure_ok _ _ _).mp source
  have shape := congrArg Prod.fst result
  dsimp only at shape
  have elementShape : info.ty = pair.1 := congrArg PlaceInfo.ty shape
  have permission : pair.2 = true := by
    rw [shape] at writable
    cases pairTy : pair.1 <;> simp_all [PlaceInfo.referenceWritable]
  refine ⟨viewStart, viewFinish, indexFinish, intTy, ?_, indexSource⟩
  have pairShape : pair = (info.ty, true) := Prod.ext elementShape.symm permission
  simpa only [pairShape] using viewSource

theorem lowerPlace_elem_val_writable_typed_of_children {env : Core.TEnv} {expr index : Expr}
    {origin : OriginId} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.elem (.val expr) index origin) start = .ok (info, finish))
    (writable : info.referenceWritable env.mod.profile = true)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace (.elem (.val expr) index origin) (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (exprTyped : ∀ childStart childFinish childState childValue,
      Core.tyExpr env expr childStart = .ok (.slice .mutable info.ty, childFinish) →
      lowerExpr expr (lowerEnv env.mod env.vars results) before = (childValue, childState) →
      childState.cur.isSome = true → childState.vals[childValue]? = some (some (.data (.slice .mutable info.ty))))
    (indexTyped : ∀ childStart childFinish childBefore childState childValue intTy,
      Core.tyExpr env index childStart = .ok (.int intTy, childFinish) →
      lowerExpr index (lowerEnv env.mod env.vars results) childBefore = (childValue, childState) →
      childState.cur.isSome = true → childState.vals[childValue]? = some (some (.data (.int intTy)))) :
    after.vals[value]? = some (some (.data (.ref .mutable info.ty))) := by
  obtain ⟨viewStart, viewFinish, indexFinish, intTy, viewSource, indexSource⟩ :=
    tyPlace_elem_writable_children source writable
  have lowering := run
  simp only [lowerPlace] at lowering
  obtain ⟨viewValue, viewState, viewRun, lowering⟩ := bind_eq.mp lowering
  obtain ⟨indexValue, indexState, indexRun, emitted⟩ := bind_eq.mp lowering
  have indexLive := (dead_emitDef (.indexChecked viewValue indexValue (some origin))).live_before emitted live
  have indexRecorded := indexTyped _ _ _ _ _ _ indexSource indexRun indexLive
  have viewLive := (dead_lowerExpr index).live_before indexRun indexLive
  have viewRecorded := lowerView_val_writable_typed_of_child viewSource viewRun viewLive
    (fun childFinish childState childValue childSource childRun childLive =>
      exprTyped _ _ _ _ childSource childRun childLive)
  cases current : indexState.cur with
  | none => simp [current] at indexLive
  | some block =>
    have typed := lowerPlace_elem_typed_of_children (origin := origin) viewRun viewRecorded indexRun indexRecorded current
    rw [run] at typed
    exact typed.2

#print axioms lowerPlace_elem_val_writable_typed_of_children

end Goose.Lower.Validation
