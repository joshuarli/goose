import Goose.Lower.FuelBoundExpressionsAccess

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel
open Goose.Core.Sound

theorem typedPlaceFuelBound_elem {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {view : View} {index : Expr} (viewChild : TypedViewFuelBound sourceFuel fuel cfg results view)
    (indexChild : ∀ residual, residual ≤ fuel → TypedExprFuelBound sourceFuel residual cfg results index)
    (origin : OriginId) :
    TypedPlaceFuelBound (sourceFuel + 1) fuel cfg results (.elem view index origin) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨intTy, viewSource, viewTyping, viewRoots, next⟩ := source.elemChildren origin
  have viewMetadata : SourceResults viewSource.typingEnv viewSource.rootsEnv results := by
    rw [viewTyping, viewRoots]
    exact metadata
  simp only [lowerPlace, bind_eq] at lowering
  obtain ⟨viewId, firstLs, viewRun, indexId, middle, indexRun, indexChecked⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef indexChecked)
  have firstExtension := middleExtension.of_adv (advB_lowerExpr index _ _ _ _ indexRun)
  have first := viewChild env state viewSource viewMetadata ls firstLs viewId pt cx fr viewRun
    point firstExtension rel moduleEq resultsEq generated
  have middleGenerated := generated.lowerView view viewRun
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalView sourceFuel cfg env view >>= fun sampled =>
        evalExpr sourceFuel cfg env index >>= fun value => do
          let (_,integer) ← expectInt value
          if 0 ≤ integer ∧ integer < (sampled.len : Int) then
            pure (Loc.mk sampled.loc.root (sampled.loc.path ++ [sampled.start + integer.toNat]))
          else abortAt .indexOob origin)
      (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state := by
    refine first.bind ?_
    intro sampled sampledAfter pt' fr' viewDone post residual bound
    obtain ⟨indexSource,indexTyping,indexRoots,indexType⟩ := next sourceFuel sampled sampledAfter viewDone
    have indexMetadata : SourceResults indexSource.typingEnv indexSource.rootsEnv results := by
      rw [indexTyping, indexRoots]
      exact metadata
    have second := (indexChild residual bound) env sampledAfter indexSource indexMetadata
      firstLs middle indexId pt' cx fr' indexRun post.pp middleExtension post.rel
      moduleEq resultsEq middleGenerated
    have secondComposition : FuelBoundAt sourceFuel residual cx pt' fr'
        (fun sourceFuel => evalExpr sourceFuel cfg env index >>= fun value => do
          let (_,integer) ← expectInt value
          if 0 ≤ integer ∧ integer < (sampled.len : Int) then
            pure (Loc.mk sampled.loc.root (sampled.loc.path ++ [sampled.start + integer.toNat]))
          else abortAt .indexOob origin)
        (fun location _ pt'' fr'' =>
          Post cfg env cx ls fr after fr'' pt'' [(id,.val (.ref location))]) sampledAfter := by
      refine second.bind ?_
      intro value final pt'' fr'' indexDone postIndex remaining remainingBound
      have indexTyped := (indexSource.result sourceFuel value indexDone).typed
      rw [indexType] at indexTyped
      obtain ⟨integer,rfl⟩ := Core.Sound.hasTy_int indexTyped
      have combined := post.comp postIndex
      have sampledCell := combined.has (viewId,.view sampled) (by simp)
      have indexCell := combined.has (indexId,.val (.int intTy integer)) (by simp)
      refine leaf_def_fuelBoundAt combined indexChecked extension
        (by intro f args org h; cases h) (fun location => RVal.val (.ref location))
        (sourceFuel := sourceFuel) ?_
      simp only [execPure, getView_of sampledCell, getVal_of indexCell, Core.expectInt,
        pure_bind]
      by_cases inBounds : 0 ≤ integer ∧ integer < (sampled.len : Int)
      · simp [inBounds]
      · simp [inBounds, abortAtOrg, abortAt]
        rfl
    exact secondComposition
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalPlace])


theorem typedExprFuelBound_slice {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {view : View} {low high : Bound} {mutability : Mutability} {origin : OriginId}
    (viewChild : TypedViewFuelBound sourceFuel fuel cfg results view)
    (lowChild : ∀ residual, residual ≤ fuel → TypedBoundFuelBound sourceFuel residual cfg results low)
    (highChild : ∀ residual, residual ≤ fuel → TypedBoundFuelBound sourceFuel residual cfg results high) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.slice mutability view low high origin) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨viewSource, viewTyping, viewRoots, next⟩ := source.sliceChildren mutability origin
  have viewMetadata : SourceResults viewSource.typingEnv viewSource.rootsEnv results := by
    rw [viewTyping, viewRoots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨viewId, first, viewRun, lowBnd, second, lowRun, highBnd, third, highRun, definition⟩ := lowering
  have thirdExtension := extension.of_adv (adv_emitDef definition)
  have secondExtension := thirdExtension.of_adv (advB_lowerBound high _ _ _ _ highRun)
  have firstExtension := secondExtension.of_adv (advB_lowerBound low _ _ _ _ lowRun)
  have viewReflection := viewChild env state viewSource viewMetadata ls first viewId pt cx fr viewRun
    point firstExtension rel moduleEq resultsEq generated
  have firstGenerated := generated.lowerView view viewRun
  let sliceFinish : ViewVal → Int → Int → M Val := fun sampled lower upper =>
    if 0 ≤ lower ∧ lower ≤ upper ∧ upper ≤ (sampled.len : Int) then
      pure (.slice sampled.loc (sampled.start + lower.toNat) (upper - lower).toNat)
    else abortAt .sliceOob origin
  let sliceBounds : ViewVal → Nat → M Val := fun sampled sourceFuel => do
    let lower ← evalBound sourceFuel cfg env sampled.len 0 low
    let upper ← evalBound sourceFuel cfg env sampled.len sampled.len high
    sliceFinish sampled lower upper
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalView sourceFuel cfg env view >>= fun sampled => sliceBounds sampled sourceFuel)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine viewReflection.bind ?_
    intro sampled nextState pt' fr' viewDone viewPost residual residualBound
    obtain ⟨lowerSource, lowerTyping, lowerRoots, upperSources⟩ :=
      next sourceFuel sampled nextState viewDone
    have lowerMetadata : SourceResults lowerSource.typingEnv lowerSource.rootsEnv results := by
      rw [lowerTyping, lowerRoots]
      exact metadata
    have firstBounds := (lowChild residual residualBound) env nextState lowerSource lowerMetadata
      first second lowBnd pt' cx fr' sampled.len 0 lowRun viewPost.pp secondExtension
      viewPost.rel moduleEq resultsEq firstGenerated
    have boundsComposition : FuelBoundAt sourceFuel residual cx pt' fr'
        (fun sourceFuel => evalBound sourceFuel cfg env sampled.len 0 low >>= fun lower =>
          evalBound sourceFuel cfg env sampled.len sampled.len high >>= fun upper =>
            sliceFinish sampled lower upper)
        (fun value _ pt'' fr'' =>
          Post cfg env cx ls fr after fr'' pt'' [(resultId,.val value)]) nextState := by
      refine firstBounds.bind ?_
      intro lower lowerAfter pt'' fr'' lowerDone lowerPost remaining remainingBound
      obtain ⟨upperSource, upperTyping, upperRoots⟩ :=
        upperSources sourceFuel lower lowerAfter lowerDone
      obtain ⟨lowCells, lowSpec, lowPostState⟩ := lowerPost
      have upperMetadata : SourceResults upperSource.typingEnv upperSource.rootsEnv results := by
        rw [upperTyping, upperRoots]
        exact metadata
      have secondGenerated := firstGenerated.lowerBound low lowRun
      have secondBounds := (highChild remaining (Nat.le_trans remainingBound residualBound))
        env lowerAfter upperSource upperMetadata second third highBnd pt'' cx fr'' sampled.len
        sampled.len highRun lowPostState.pp thirdExtension lowPostState.rel moduleEq resultsEq
        secondGenerated
      refine secondBounds.bind ?_
      intro upper final pt''' fr''' upperDone ⟨highCells, highSpec, highPost⟩ remaining' remainingBound'
      have combined := (viewPost.comp lowPostState).comp highPost
      have sampledCell := combined.has (viewId,.view sampled) (by simp)
      have lowCell : ∀ cell ∈ lowCells, fr'''.vals[cell.1]? = some cell.2 := by
        intro cell member
        exact combined.has cell (by simp [member])
      have highCell : ∀ cell ∈ highCells, fr'''.vals[cell.1]? = some cell.2 := by
        intro cell member
        exact combined.has cell (by simp [member])
      have lowerEval := evalBnd_of_spec lowSpec lowCell
      have upperEval := evalBnd_of_spec highSpec highCell
      exact leaf_def_fuelBoundAt combined definition extension
        (by intro f args org h; cases h) RVal.val (sourceFuel := sourceFuel) (by
          simp only [execPure, getView_of sampledCell, lowerEval, upperEval,
            sliceFinish, pure_bind]
          by_cases inBounds : 0 ≤ lower ∧ lower ≤ upper ∧ upper ≤ (sampled.len : Int)
          · simp [inBounds]
          · simp [inBounds, abortAtOrg, abortAt]
            rfl)
    exact boundsComposition
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr, sliceBounds, sliceFinish])


end Goose.Lower
