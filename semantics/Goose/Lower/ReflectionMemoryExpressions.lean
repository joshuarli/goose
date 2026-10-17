import Goose.Lower.ReflectionReferences

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedExprReflection_push {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {owner : Place} {argument : Expr} (origin : Option OriginId)
    (place : TypedPlaceReflection fuel cfg results owner)
    (expression : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results argument) :
    TypedExprReflection fuel cfg results (.push owner argument origin) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨placeSource,placeTyping,placeRoots,nextSource⟩ := source.pushChildren origin
  have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := by
    rw [placeTyping,placeRoots]
    exact metadata
  simp only [lowerExpr,bind_eq] at lowering
  obtain ⟨address,firstLs,placeRun,valueId,middle,argumentRun,definition⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef definition)
  have firstExtension := middleExtension.of_adv (advB_lowerExpr argument _ _ _ _ argumentRun)
  have first := place env state placeSource placeMetadata ls firstLs address pt cx fr placeRun point
    firstExtension rel moduleEq resultsEq generated
  let append := fun location value => do
    let index ← match origin with
      | none => appendLoc location #[value]
      | some origin => checkedAppendLoc location #[value] origin
    pure (Val.ref {location with path := location.path ++ [index]})
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env owner >>= fun location =>
        evalExpr n cfg env argument >>= append location)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env owner) ?_
    · intro n location next pt' fr' placeDone post residual bound
      obtain ⟨argumentSource,argumentTyping,argumentRoots⟩ := nextSource n location next placeDone
      have argumentMetadata : SourceResults argumentSource.typingEnv argumentSource.rootsEnv results := by
        rw [argumentTyping,argumentRoots]
        exact metadata
      have second := expression residual bound env next argumentSource argumentMetadata firstLs middle valueId
        pt' cx fr' argumentRun post.pp middleExtension post.rel moduleEq resultsEq (generated.lowerPlace owner placeRun)
      refine second.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env argument)
        (fun _ _ _ _ => MonoM.refl _)
      intro k value final pt'' fr'' argumentDone post' remaining remainingBound
      have combined := post.comp post'
      have ownerCell := combined.has (address,.val (.ref location)) (by simp)
      have valueCell := combined.has (valueId,.val value) (by simp)
      refine leaf_def_reflectAtFuel combined definition extension (by intro f args org h; cases h)
        RVal.val (sourceFuel := 0) ?_
      cases origin with
      | none => simp [execPure,getVal_of ownerCell,getVal_of valueCell,expectRef]
      | some origin =>
        simp [execPure,getVal_of ownerCell,getVal_of valueCell,expectRef,bind_assoc,pure_bind,
          checkCapacityAtOrg,checkedAppendLoc,checkAppendCapacity,abortAtOrg,abortAt]
        rfl
    · intro location n k bound
      exact ((monoAll n k bound).expr cfg env argument).bind (fun _ => MonoM.refl _)
  refine composition.of_source (fun n => ⟨n + 1,?_⟩)
  simp only [evalExpr,append,bind_apply]
  cases placeRun : evalPlace n cfg env owner state with
  | stop stop after => rfl
  | ok location after =>
    cases expressionRun : evalExpr n cfg env argument after with
    | stop stop final => rfl
    | ok value final => cases origin <;> rfl

theorem typedExprReflection_pop {fuel : Nat} {cfg : Cfg} {results : List Ty} {owner : Place}
    (origin : OriginId) (place : TypedPlaceReflection fuel cfg results owner) :
    TypedExprReflection fuel cfg results (.pop owner origin) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨placeSource,typing,roots⟩ := source.popChild origin
  have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := by
    rw [typing,roots]
    exact metadata
  simp only [lowerExpr,bind_eq] at lowering
  obtain ⟨address,middle,placeRun,definition⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef definition)
  have first := place env state placeSource placeMetadata ls middle address pt cx fr placeRun point
    middleExtension rel moduleEq resultsEq generated
  let pop := fun location => do
    let length ← lengthLoc location
    if length == 0 then abortAt .popEmpty origin
    else do
      let value ← readLoc {location with path := location.path ++ [length - 1]}
      truncateLoc location (length - 1)
      pure value
  have composition : ReflectAtFuel fuel cx pt fr (fun n => evalPlace n cfg env owner >>= pop)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env owner)
      (fun _ _ _ _ => MonoM.refl _)
    intro n location next pt' fr' placeDone post residual bound
    have cell := post.has (address,.val (.ref location)) (by simp)
    refine leaf_def_reflectAtFuel post definition extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    simp [execPure,getVal_of cell,expectRef,abortAtOrg,abortAt]
    funext state
    cases lengthRun : lengthLoc location state with
    | stop err final => simp [bind_apply,lengthRun]
    | ok length middle =>
      by_cases empty : length = 0
      · simp [bind_apply,lengthRun,empty,Functor.map,M.stop,M.bind']
      · simp only [bind_apply,lengthRun,ite_eq_right empty]
        cases readRun : readLoc {root := location.root,path := location.path ++ [length - 1]} middle with
        | stop err final => simp [bind_apply,readRun]
        | ok value afterRead =>
          cases truncateRun : truncateLoc location (length - 1) afterRead with
          | stop err final => simp [bind_apply,readRun]
          | ok _ final => simp [bind_apply,readRun]
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr,pop]⟩)

end Goose.Lower
