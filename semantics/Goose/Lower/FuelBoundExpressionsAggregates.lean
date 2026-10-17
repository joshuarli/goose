import Goose.Lower.FuelBoundExpressionsLists

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedExprFuelBound_arrLit {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {target : Ty} {expressions : List Expr}
    (children : TypedExprChildrenFuelBound sourceFuel fuel cfg results expressions) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.arrLit target expressions) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq
    resultsEq generated
  let childrenSources : ∀ n, ExprsSource n cfg env expressions state := fun n =>
    Classical.choose (source.arrLitChildren n results metadata)
  have childrenMetadata : ∀ n, (childrenSources n).resultsMatch results := fun n =>
    Classical.choose_spec (source.arrLitChildren n results metadata)
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨ids, middle, childrenRun, definition⟩ := lowering
  have middleExtension : ExtT middle cx.fn.blocks := extension.of_adv (adv_emitDef definition)
  have reflectedChildren := typedExprsFuelBound_of_children expressions children env state childrenSources
    childrenMetadata ls middle ids pt cx fr childrenRun point middleExtension rel moduleEq resultsEq generated
  have composed : FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => mapList (evalExpr n cfg env) expressions >>= fun values => expectArrayLit target values.toArray)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine reflectedChildren.bind ?_
    intro values final pt' fr' childrenDone childrenPost residual residualBound
    obtain ⟨lengthMatch, post⟩ := childrenPost
    have valuesRead := mapList_getVal_cells lengthMatch post.has
    exact leaf_def_fuelBoundAt post definition extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := sourceFuel) (by
        simp only [execPure, valuesRead, pure_bind])
  exact composed.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])

theorem typedExprFuelBound_structLit {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {target : Ty} {expressions : List Expr}
    (children : TypedExprChildrenFuelBound sourceFuel fuel cfg results expressions) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.structLit target expressions) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq
    resultsEq generated
  have typing := source.typed
  simp only [tyExpr] at typing
  inv at typing
  obtain ⟨definitionSource, _, definitionTyping, _⟩ := typing
  obtain ⟨sid, fields, rfl, _⟩ := Core.Sound.structDef_ok _ _ _ _ _ definitionTyping
  let childrenSources : ∀ n, ExprsSource n cfg env expressions state := fun n =>
    Classical.choose (source.structLitChildren n results metadata)
  have childrenMetadata : ∀ n, (childrenSources n).resultsMatch results := fun n =>
    Classical.choose_spec (source.structLitChildren n results metadata)
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨ids, middle, childrenRun, definition⟩ := lowering
  have middleExtension : ExtT middle cx.fn.blocks := extension.of_adv (adv_emitDef definition)
  have reflectedChildren := typedExprsFuelBound_of_children expressions children env state childrenSources
    childrenMetadata ls middle ids pt cx fr childrenRun point middleExtension rel moduleEq resultsEq generated
  have composed : FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => mapList (evalExpr n cfg env) expressions >>= fun values =>
        pure (.record sid values.toArray))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine reflectedChildren.bind ?_
    intro values final pt' fr' childrenDone childrenPost residual residualBound
    obtain ⟨lengthMatch, post⟩ := childrenPost
    have valuesRead := mapList_getVal_cells lengthMatch post.has
    exact leaf_def_fuelBoundAt post definition extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := sourceFuel) (by simp only [execPure, valuesRead, pure_bind])
  exact composed.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])


end Goose.Lower
