import Goose.Lower.FuelBoundExpressionsAccess

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel
open Goose.Core.Sound

theorem lowerExpr_read_var_fuelBoundAt {cfg : Cfg} {env : Env} {cx : FnCtx} {ls after : LS}
    {fr : Frame} {pt : Pt} {resultId varId : Nat} {le : LEnv} {fuel : Nat} {state : St}
    (rel : Rel cfg env cx fr ls) (point : ls.pp = some pt)
    (lowering : lowerExpr (.read (.var varId)) le ls = (resultId, after))
    (extension : ExtT after cx.fn.blocks) :
    FuelBoundAt 2 fuel cx pt fr (fun n => evalExpr n cfg env (.read (.var varId)))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId, .val value)]) state := by
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, readRun⟩ := lowering
  rcases readRun with ⟨value, afterLoad, load, unitResult, afterRecord, record, returned⟩
  cases unitResult
  rw [pure_run] at returned
  rcases Prod.mk.inj returned with ⟨rfl, rfl⟩
  have recordAdvance : afterLoad.Adv afterRecord :=
    advB_recordReadValueRootRecipe value (.var varId) le afterLoad () afterRecord record
  have extensionAfterLoad : ExtT afterLoad cx.fn.blocks := extension.of_adv recordAdvance
  have middleExtension : ExtT middle cx.fn.blocks :=
    extension.of_adv ((adv_emitDef load).trans recordAdvance)
  have first := lowerPlace_var_fuelBoundAt (fuel := fuel) (state := state) rel point placeRun middleExtension
  have composed : FuelBoundAt 1 fuel cx pt fr
      (fun n => evalPlace n cfg env (.var varId) >>= readLoc)
      (fun readValue _ pt' fr' =>
        Post cfg env cx ls fr afterRecord fr' pt' [(value, .val readValue)]) state := by
    refine first.bind ?_
    intro location next pt' fr' done post residual bound
    have cell := post.has (address, .val (.ref location)) (by simp)
    have loadBound : FuelBoundAt 1 residual cx pt' fr'
        (fun _ => readLoc location)
        (fun readValue _ point'' frame'' =>
          Post cfg env cx ls fr afterLoad frame'' point'' [(value, .val readValue)]) next := by
      exact leaf_def_fuelBoundAt post load extensionAfterLoad
        (by intro f args org h; cases h) RVal.val (sourceFuel := 1) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
    exact FuelBoundAt.mono loadBound (by
      intro readValue final point'' frame'' postAfterLoad
      exact Post.recordReadValueRootRecipe postAfterLoad record)
  exact composed.of_source (otherFuel := 2) (by simp only [evalExpr])

theorem typedPlaceFuelBound_deref {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expr) :
    TypedPlaceFuelBound (sourceFuel + 3) fuel cfg results (.deref expr) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  cases hslice : sliceRefTy source.typingEnv expr with
  | none =>
    obtain ⟨childSource, typing, roots, mutability, target, type⟩ := source.derefChild hslice
    have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
      rw [typing, roots]
      exact metadata
    simp only [lowerPlace] at lowering
    have first := child env state childSource childMetadata ls after id pt cx fr lowering
      point extension rel moduleEq resultsEq generated
    have composition : FuelBoundAt sourceFuel fuel cx pt fr
        (fun n => evalExpr n cfg env expr >>= expectRef)
        (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id, .val (.ref location))]) state := by
      refine first.bind ?_
      intro value next pt' fr' done post residual bound
      have typed := (childSource.result sourceFuel value done).typed
      rw [type] at typed
      obtain ⟨location, rfl, _⟩ := typed
      exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := residual) post
    have bounded : FuelBoundAt (sourceFuel + 1) fuel cx pt fr
        (fun n => evalPlace n cfg env (.deref expr))
        (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id, .val (.ref location))]) state :=
      composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalPlace])
    exact bounded.source_mono (fun n k bound => (monoAll n k bound).place cfg env (.deref expr)) (by omega)
  | some ty =>
    obtain ⟨varId, localDecl, mutability, sliceMutability, element, rfl, visible, variableProof,
      type, flat, sameTy⟩ := Core.Sound.sliceRefTy_some hslice
    have future : varId ∈ source.context.inputFuture := by
      cases source.context <;>
        simp [EvaluationContext.inputFuture, NodeContext.inputFuture,
          DemandNode.variables, Place.variables, Expr.variables]
    have sourceReference : ∀ n,
        Core.Sound.Sat (evalExpr n cfg env (.read (.var varId))) state
          (fun value _ => ∃ location, value = .ref location) := by
      intro n
      apply Core.Sound.sat_read_var source.frame visible future n
      intro actual scopeInst value varLookup scopeRun rootRun typed
      rw [source.frame.vars_t, varLookup] at variableProof
      cases variableProof
      rw [type] at typed
      obtain ⟨location, rfl, _⟩ := typed
      exact ⟨location, rfl⟩
    simp only [lowerPlace] at lowering
    have first := (lowerExpr_read_var_fuelBoundAt (fuel := fuel) (state := state) rel point lowering extension).source_mono
      (fun n k bound => (monoAll n k bound).expr cfg env (.read (.var varId)))
      (show 2 ≤ sourceFuel + 2 by omega)
    have composition : FuelBoundAt (sourceFuel + 2) fuel cx pt fr
        (fun n => evalExpr n cfg env (.read (.var varId)) >>= expectRef)
        (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id, .val (.ref location))]) state := by
      refine first.bind ?_
      intro value next pt' fr' done post residual bound
      have known := sourceReference (sourceFuel + 2)
      unfold Core.Sound.Sat at known
      rw [done] at known
      obtain ⟨location, rfl⟩ := known
      exact FuelBoundAt.ret (sourceFuel := sourceFuel + 2) (targetFuel := residual) post
    exact composition.of_source (otherFuel := sourceFuel + 3) (by simp only [evalPlace])

end Goose.Lower
