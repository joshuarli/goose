import Goose.Lower.FuelBoundTyped
import Goose.Lower.ReflectionReferences

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel
open Goose.Core.Sound

theorem typedPlaceFuelBound_var (fuel : Nat) (cfg : Cfg) (results : List Ty) (id : VarId) :
    TypedPlaceFuelBound 1 fuel cfg results (.var id) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact lowerPlace_var_fuelBoundAt rel point lowering extension

theorem typedPlaceFuelBound_global (fuel : Nat) (cfg : Cfg) (results : List Ty) (id : GlobalId) :
    TypedPlaceFuelBound 1 fuel cfg results (.global id) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact lowerPlace_global_fuelBoundAt rel point lowering extension

theorem typedBoundFuelBound_omitted (fuel : Nat) (cfg : Cfg) (results : List Ty) :
    TypedBoundFuelBound 1 fuel cfg results .omitted := by
  intro env state source metadata ls after bnd pt cx fr length default lowering point extension rel moduleEq resultsEq generated
  simp only [lowerBound, pure_run] at lowering
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj lowering
  have matched : ∃ cells, BndSpec length default Bnd.omitted default cells ∧
      Post cfg env cx ls fr ls fr pt cells := by
    refine ⟨[], ?_, Post.init rel point⟩
    simp [BndSpec]
  exact (FuelBoundAt.ret (sourceFuel := 0) (targetFuel := fuel) matched).of_source
    (otherFuel := 1) (by simp [evalBound])

theorem typedExprFuelBound_read {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (child : TypedPlaceFuelBound sourceFuel fuel cfg results place) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.read place) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨placeSource, typing, roots, _⟩ := source.readChild
  have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, readRun⟩ := lowering
  rcases readRun with ⟨value, afterLoad, load, unitResult, afterRecord, record, returned⟩
  cases unitResult
  rw [pure_run] at returned
  rcases Prod.mk.inj returned with ⟨rfl, rfl⟩
  have recordAdvance : afterLoad.Adv afterRecord :=
    advB_recordReadValueRootRecipe value place (lowerEnv cfg.mod env.vars results)
      afterLoad () afterRecord record
  have extensionAfterLoad : ExtT afterLoad cx.fn.blocks := extension.of_adv recordAdvance
  have middleExtension : ExtT middle cx.fn.blocks :=
    extension.of_adv ((adv_emitDef load).trans recordAdvance)
  have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun point
    middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalPlace sourceFuel cfg env place >>= readLoc)
      (fun readValue _ pt' fr' =>
        Post cfg env cx ls fr afterRecord fr' pt' [(value,.val readValue)]) state := by
    refine first.bind ?_
    intro location next pt' fr' done post residual bound
    have cell := post.has (address,.val (.ref location)) (by simp)
    have loadBound : FuelBoundAt sourceFuel residual cx pt' fr'
        (fun _ => readLoc location)
        (fun readValue _ point'' frame'' =>
          Post cfg env cx ls fr afterLoad frame'' point'' [(value,.val readValue)]) next := by
      exact leaf_def_fuelBoundAt post load extensionAfterLoad
        (by intro f args org h; cases h) RVal.val (sourceFuel := sourceFuel) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
    exact FuelBoundAt.mono loadBound (by
      intro readValue final point'' frame'' postAfterLoad
      exact Post.recordReadValueRootRecipe postAfterLoad record)
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])


theorem typedExprFuelBound_ref {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (mutability : Mutability) (child : TypedPlaceFuelBound sourceFuel fuel cfg results place) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.ref mutability place) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨placeSource, typing, roots⟩ := source.refChild mutability
  have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, freeze⟩ := lowering
  rcases borrowTo_ref_cases freeze with ⟨rfl,rfl⟩ | definition | definition
  · have first := child env state placeSource placeMetadata ls after resultId pt cx fr placeRun
      point extension rel moduleEq resultsEq generated
    have composition : FuelBoundAt sourceFuel fuel cx pt fr
        (fun sourceFuel => evalPlace sourceFuel cfg env place >>= fun location => pure (.ref location))
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
      refine first.bind ?_
      intro location next pt' fr' done post residual bound
      exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := residual) post
    exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])
  · have middleExtension := extension.of_adv (adv_emitDef definition)
    have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun
      point middleExtension rel moduleEq resultsEq generated
    have composition : FuelBoundAt sourceFuel fuel cx pt fr
        (fun sourceFuel => evalPlace sourceFuel cfg env place >>= fun location => pure (.ref location))
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
      refine first.bind ?_
      intro location next pt' fr' done post residual bound
      have cell := post.has (address,.val (.ref location)) (by simp)
      exact leaf_def_fuelBoundAt post definition extension (by intro f args org h; cases h)
        RVal.val (sourceFuel := sourceFuel) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
    exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])

  · have middleExtension := extension.of_adv (adv_emitDef definition)
    have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun
      point middleExtension rel moduleEq resultsEq generated
    have composition : FuelBoundAt sourceFuel fuel cx pt fr
        (fun sourceFuel => evalPlace sourceFuel cfg env place >>= fun location => pure (.ref location))
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
      refine first.bind ?_
      intro location next pt' fr' done post residual bound
      have cell := post.has (address,.val (.ref location)) (by simp)
      exact leaf_def_fuelBoundAt post definition extension (by intro f args org h; cases h)
        RVal.val (sourceFuel := sourceFuel) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
    exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])


theorem typedExprFuelBound_len {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {view : View}
    (child : TypedViewFuelBound sourceFuel fuel cfg results view) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.len view) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨viewSource, typing, roots, _, _⟩ := source.lenChild
  have viewMetadata : SourceResults viewSource.typingEnv viewSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨viewId, middle, viewRun, definition⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef definition)
  have first := child env state viewSource viewMetadata ls middle viewId pt cx fr viewRun point
    middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalView sourceFuel cfg env view >>= fun value => pure (.int .i64 value.len))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_
    intro value next pt' fr' done post residual bound
    have cell := post.has (viewId,.view value) (by simp)
    exact leaf_def_fuelBoundAt post definition extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := sourceFuel) (by simp only [execPure, getView_of cell, pure_bind])
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])


theorem typedArgFuelBound_byVal {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedArgFuelBound (sourceFuel + 1) fuel cfg results (.byVal expression) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  cases source with
  | byVal expressionSource =>
    simp only [lowerArg] at lowering
    have reflected := child env state expressionSource metadata ls after id pt cx fr lowering point
      extension rel moduleEq resultsEq generated
    exact reflected.of_source (otherFuel := sourceFuel + 1) (by simp only [evalArg])


theorem typedArgFuelBound_byRef {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (mutability : Mutability) (child : TypedPlaceFuelBound sourceFuel fuel cfg results place) :
    TypedArgFuelBound (sourceFuel + 1) fuel cfg results (.byRef mutability place) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  cases source with
  | byRef _ placeSource target =>
    have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := metadata
    simp only [lowerArg, bind_eq] at lowering
    obtain ⟨address, middle, placeRun, freeze⟩ := lowering
    rcases borrowTo_ref_cases freeze with ⟨rfl,rfl⟩ | definition | definition
    · have first := child env state placeSource placeMetadata ls after resultId pt cx fr placeRun
        point extension rel moduleEq resultsEq generated
      have composition : FuelBoundAt sourceFuel fuel cx pt fr
          (fun sourceFuel => evalPlace sourceFuel cfg env place >>= fun location => pure (.ref location))
          (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
        refine first.bind ?_
        intro location next pt' fr' done post residual bound
        exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := residual) post
      exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalArg])
    · have middleExtension := extension.of_adv (adv_emitDef definition)
      have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun
        point middleExtension rel moduleEq resultsEq generated
      have composition : FuelBoundAt sourceFuel fuel cx pt fr
          (fun sourceFuel => evalPlace sourceFuel cfg env place >>= fun location => pure (.ref location))
          (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
        refine first.bind ?_
        intro location next pt' fr' done post residual bound
        have cell := post.has (address,.val (.ref location)) (by simp)
        exact leaf_def_fuelBoundAt post definition extension (by intro f args org h; cases h)
          RVal.val (sourceFuel := sourceFuel) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
      exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalArg])

    · have middleExtension := extension.of_adv (adv_emitDef definition)
      have first := child env state placeSource placeMetadata ls middle address pt cx fr placeRun
        point middleExtension rel moduleEq resultsEq generated
      have composition : FuelBoundAt sourceFuel fuel cx pt fr
          (fun sourceFuel => evalPlace sourceFuel cfg env place >>= fun location => pure (.ref location))
          (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
        refine first.bind ?_
        intro location next pt' fr' done post residual bound
        have cell := post.has (address,.val (.ref location)) (by simp)
        exact leaf_def_fuelBoundAt post definition extension (by intro f args org h; cases h)
          RVal.val (sourceFuel := sourceFuel) (by
          simp only [execPure, getVal_of cell, expectRef, pure_bind])
      exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalArg])


theorem typedPlaceFuelBound_field {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (child : TypedPlaceFuelBound sourceFuel fuel cfg results place) (index : Nat) :
    TypedPlaceFuelBound (sourceFuel + 1) fuel cfg results (.field place index) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots⟩ := source.fieldChild index
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerPlace, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, fieldRun⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef fieldRun)
  have first := child env state childSource childMetadata ls middle address pt cx fr placeRun
    point middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalPlace sourceFuel cfg env place >>= fun location => pure { location with path := location.path ++ [index] })
      (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state := by
    refine first.bind ?_
    intro location next pt' fr' done post residual bound
    have cell := post.has (address,.val (.ref location)) (by simp)
    refine leaf_def_fuelBoundAt post fieldRun extension (by intro f args org h; cases h)
      (fun location => RVal.val (.ref location)) (sourceFuel := sourceFuel) ?_
    simp only [execPure, getVal_of cell, expectRef, pure_bind]
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalPlace])


theorem typedViewFuelBound_of {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {place : Place}
    (child : TypedPlaceFuelBound sourceFuel fuel cfg results place) :
    TypedViewFuelBound (sourceFuel + 1) fuel cfg results (.of place) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots, _⟩ := source.ofChild
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerView, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, viewRun⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef viewRun)
  have first := child env state childSource childMetadata ls middle address pt cx fr placeRun
    point middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalPlace sourceFuel cfg env place >>= fun location =>
        readLoc location >>= fun value => do
          let (length,resizable) ← expectArray value
          pure ({loc := location, start := 0, len := length, resizable := resizable} : ViewVal))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.view value)]) state := by
    refine first.bind ?_
    intro location next pt' fr' done post residual bound
    have cell := post.has (address,.val (.ref location)) (by simp)
    refine leaf_def_fuelBoundAt post viewRun extension (by intro f args org h; cases h)
      RVal.view (sourceFuel := sourceFuel) ?_
    simp only [execPure, getVal_of cell, expectRef, pure_bind, bind_assoc]
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalView])


theorem typedViewFuelBound_val {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expr) :
    TypedViewFuelBound (sourceFuel + 1) fuel cfg results (.val expr) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots, mutability, type, _⟩ := source.valChild
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerView, bind_eq] at lowering
  obtain ⟨sliceId, middle, exprRun, viewRun⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef viewRun)
  have first := child env state childSource childMetadata ls middle sliceId pt cx fr exprRun
    point middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env expr >>= fun value => do
        let (location,start,length) ← expectSlice value
        pure ({loc := location, start := start, len := length, resizable := false} : ViewVal))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.view value)]) state := by
    refine first.bind ?_
    intro value next pt' fr' done post residual bound
    have cell := post.has (sliceId,.val value) (by simp)
    refine leaf_def_fuelBoundAt post viewRun extension (by intro f args org h; cases h)
      RVal.view (sourceFuel := sourceFuel) ?_
    simp only [execPure, getVal_of cell, expectSlice, pure_bind, bind_assoc]
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalView])


theorem typedBoundFuelBound_expr {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expr) :
    TypedBoundFuelBound (sourceFuel + 1) fuel cfg results (.expr expr) := by
  intro env state source metadata ls after bnd pt cx fr length default lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots, intTy, type, _⟩ := source.expressionChild false
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerBound, bind_eq] at lowering
  obtain ⟨valueId, middle, exprRun, pureRun⟩ := lowering
  rw [pure_run] at pureRun
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj pureRun
  have first := child env state childSource childMetadata ls middle valueId pt cx fr exprRun
    point extension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env expr >>= fun value => do
        let (_,integer) ← expectInt value
        pure integer)
      (fun value _ pt' fr' => ∃ cells, BndSpec length default (.val valueId) value cells ∧
        Post cfg env cx ls fr middle fr' pt' cells) state := by
    refine first.bind ?_
    intro value next pt' fr' done post residual bound
    have typed := (childSource.result sourceFuel value done).typed
    rw [type] at typed
    obtain ⟨integer,rfl⟩ := Core.Sound.hasTy_int typed
    refine FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := residual) ⟨[(valueId,.val (.int intTy integer))], ?_, post⟩
    exact ⟨intTy, by simp⟩
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalBound])


theorem typedBoundFuelBound_fromEnd {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expr : Expr}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expr) :
    TypedBoundFuelBound (sourceFuel + 1) fuel cfg results (.fromEnd expr) := by
  intro env state source metadata ls after bnd pt cx fr length default lowering point extension rel moduleEq resultsEq generated
  obtain ⟨childSource, typing, roots, intTy, type, _⟩ := source.expressionChild true
  have childMetadata : SourceResults childSource.typingEnv childSource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  simp only [lowerBound, bind_eq] at lowering
  obtain ⟨valueId, middle, exprRun, pureRun⟩ := lowering
  rw [pure_run] at pureRun
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj pureRun
  have first := child env state childSource childMetadata ls middle valueId pt cx fr exprRun
    point extension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env expr >>= fun value => do
        let (_,integer) ← expectInt value
        pure ((length : Int) - integer))
      (fun value _ pt' fr' => ∃ cells, BndSpec length default (.fromEnd valueId) value cells ∧
        Post cfg env cx ls fr middle fr' pt' cells) state := by
    refine first.bind ?_
    intro value next pt' fr' done post residual bound
    have typed := (childSource.result sourceFuel value done).typed
    rw [type] at typed
    obtain ⟨integer,rfl⟩ := Core.Sound.hasTy_int typed
    refine FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := residual) ⟨[(valueId,.val (.int intTy integer))], ?_, post⟩
    exact ⟨intTy, integer, by simp⟩
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalBound])


end Goose.Lower
