import Goose.Lower.FuelBoundTyped
import Goose.Lower.ReflectionTyped

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem typedExprFuelBound_lit (fuel : Nat) (cfg : Cfg) (results : List Ty) (type : IntTy) (value : Int) :
    TypedExprFuelBound 1 fuel cfg results (.lit type value) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact lowerExpr_lit_fuelBoundAt rel point lowering extension

theorem typedExprFuelBound_bool (fuel : Nat) (cfg : Cfg) (results : List Ty) (value : Bool) :
    TypedExprFuelBound 1 fuel cfg results (.bool value) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact lowerExpr_bool_fuelBoundAt rel point lowering extension

theorem typedExprFuelBound_not {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.not expression) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨expressionSource,typing,roots,_⟩ := source.notChild
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing,roots]
    exact metadata
  simp only [lowerExpr,bind_eq] at lowering
  obtain ⟨argument,middle,expressionRun,emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := child env state expressionSource expressionMetadata ls middle argument pt cx fr
    expressionRun point middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env expression >>= fun value => do pure (.bool (!(← expectBool value))))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state := by
    refine first.bind ?_
    intro value next pt' fr' done post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_fuelBoundAt post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := sourceFuel) ?_
    simp only [execPure,getVal_of cell,bind_assoc,pure_bind]
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])


theorem typedExprFuelBound_conv {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (kind : ConvKind) (target : Ty) (origin : OriginId)
    (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.conv kind target expression origin) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨expressionSource,typing,roots,inputInt,targetInt,_,rfl,_⟩ := source.convChild kind target origin
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing,roots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨argument,middle,lowerExprRun,type,middle',typeRun,emit⟩ := lowering
  have same := intTyOf_eq typeRun
  subst same
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := child env state expressionSource expressionMetadata ls middle' argument pt cx fr
    lowerExprRun point middleExtension rel moduleEq resultsEq generated
  let operationSource := fun value => do
    let (type,integer) ← expectInt value
    match evalConv cfg.profile kind type targetInt integer with
    | .ok result => pure (Val.int targetInt result)
    | .error kind => abortAt (AbortKind.ofNum kind) origin
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env expression >>= operationSource)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_
    intro value next pt' fr' source post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_fuelBoundAt post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := sourceFuel) ?_
    cases value with
    | int t integer =>
      simp only [execPure,getVal_of cell,expectInt,pure_bind,post.rel.prof]
      cases evalConv cfg.profile kind t targetInt integer <;> rfl
    | _ =>
      funext s
      simp only [execPure,getVal_of cell,expectInt,pure_bind]
      rfl
  refine composition.of_source (otherFuel := sourceFuel + 1) ?_
  simp only [evalExpr]
  apply congrFun
  apply congrArg (fun continuation : Val → M Val => evalExpr sourceFuel cfg env expression >>= continuation)
  funext value s
  simp only [operationSource,bind_apply]
  cases expectInt value s <;> rfl


theorem typedExprFuelBound_fill {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (target : Ty) (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.fill target expression) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨element,count,rfl,expressionSource,typing,roots,_⟩ := source.fillChild target
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing,roots]
    exact metadata
  simp only [lowerExpr,bind_eq] at lowering
  obtain ⟨argument,middle,lowerExprRun,emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := child env state expressionSource expressionMetadata ls middle argument pt cx fr
    lowerExprRun point middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env expression >>= fun value => pure (.fixed (Array.replicate count value)))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_
    intro value next pt' fr' source post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_fuelBoundAt post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := sourceFuel) ?_
    simp only [execPure,expectFixedCount,getVal_of cell,pure_bind]
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr,expectFixedCount,pure_bind])


theorem typedExprFuelBound_un {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (operation : UnOp) (origin : OriginId) (child : TypedExprFuelBound sourceFuel fuel cfg results expression) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.un operation expression origin) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨expressionSource,typing,roots,_⟩ := source.unChild operation origin
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing,roots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨argument,middle,lowerExprRun,type,middle',typeRun,emit⟩ := lowering
  have same := intTyOf_eq typeRun
  subst same
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := child env state expressionSource expressionMetadata ls middle' argument pt cx fr
    lowerExprRun point middleExtension rel moduleEq resultsEq generated
  let operationSource := fun value => do
    let (type,integer) ← expectInt value
    match evalUn cfg.profile operation type integer with
    | .ok result => pure (Val.int type result)
    | .error kind => abortAt (AbortKind.ofNum kind) origin
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env expression >>= operationSource)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_
    intro value next pt' fr' source post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_fuelBoundAt post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := sourceFuel) ?_
    cases value with
    | int t integer =>
      simp only [execPure,getVal_of cell,expectInt,pure_bind,post.rel.prof]
      cases evalUn cfg.profile operation t integer <;> rfl
    | _ =>
      funext s
      simp only [execPure,getVal_of cell,expectInt,pure_bind]
      rfl
  refine composition.of_source (otherFuel := sourceFuel + 1) ?_
  simp only [evalExpr]
  apply congrFun
  apply congrArg (fun continuation : Val → M Val => evalExpr sourceFuel cfg env expression >>= continuation)
  funext value s
  simp only [operationSource,bind_apply]
  cases expectInt value s <;> rfl



theorem typedExprFuelBound_bin {cfg : Cfg} {results : List Ty} {left right : Expr} {sourceFuel fuel : Nat}
    (operation : BinOp) (origin : OriginId)
    (leftChild : TypedExprFuelBound sourceFuel fuel cfg results left)
    (rightChild : ∀ residual, residual ≤ fuel → TypedExprFuelBound sourceFuel residual cfg results right) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.bin operation left right origin) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨integer,leftSource,leftTyping,leftRoots,leftType,_,rightSources⟩ := source.binChildren operation origin
  have leftMetadata : SourceResults leftSource.typingEnv leftSource.rootsEnv results := by
    rw [leftTyping,leftRoots]
    exact metadata
  simp only [lowerExpr,bind_eq] at lowering
  obtain ⟨x,middle,leftRun,y,last,rightRun,type,last',typeRun,emit⟩ := lowering
  have same := intTyOf_eq typeRun
  subst same
  have lastExtension := extension.of_adv (adv_emitDef emit)
  have middleExtension := lastExtension.of_adv (advB_lowerExpr right _ _ _ _ rightRun)
  have first := leftChild env state leftSource leftMetadata ls middle x pt cx fr leftRun point
    middleExtension rel moduleEq resultsEq generated
  have middleGenerated := generated.lowerExpr left leftRun
  let binarySource := fun value sourceFuel => do
    let (t,x) ← expectInt value
    let (u,y) ← expectInt (← evalExpr sourceFuel cfg env right)
    expectSameTy t u
    match evalBin cfg.profile operation t x y with
    | .ok result => pure (Val.int t result)
    | .error kind => abortAt (AbortKind.ofNum kind) origin
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env left >>= fun value => binarySource value sourceFuel)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state := by
    refine first.bind ?_
    intro a next pt' fr' done post residual bound
    have typed := (leftSource.result sourceFuel a done).typed
    rw [leftType] at typed
    obtain ⟨leftInteger,rfl⟩ := Core.Sound.hasTy_int typed
    obtain ⟨rightSource,rightTyping,rightRoots,rightType,_⟩ := rightSources sourceFuel _ next done
    have rightMetadata : SourceResults rightSource.typingEnv rightSource.rootsEnv results := by
      rw [rightTyping,rightRoots]
      exact metadata
    have second := rightChild residual bound env next rightSource rightMetadata middle last' y pt' cx fr'
      rightRun post.pp lastExtension post.rel moduleEq resultsEq middleGenerated
    simp only [binarySource,expectInt,pure_bind]
    refine second.bind ?_
    intro b final pt'' fr'' rightDone post' remaining remainingBound
    have typed := (rightSource.result sourceFuel b rightDone).typed
    rw [rightType] at typed
    obtain ⟨rightInteger,rfl⟩ := Core.Sound.hasTy_int typed
    have combined := post.comp post'
    have leftCell := combined.has (x,.val (.int integer leftInteger)) (by simp)
    have rightCell := combined.has (y,.val (.int integer rightInteger)) (by simp)
    refine leaf_def_fuelBoundAt combined emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := sourceFuel) ?_
    simp only [execPure,getVal_of leftCell,getVal_of rightCell,expectInt,expectSameTy,
      ↓reduceIte,pure_bind,post'.rel.prof]
    cases evalBin cfg.profile operation integer leftInteger rightInteger <;> rfl
  refine composition.of_source (otherFuel := sourceFuel + 1) ?_
  simp only [evalExpr]
  apply congrFun
  apply congrArg (fun continuation : Val → M Val => evalExpr sourceFuel cfg env left >>= continuation)
  funext value s
  simp only [binarySource,bind_apply]
  cases expectInt value s with
  | stop stop after => rfl
  | ok pair after => cases pair; rfl


theorem typedExprFuelBound_cmp {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} {left right : Expr}
    (operation : CmpOp) (leftChild : TypedExprFuelBound sourceFuel fuel cfg results left)
    (rightChild : ∀ residual, residual ≤ fuel → TypedExprFuelBound sourceFuel residual cfg results right) :
    TypedExprFuelBound (sourceFuel + 1) fuel cfg results (.cmp operation left right) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨leftSource,leftTyping,leftRoots,_,rightSources⟩ := source.cmpChildren operation
  have leftMetadata : SourceResults leftSource.typingEnv leftSource.rootsEnv results := by
    rw [leftTyping,leftRoots]
    exact metadata
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨x,middle,leftRun,y,last,rightRun,type,last',typeRun,emit⟩ := lowering
  have same := valTy_eq typeRun
  subst same
  have selected : ∃ op, emitDef op (lowerEnv cfg.mod env.vars results) last' = (resultId,after) ∧
      (op = .boolCmp operation x y ∨ ∃ type, op = .cmp operation type x y) := by
    cases type with
    | data type =>
      cases type <;> first
        | exact ⟨_,emit,Or.inr ⟨_,rfl⟩⟩
        | exact ⟨_,emit,Or.inl rfl⟩
    | view _ _ => exact ⟨_,emit,Or.inl rfl⟩
  obtain ⟨op,emit,selected⟩ := selected
  have lastExtension := extension.of_adv (adv_emitDef emit)
  have middleExtension := lastExtension.of_adv (advB_lowerExpr right _ _ _ _ rightRun)
  have first := leftChild env state leftSource leftMetadata ls middle x pt cx fr
    leftRun point middleExtension rel moduleEq resultsEq generated
  have middleGenerated := generated.lowerExpr left leftRun
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun sourceFuel => evalExpr sourceFuel cfg env left >>= fun a => evalExpr sourceFuel cfg env right >>= fun b =>
        expectComparable a b >>= fun pair => pure (.bool (evalCmp operation pair.1 pair.2)))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_
    intro a next pt' fr' source post residual bound
    obtain ⟨rightSource,rightTyping,rightRoots,_⟩ := rightSources sourceFuel a next source
    have rightMetadata : SourceResults rightSource.typingEnv rightSource.rootsEnv results := by
      rw [rightTyping,rightRoots]
      exact metadata
    have second := rightChild residual bound env next rightSource rightMetadata middle last' y pt' cx fr'
      rightRun post.pp lastExtension post.rel moduleEq resultsEq middleGenerated
    refine second.bind ?_
    intro b final pt'' fr'' source' post' remaining remainingBound
    have combined := post.comp post'
    have leftCell := combined.has (x,.val a) (by simp)
    have rightCell := combined.has (y,.val b) (by simp)
    have noncall : ∀ f args org, op ≠ .call f args org := by
      rcases selected with rfl | ⟨type,rfl⟩ <;> simp
    refine leaf_def_fuelBoundAt combined emit extension noncall RVal.val (sourceFuel := sourceFuel) ?_
    rcases selected with rfl | ⟨type,rfl⟩
    · exact (execPure_cmp leftCell rightCell).2
    · exact (execPure_cmp leftCell rightCell).1 type
  exact composition.of_source (otherFuel := sourceFuel + 1) (by simp only [evalExpr])


end Goose.Lower
