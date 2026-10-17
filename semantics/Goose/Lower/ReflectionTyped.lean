import Goose.Lower.GeneratedBuilder
import Goose.Lower.TypedExpressions
import Goose.Lower.ReflectionExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem ReflectAtFuel.typed_bool {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    {fuel : Nat} {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {post : Val → St → Pt → GIR.Frame → Prop}
    (source : ExprSource cfg env expression state) (type : source.ty = .bool)
    (reflection : ReflectAtFuel fuel cx pt fr (fun n => evalExpr n cfg env expression) post state) :
    ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= expectBool)
      (fun value after pt' fr' => post (.bool value) after pt' fr') state := by
  refine reflection.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
    (fun _ _ _ _ => MonoM.refl _)
  intro n value after pt' fr' done matched residual bound
  have typed := (source.result n value done).typed
  rw [type] at typed
  obtain ⟨boolean,rfl⟩ := Core.Sound.hasTy_bool typed
  exact ReflectAtFuel.ret residual matched

theorem lowerPlace_deref_reflectAtFuel {cfg : Cfg} {env : Env} {expression : Expr} {state : St}
    {fuel : Nat} {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {ls after : LS} {id : ValueId} {le : LEnv}
    (source : PlaceSource cfg env (.deref expression) state)
    (normal : sliceRefTy source.typingEnv expression = none)
    (lowering : lowerPlace (.deref expression) le ls = (id,after))
    (child : lowerExpr expression le ls = (id,after) →
      ReflectAtFuel fuel cx pt fr (fun n => evalExpr n cfg env expression)
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state) :
    ReflectAtFuel fuel cx pt fr (fun n => evalPlace n cfg env (.deref expression))
      (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state := by
  have expressionRun : lowerExpr expression le ls = (id,after) := by
    simpa only [lowerPlace] using lowering
  have child := child expressionRun
  obtain ⟨expressionSource,_,_,mutability,target,type⟩ := source.derefChild normal
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= expectRef)
      (fun location _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val (.ref location))]) state := by
    refine child.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' done matched residual bound
    have typed := (expressionSource.result n value done).typed
    rw [type] at typed
    obtain ⟨location,rfl,_⟩ := typed
    exact ReflectAtFuel.ret residual matched
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalPlace]⟩)

def TypedExprReflection (fuel : Nat) (cfg : Cfg) (results : List Ty) (expression : Expr) : Prop :=
  ∀ (env : Env) (state : St) (source : ExprSource cfg env expression state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls after : LS) (id : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerExpr expression (lowerEnv cfg.mod env.vars results) ls = (id,after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    ReflectAtFuel fuel cx pt fr (fun n => evalExpr n cfg env expression)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state

theorem TypedExprReflection.of_untyped {fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (reflection : ExprReflection fuel expression) : TypedExprReflection fuel cfg results expression := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact reflection cfg env cx (lowerEnv cfg.mod env.vars results) ls after fr pt id state
    rel point lowering extension

theorem typedExprReflection_lit (fuel : Nat) (cfg : Cfg) (results : List Ty) (type : IntTy) (value : Int) :
    TypedExprReflection fuel cfg results (.lit type value) :=
  TypedExprReflection.of_untyped (exprReflection_lit fuel type value)

theorem typedExprReflection_bool (fuel : Nat) (cfg : Cfg) (results : List Ty) (value : Bool) :
    TypedExprReflection fuel cfg results (.bool value) :=
  TypedExprReflection.of_untyped (exprReflection_bool fuel value)

theorem typedExprReflection_not {fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (child : TypedExprReflection fuel cfg results expression) :
    TypedExprReflection fuel cfg results (.not expression) := by
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
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= fun value => do pure (.bool (!(← expectBool value))))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' done post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    simp only [execPure,getVal_of cell,bind_assoc,pure_bind]
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

theorem typedExprReflection_bin {cfg : Cfg} {results : List Ty} {left right : Expr} {fuel : Nat}
    (operation : BinOp) (origin : OriginId)
    (leftChild : TypedExprReflection fuel cfg results left)
    (rightChild : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results right) :
    TypedExprReflection fuel cfg results (.bin operation left right origin) := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨integer,leftSource,leftTyping,leftRoots,leftType,rightSources⟩ := source.binChildren operation origin
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
  let binarySource := fun value n => do
    let (t,x) ← expectInt value
    let (u,y) ← expectInt (← evalExpr n cfg env right)
    expectSameTy t u
    match evalBin cfg.profile operation t x y with
    | .ok result => pure (Val.int t result)
    | .error kind => abortAt (AbortKind.ofNum kind) origin
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env left >>= fun value => binarySource value n)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env left) ?_
    · intro n a next pt' fr' done post residual bound
      have typed := (leftSource.result n a done).typed
      rw [leftType] at typed
      obtain ⟨leftInteger,rfl⟩ := Core.Sound.hasTy_int typed
      obtain ⟨rightSource,rightTyping,rightRoots,rightType⟩ := rightSources n _ next done
      have rightMetadata : SourceResults rightSource.typingEnv rightSource.rootsEnv results := by
        rw [rightTyping,rightRoots]
        exact metadata
      have second := rightChild residual bound env next rightSource rightMetadata middle last' y pt' cx fr'
        rightRun post.pp lastExtension post.rel moduleEq resultsEq middleGenerated
      simp only [binarySource,expectInt,pure_bind]
      refine second.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env right)
        (fun _ _ _ _ => MonoM.refl _)
      intro k b final pt'' fr'' rightDone post' remaining remainingBound
      have typed := (rightSource.result k b rightDone).typed
      rw [rightType] at typed
      obtain ⟨rightInteger,rfl⟩ := Core.Sound.hasTy_int typed
      have combined := post.comp post'
      have leftCell := combined.has (x,.val (.int integer leftInteger)) (by simp)
      have rightCell := combined.has (y,.val (.int integer rightInteger)) (by simp)
      refine leaf_def_reflectAtFuel combined emit extension (by intro f args org h; cases h)
        RVal.val (sourceFuel := 0) ?_
      simp only [execPure,getVal_of leftCell,getVal_of rightCell,expectInt,expectSameTy,
        ↓reduceIte,pure_bind,post'.rel.prof]
      cases evalBin cfg.profile operation integer leftInteger rightInteger <;> rfl
    · intro value n k bound
      unfold binarySource
      exact (MonoM.refl (expectInt value)).bind (fun pair =>
        ((monoAll n k bound).expr cfg env right).bind (fun value => MonoM.refl _))
  refine composition.of_source (fun n => ⟨n + 1,?_⟩)
  simp only [evalExpr]
  apply congrFun
  apply congrArg (fun continuation : Val → M Val => evalExpr n cfg env left >>= continuation)
  funext value s
  simp only [binarySource,bind_apply]
  cases expectInt value s with
  | stop stop after => rfl
  | ok pair after => cases pair; rfl

theorem typedExprReflection_conv {fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (kind : ConvKind) (target : Ty) (origin : OriginId)
    (child : TypedExprReflection fuel cfg results expression) :
    TypedExprReflection fuel cfg results (.conv kind target expression origin) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨expressionSource,typing,roots,inputInt,targetInt,_,rfl⟩ := source.convChild kind target origin
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
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= operationSource)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' source post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    cases value with
    | int t integer =>
      simp only [execPure,getVal_of cell,expectInt,pure_bind,post.rel.prof]
      cases evalConv cfg.profile kind t targetInt integer <;> rfl
    | _ =>
      funext s
      simp only [execPure,getVal_of cell,expectInt,pure_bind]
      rfl
  refine composition.of_source (fun n => ⟨n + 1,?_⟩)
  simp only [evalExpr]
  apply congrFun
  apply congrArg (fun continuation : Val → M Val => evalExpr n cfg env expression >>= continuation)
  funext value s
  simp only [operationSource,bind_apply]
  cases expectInt value s <;> rfl

theorem typedExprReflection_fill {fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (target : Ty) (child : TypedExprReflection fuel cfg results expression) :
    TypedExprReflection fuel cfg results (.fill target expression) := by
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
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= fun value => pure (.fixed (Array.replicate count value)))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' source post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    simp only [execPure,expectFixedCount,getVal_of cell,pure_bind]
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr,expectFixedCount,pure_bind]⟩)

theorem typedExprReflection_un {fuel : Nat} {cfg : Cfg} {results : List Ty} {expression : Expr}
    (operation : UnOp) (origin : OriginId) (child : TypedExprReflection fuel cfg results expression) :
    TypedExprReflection fuel cfg results (.un operation expression origin) := by
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
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= operationSource)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' source post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    cases value with
    | int t integer =>
      simp only [execPure,getVal_of cell,expectInt,pure_bind,post.rel.prof]
      cases evalUn cfg.profile operation t integer <;> rfl
    | _ =>
      funext s
      simp only [execPure,getVal_of cell,expectInt,pure_bind]
      rfl
  refine composition.of_source (fun n => ⟨n + 1,?_⟩)
  simp only [evalExpr]
  apply congrFun
  apply congrArg (fun continuation : Val → M Val => evalExpr n cfg env expression >>= continuation)
  funext value s
  simp only [operationSource,bind_apply]
  cases expectInt value s <;> rfl

theorem typedExprReflection_cmp {fuel : Nat} {cfg : Cfg} {results : List Ty} {left right : Expr}
    (operation : CmpOp) (leftChild : TypedExprReflection fuel cfg results left)
    (rightChild : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results right) :
    TypedExprReflection fuel cfg results (.cmp operation left right) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  obtain ⟨leftSource,leftTyping,leftRoots,rightSources⟩ := source.cmpChildren operation
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
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env left >>= fun a => evalExpr n cfg env right >>= fun b =>
        expectComparable a b >>= fun pair => pure (.bool (evalCmp operation pair.1 pair.2)))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env left) ?_
    · intro n a next pt' fr' source post residual bound
      obtain ⟨rightSource,rightTyping,rightRoots⟩ := rightSources n a next source
      have rightMetadata : SourceResults rightSource.typingEnv rightSource.rootsEnv results := by
        rw [rightTyping,rightRoots]
        exact metadata
      have second := rightChild residual bound env next rightSource rightMetadata middle last' y pt' cx fr'
        rightRun post.pp lastExtension post.rel moduleEq resultsEq middleGenerated
      refine second.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env right)
        (fun _ _ _ _ => MonoM.refl _)
      intro k b final pt'' fr'' source' post' remaining remainingBound
      have combined := post.comp post'
      have leftCell := combined.has (x,.val a) (by simp)
      have rightCell := combined.has (y,.val b) (by simp)
      have noncall : ∀ f args org, op ≠ .call f args org := by
        rcases selected with rfl | ⟨type,rfl⟩ <;> simp
      refine leaf_def_reflectAtFuel combined emit extension noncall RVal.val (sourceFuel := 0) ?_
      rcases selected with rfl | ⟨type,rfl⟩
      · exact (execPure_cmp leftCell rightCell).2
      · exact (execPure_cmp leftCell rightCell).1 type
    · intro a n k bound
      exact ((monoAll n k bound).expr cfg env right).bind (fun _ => MonoM.refl _)
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

end Goose.Lower
