import Goose.Lower.ReflectionLeaves

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def ExprReflection (fuel : Nat) (expression : Expr) : Prop :=
  ∀ (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv) (ls after : LS) (fr : Frame)
    (pt : Pt) (resultId : ValueId) (state : St),
    Rel cfg env cx fr ls → ls.pp = some pt →
    lowerExpr expression le ls = (resultId,after) → ExtT after cx.fn.blocks →
    ReflectAtFuel fuel cx pt fr (fun n => evalExpr n cfg env expression)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state

def PlaceReflection (fuel : Nat) (place : Place) : Prop :=
  ∀ (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv) (ls after : LS) (fr : Frame)
    (pt : Pt) (resultId : ValueId) (state : St),
    Rel cfg env cx fr ls → ls.pp = some pt →
    lowerPlace place le ls = (resultId,after) → ExtT after cx.fn.blocks →
    ReflectAtFuel fuel cx pt fr (fun n => evalPlace n cfg env place)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val (.ref value))]) state

def ViewReflection (fuel : Nat) (view : View) : Prop :=
  ∀ (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv) (ls after : LS) (fr : Frame)
    (pt : Pt) (resultId : ValueId) (state : St),
    Rel cfg env cx fr ls → ls.pp = some pt →
    lowerView view le ls = (resultId,after) → ExtT after cx.fn.blocks →
    ReflectAtFuel fuel cx pt fr (fun n => evalView n cfg env view)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.view value)]) state

theorem exprReflection_lit (fuel : Nat) (type : IntTy) (value : Int) :
    ExprReflection fuel (.lit type value) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  exact lowerExpr_lit_reflectAtFuel rel point lowering extension

theorem exprReflection_bool (fuel : Nat) (value : Bool) :
    ExprReflection fuel (.bool value) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  exact lowerExpr_bool_reflectAtFuel rel point lowering extension

theorem placeReflection_var (fuel : Nat) (varId : VarId) :
    PlaceReflection fuel (.var varId) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  exact lowerPlace_var_reflectAtFuel rel point lowering extension

theorem placeReflection_global (fuel : Nat) (global : GlobalId) :
    PlaceReflection fuel (.global global) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  exact lowerPlace_global_reflectAtFuel rel point lowering extension

theorem exprReflection_read {fuel : Nat} {place : Place}
    (child : PlaceReflection fuel place) : ExprReflection fuel (.read place) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨address,middle,lowerPlaceRun,emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := child cfg env cx le ls middle fr pt address state rel point lowerPlaceRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= readLoc)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
      (fun _ _ _ _ => MonoM.refl _) 
    intro n location next pt' fr' source post residual bound
    have cell := post.has (address,.val (.ref location)) (by simp)
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    simp only [execPure, getVal_of cell, expectRef, pure_bind]
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

theorem exprReflection_not {fuel : Nat} {expression : Expr}
    (child : ExprReflection fuel expression) : ExprReflection fuel (.not expression) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨argument,middle,lowerExprRun,emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := child cfg env cx le ls middle fr pt argument state rel point lowerExprRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= fun value => do
        pure (.bool (!(← expectBool value))))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' source post residual bound
    have cell := post.has (argument,.val value) (by simp)
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    simp only [execPure, getVal_of cell, bind_assoc, pure_bind]
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

theorem exprReflection_len {fuel : Nat} {view : View}
    (child : ViewReflection fuel view) : ExprReflection fuel (.len view) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨argument,middle,lowerViewRun,emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := child cfg env cx le ls middle fr pt argument state rel point lowerViewRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalView n cfg env view >>= fun value => pure (.int .i64 value.len))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).view cfg env view)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' source post residual bound
    have cell := post.has (argument,.view value) (by simp)
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    simp only [execPure, getView_of cell, pure_bind]
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

theorem exprReflection_ref {fuel : Nat} {place : Place} (mutability : Mutability)
    (child : PlaceReflection fuel place) : ExprReflection fuel (.ref mutability place) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨address,middle,lowerPlaceRun,freeze⟩ := lowering
  rcases freezeTo_cases freeze with ⟨rfl,rfl⟩ | ⟨emit⟩
  · have first := child cfg env cx le ls after fr pt resultId state rel point lowerPlaceRun extension
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => evalPlace n cfg env place >>= fun value => pure (.ref value))
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
        (fun _ _ _ _ => MonoM.refl _)
      intro n value next pt' fr' source post residual bound
      exact ReflectAtFuel.ret residual post
    exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)
  · have middleExtension := extension.of_adv (adv_emitDef emit)
    have first := child cfg env cx le ls middle fr pt address state rel point lowerPlaceRun middleExtension
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => evalPlace n cfg env place >>= fun value => pure (.ref value))
        (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
      refine first.bind ?_ (fun n k bound => (monoAll n k bound).place cfg env place)
        (fun _ _ _ _ => MonoM.refl _)
      intro n value next pt' fr' source post residual bound
      have cell := post.has (address,.val (.ref value)) (by simp)
      refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
        RVal.val (sourceFuel := 0) ?_
      simp only [execPure, getVal_of cell, expectRef, pure_bind]
    exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

end Goose.Lower
