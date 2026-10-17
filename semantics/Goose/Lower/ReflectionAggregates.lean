import Goose.Lower.ReflectionExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def ExprsReflection (fuel : Nat) (expressions : List Expr) : Prop :=
  ∀ (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv) (ls after : LS) (fr : Frame)
    (pt : Pt) (ids : List ValueId) (state : St),
    Rel cfg env cx fr ls → ls.pp = some pt →
    lowerExprs expressions le ls = (ids,after) → ExtT after cx.fn.blocks →
    ReflectAtFuel fuel cx pt fr (fun n => mapList (evalExpr n cfg env) expressions)
      (fun values _ pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr after fr' pt' (cellsOf ids values)) state

theorem exprsReflection_nil (fuel : Nat) : ExprsReflection fuel [] := by
  intro cfg env cx le ls after fr pt ids state rel point lowering extension
  simp only [lowerExprs,pure_run] at lowering
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj lowering
  exact ReflectAtFuel.ret fuel ⟨rfl,by simpa only [cellsOf] using Post.init rel point⟩

theorem exprsReflection_cons {fuel : Nat} {expression : Expr} {rest : List Expr}
    (head : ExprReflection fuel expression)
    (tail : ∀ residual, residual ≤ fuel → ExprsReflection residual rest) :
    ExprsReflection fuel (expression :: rest) := by
  intro cfg env cx le ls after fr pt ids state rel point lowering extension
  simp only [lowerExprs,bind_eq] at lowering
  obtain ⟨id,middle,headRun,restIds,last,tailRun,finish⟩ := lowering
  rw [pure_run] at finish
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj finish
  have middleExtension := extension.of_adv (advB_lowerExprs rest _ _ _ _ tailRun)
  have first := head cfg env cx le ls middle fr pt id state rel point headRun middleExtension
  simp only [mapList]
  refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression) ?_
  · intro n value next pt' fr' source post residual bound
    have second := tail residual bound cfg env cx le middle last fr' pt' restIds next
      post.rel post.pp tailRun extension
    refine second.bind ?_
      (fun n k bound => MonoM.mapList (fun e => (monoAll n k bound).expr cfg env e) rest)
      (fun _ _ _ _ => MonoM.refl _)
    intro k values final pt'' fr'' source' matched remaining remainingBound
    obtain ⟨length,post'⟩ := matched
    exact ReflectAtFuel.ret remaining
      ⟨by simp only [List.length_cons,length],by simpa only [cellsOf,List.singleton_append] using post.comp post'⟩
  · intro value n k bound
    exact (MonoM.mapList (fun e => (monoAll n k bound).expr cfg env e) rest).bind
      (fun _ => MonoM.refl _)

theorem exprsReflection_of_children {fuel : Nat} {expressions : List Expr}
    (children : ∀ expression ∈ expressions, ∀ residual, residual ≤ fuel → ExprReflection residual expression) :
    ExprsReflection fuel expressions := by
  induction expressions generalizing fuel with
  | nil => exact exprsReflection_nil fuel
  | cons expression rest induction =>
    apply exprsReflection_cons (children expression (by simp) fuel (Nat.le_refl _))
    intro residual bound
    apply induction
    intro child member remaining remainingBound
    exact children child (by simp [member]) remaining (Nat.le_trans remainingBound bound)

theorem exprReflection_arrLit {fuel : Nat} {expressions : List Expr} (type : Ty)
    (children : ExprsReflection fuel expressions) : ExprReflection fuel (.arrLit type expressions) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  simp only [lowerExpr,bind_eq] at lowering
  obtain ⟨ids,middle,childrenRun,emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := children cfg env cx le ls middle fr pt ids state rel point childrenRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => mapList (evalExpr n cfg env) expressions >>= fun values => expectArrayLit type values.toArray)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_
      (fun n k bound => MonoM.mapList (fun e => (monoAll n k bound).expr cfg env e) expressions)
      (fun _ _ _ _ => MonoM.refl _)
    intro n values next pt' fr' source matched residual bound
    obtain ⟨length,post⟩ := matched
    have cells := mapList_getVal_cells (fr := fr') length post.has
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    simp only [execPure,cells,pure_bind]
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

theorem exprReflection_structLit {fuel : Nat} {expressions : List Expr}
    (structId : Nat) (arguments : TyList) (children : ExprsReflection fuel expressions) :
    ExprReflection fuel (.structLit (.structT structId arguments) expressions) := by
  intro cfg env cx le ls after fr pt resultId state rel point lowering extension
  simp only [lowerExpr,bind_eq] at lowering
  obtain ⟨ids,middle,childrenRun,emit⟩ := lowering
  have middleExtension := extension.of_adv (adv_emitDef emit)
  have first := children cfg env cx le ls middle fr pt ids state rel point childrenRun middleExtension
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => mapList (evalExpr n cfg env) expressions >>= fun values => pure (.record structId values.toArray))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_
      (fun n k bound => MonoM.mapList (fun e => (monoAll n k bound).expr cfg env e) expressions)
      (fun _ _ _ _ => MonoM.refl _)
    intro n values next pt' fr' source matched residual bound
    obtain ⟨length,post⟩ := matched
    have cells := mapList_getVal_cells (fr := fr') length post.has
    refine leaf_def_reflectAtFuel post emit extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) ?_
    simp only [execPure,cells,pure_bind]
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

end Goose.Lower
