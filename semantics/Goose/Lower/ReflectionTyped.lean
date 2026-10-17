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

end Goose.Lower
