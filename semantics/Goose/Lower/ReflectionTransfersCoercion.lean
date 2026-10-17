import Goose.Lower.Coerce
import Goose.Lower.ReflectionLeaves

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private theorem ReflectAtFuel.pure_result_eq {fuel : Nat} {cx : FnCtx} {pt : Pt}
    {fr : Frame} {value : α} {state : St} {post : α → St → Pt → Frame → Prop}
    (reflection : ReflectAtFuel fuel cx pt fr (fun _ => pure value) post state) :
    ReflectAtFuel fuel cx pt fr (fun _ => pure value)
      (fun result after pt' fr' => result = value ∧ post result after pt' fr') state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout run with success | stopped
  · obtain ⟨n, sourceValue, after, pt', fr', residual, sourceRun, matched, bound, targetRun⟩ := success
    have sourceValueEq : sourceValue = value := by
      change Res.ok value state = Res.ok sourceValue after at sourceRun
      exact (Res.ok.inj sourceRun).1.symm
    exact Or.inl ⟨n, sourceValue, after, pt', fr', residual, sourceRun,
      ⟨sourceValueEq, matched⟩, bound, targetRun⟩
  · exact Or.inr stopped

theorem coerceTo_reflectAtFuel {fuel : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv}
    {base ls ls' : LS} {before fr : Frame} {pt : Pt} {r r' : ValueId} {target : Ty}
    {value : Val} {org : OriginId} {state : St}
    (beforePost : Post cfg env cx base before ls fr pt [(r, .val value)])
    (shape : CoercionValue target value)
    (lowering : coerceTo target r org le ls = (r', ls'))
    (extension : ExtT ls' cx.fn.blocks) :
    ReflectAtFuel fuel cx pt fr (fun _ => pure value)
      (fun result _ pt' fr' => result = value ∧
        Post cfg env cx base before ls' fr' pt' [(r', .val result)]) state := by
  rcases coerceTo_cases lowering with ⟨result, finish⟩ | ⟨elem, targetEq, freeze⟩ |
      ⟨elem, view, middle, targetEq, viewRun, sliceRun⟩
  · subst r'
    subst ls'
    exact ReflectAtFuel.ret fuel ⟨rfl, beforePost⟩
  · subst target
    obtain ⟨location, valueEq⟩ := shape
    subst value
    have cell := beforePost.has (r, .val (.ref location)) (by simp)
    exact ReflectAtFuel.pure_result_eq (leaf_def_reflectAtFuel (fuel := fuel)
      (source := fun _ : Nat => pure (Val.ref location))
      (state := state) beforePost freeze extension
      (by intro function args origin impossible; cases impossible) RVal.val (sourceFuel := 0) (by
        simp only [execPure, getVal_of cell, expectRef, pure_bind]))
  · subst target
    obtain ⟨location, start, length, valueEq⟩ := shape
    subst value
    have cell := beforePost.has (r, .val (.slice location start length)) (by simp)
    have middleExtension := extension.of_adv (adv_emitDef sliceRun)
    let sampled : ViewVal := ⟨location, start, length, false⟩
    have first := leaf_def_reflectAtFuel (fuel := fuel) (state := state)
        (source := fun _ : Nat => (pure (Val.slice location start length) : M Val))
        beforePost viewRun middleExtension
        (by intro function args origin impossible; cases impossible) (fun _ => .view sampled)
        (sourceFuel := 0) (by
          simp only [execPure, getVal_of cell, expectSlice, pure_bind]
          simp [sampled])
    have first := ReflectAtFuel.pure_result_eq first
    have second : ∀ (n : Nat) value after pt' fr',
          (pure (Val.slice location start length) : M Val) state = Res.ok value after →
          (value = .slice location start length ∧
            Post cfg env cx base before middle fr' pt' [(view, .view sampled)]) →
          ∀ residual, residual ≤ fuel →
            ReflectAtFuel residual cx pt' fr' (fun _ : Nat => (pure value : M Val))
              (fun result _ pt'' fr'' => result = Val.slice location start length ∧
                Post cfg env cx base before ls' fr'' pt'' [(r', .val result)]) after := by
      intro n value after pt' fr' _ matched residual bound
      rcases matched with ⟨valueEq, viewPost⟩
      subst value
      have viewCell := viewPost.has (view, .view sampled) (by simp)
      exact ReflectAtFuel.pure_result_eq (leaf_def_reflectAtFuel (fuel := residual)
        (source := fun _ : Nat => (pure (Val.slice location start length) : M Val))
        (state := after) viewPost sliceRun extension
        (by intro function args origin impossible; cases impossible) RVal.val (sourceFuel := 0) (by
          simp [sampled, execPure, getView_of viewCell, evalBnd]))
    have sourceMonotone : FuelMonotone (fun _ : Nat => (pure (Val.slice location start length) : M Val)) := by
      intro n k bound
      exact MonoM.refl _
    have continuationMonotone : ∀ value, FuelMonotone (fun _ : Nat => (pure value : M Val)) := by
      intro value n k bound
      exact MonoM.refl _
    exact first.bind second sourceMonotone continuationMonotone

end Goose.Lower
