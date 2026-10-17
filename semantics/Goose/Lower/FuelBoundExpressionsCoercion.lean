import Goose.Lower.Coerce
import Goose.Lower.FuelBoundLeaves

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private theorem FuelBoundAt.pure_result_eq {sourceFuel fuel : Nat} {cx : FnCtx} {pt : Pt}
    {fr : Frame} {value : α} {state : St} {post : α → St → Pt → Frame → Prop}
    (reflection : FuelBoundAt sourceFuel fuel cx pt fr (fun _ => pure value) post state) :
    FuelBoundAt sourceFuel fuel cx pt fr (fun _ => pure value)
      (fun result after pt' fr' => result = value ∧ post result after pt' fr') state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout run with success | stopped
  · obtain ⟨sourceValue, after, pt', fr', residual, sourceRun, matched, bound, targetRun⟩ := success
    have sourceValueEq : sourceValue = value := by
      change Res.ok value state = Res.ok sourceValue after at sourceRun
      exact (Res.ok.inj sourceRun).1.symm
    exact Or.inl ⟨sourceValue, after, pt', fr', residual, sourceRun,
      ⟨sourceValueEq, matched⟩, bound, targetRun⟩
  · exact Or.inr stopped

theorem coerceTo_fuelBoundAt {sourceFuel fuel : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv}
    {base ls ls' : LS} {before fr : Frame} {pt : Pt} {r r' : ValueId} {target : Ty}
    {value : Val} {org : OriginId} {state : St}
    (beforePost : Post cfg env cx base before ls fr pt [(r, .val value)])
    (shape : CoercionValue target value)
    (lowering : coerceTo target r org le ls = (r', ls'))
    (extension : ExtT ls' cx.fn.blocks) :
    FuelBoundAt sourceFuel fuel cx pt fr (fun _ => pure value)
      (fun result _ pt' fr' => result = value ∧
        Post cfg env cx base before ls' fr' pt' [(r', .val result)]) state := by
  rcases coerceTo_cases lowering with ⟨result, finish⟩ | ⟨elem, targetEq, freeze⟩ |
      ⟨elem, view, middle, targetEq, viewRun, sliceRun⟩
  · subst r'
    subst ls'
    exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := fuel) ⟨rfl, beforePost⟩
  · subst target
    obtain ⟨location, valueEq⟩ := shape
    subst value
    have cell := beforePost.has (r, .val (.ref location)) (by simp)
    exact FuelBoundAt.pure_result_eq (leaf_def_fuelBoundAt (fuel := fuel)
      (source := fun _ : Nat => pure (Val.ref location))
      (state := state) beforePost freeze extension
      (by intro function args origin impossible; cases impossible) RVal.val (sourceFuel := sourceFuel) (by
        simp only [execPure, getVal_of cell, expectRef, pure_bind]))
  · subst target
    obtain ⟨location, start, length, valueEq⟩ := shape
    subst value
    have cell := beforePost.has (r, .val (.slice location start length)) (by simp)
    have middleExtension := extension.of_adv (adv_emitDef sliceRun)
    let sampled : ViewVal := ⟨location, start, length, false⟩
    have first := leaf_def_fuelBoundAt (fuel := fuel) (state := state)
        (source := fun _ : Nat => (pure (Val.slice location start length) : M Val))
        beforePost viewRun middleExtension
        (by intro function args origin impossible; cases impossible) (fun _ => .view sampled)
        (sourceFuel := sourceFuel) (by
          simp only [execPure, getVal_of cell, expectSlice, pure_bind]
          simp [sampled])
    have first := FuelBoundAt.pure_result_eq first
    have second : ∀ value after pt' fr',
          (pure (Val.slice location start length) : M Val) state = Res.ok value after →
          (value = .slice location start length ∧
            Post cfg env cx base before middle fr' pt' [(view, .view sampled)]) →
          ∀ residual, residual ≤ fuel →
            FuelBoundAt sourceFuel residual cx pt' fr' (fun _ : Nat => (pure value : M Val))
              (fun result _ pt'' fr'' => result = Val.slice location start length ∧
                Post cfg env cx base before ls' fr'' pt'' [(r', .val result)]) after := by
      intro value after pt' fr' _ matched residual bound
      rcases matched with ⟨valueEq, viewPost⟩
      subst value
      have viewCell := viewPost.has (view, .view sampled) (by simp)
      exact FuelBoundAt.pure_result_eq (leaf_def_fuelBoundAt (fuel := residual)
        (source := fun _ : Nat => (pure (Val.slice location start length) : M Val))
        (state := after) viewPost sliceRun extension
        (by intro function args origin impossible; cases impossible) RVal.val (sourceFuel := sourceFuel) (by
          simp [sampled, execPure, getView_of viewCell, evalBnd]))
    exact first.bind second

end Goose.Lower
