import Goose.Lower.Eventual

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def FuelBoundM (sourceFuel targetFuel : Nat) (source target : Nat → M α) (state : St) : Prop :=
  ∀ result, NonTimeout result → target targetFuel state = result →
    source sourceFuel state = result

def FuelBoundAt (sourceFuel targetFuel : Nat) (cx : FnCtx) (pt : Pt) (fr : GIR.Frame)
    (source : Nat → M α) (post : α → St → Pt → GIR.Frame → Prop) (state : St) : Prop :=
  ∀ result, NonTimeout result → runAt cx pt fr targetFuel state = result →
    (∃ value after pt' fr' residual,
      source sourceFuel state = .ok value after ∧ post value after pt' fr' ∧
      residual ≤ targetFuel ∧ runAt cx pt' fr' residual after = result) ∨
    (∃ stop after, source sourceFuel state = .stop stop after ∧ result = .stop stop after)

theorem FuelBoundAt.zero (sourceFuel : Nat) (cx : FnCtx) (pt : Pt) (fr : GIR.Frame)
    (source : Nat → M α) (post : α → St → Pt → GIR.Frame → Prop) (state : St) :
    FuelBoundAt sourceFuel 0 cx pt fr source post state := by
  intro result final done
  exact (final state (done.symm.trans rfl)).elim

theorem FuelBoundAt.ret {sourceFuel targetFuel : Nat} {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {value : α} {post : α → St → Pt → GIR.Frame → Prop} {state : St}
    (matched : post value state pt fr) :
    FuelBoundAt sourceFuel targetFuel cx pt fr (fun _ => pure value) post state := by
  intro result final done
  exact Or.inl ⟨value,state,pt,fr,targetFuel,rfl,matched,Nat.le_refl _,done⟩

theorem FuelBoundAt.mono {sourceFuel targetFuel : Nat} {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source : Nat → M α} {p q : α → St → Pt → GIR.Frame → Prop} {state : St}
    (bounded : FuelBoundAt sourceFuel targetFuel cx pt fr source p state)
    (weaken : ∀ value after pt' fr', p value after pt' fr' → q value after pt' fr') :
    FuelBoundAt sourceFuel targetFuel cx pt fr source q state := by
  intro result final done
  rcases bounded result final done with success | stopped
  · obtain ⟨value,after,pt',fr',residual,run,matched,bound,continuation⟩ := success
    exact Or.inl ⟨value,after,pt',fr',residual,run,weaken _ _ _ _ matched,bound,continuation⟩
  · exact Or.inr stopped

theorem FuelBoundAt.of_source {sourceFuel otherFuel targetFuel : Nat}
    {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {source other : Nat → M α}
    {post : α → St → Pt → GIR.Frame → Prop} {state : St}
    (bounded : FuelBoundAt sourceFuel targetFuel cx pt fr source post state)
    (equal : other otherFuel state = source sourceFuel state) :
    FuelBoundAt otherFuel targetFuel cx pt fr other post state := by
  intro result final done
  rcases bounded result final done with success | stopped
  · obtain ⟨value,after,pt',fr',residual,run,matched,bound,continuation⟩ := success
    exact Or.inl ⟨value,after,pt',fr',residual,equal.trans run,matched,bound,continuation⟩
  · obtain ⟨stop,after,run,equalResult⟩ := stopped
    exact Or.inr ⟨stop,after,equal.trans run,equalResult⟩

theorem FuelBoundAt.source_mono {sourceFuel larger targetFuel : Nat}
    {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {source : Nat → M α}
    {post : α → St → Pt → GIR.Frame → Prop} {state : St}
    (bounded : FuelBoundAt sourceFuel targetFuel cx pt fr source post state)
    (monotone : ∀ n k, n ≤ k → MonoM (source n) (source k)) (enough : sourceFuel ≤ larger) :
    FuelBoundAt larger targetFuel cx pt fr source post state := by
  intro result final done
  rcases bounded result final done with success | stopped
  · obtain ⟨value,after,pt',fr',residual,run,matched,bound,continuation⟩ := success
    exact Or.inl ⟨value,after,pt',fr',residual,
      (monotone _ _ enough state).1 value after run,matched,bound,continuation⟩
  · obtain ⟨stop,after,run,equal⟩ := stopped
    have nonTimeout : ¬ isTimeout stop := by
      cases stop <;> simp [isTimeout]
      exact (final after equal).elim
    exact Or.inr ⟨stop,after,((monotone _ _ enough state).2 stop after run).resolve_left nonTimeout,equal⟩

theorem FuelBoundAt.step {sourceFuel targetFuel : Nat} {cx : FnCtx} {pt next : Pt}
    {fr nextFrame : GIR.Frame} {source : Nat → M α}
    {post : α → St → Pt → GIR.Frame → Prop} {state : St}
    (step : runAt cx pt fr (targetFuel + 1) state = runAt cx next nextFrame targetFuel state)
    (bounded : FuelBoundAt sourceFuel targetFuel cx next nextFrame source post state) :
    FuelBoundAt sourceFuel (targetFuel + 1) cx pt fr source post state := by
  intro result final done
  rcases bounded result final (step.symm.trans done) with success | stopped
  · obtain ⟨value,after,pt',fr',residual,run,matched,bound,continuation⟩ := success
    exact Or.inl ⟨value,after,pt',fr',residual,run,matched,by omega,continuation⟩
  · exact Or.inr stopped

theorem FuelBoundAt.bind {sourceFuel targetFuel : Nat} {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {first : Nat → M α} {second : α → Nat → M β}
    {p : α → St → Pt → GIR.Frame → Prop} {q : β → St → Pt → GIR.Frame → Prop} {state : St}
    (left : FuelBoundAt sourceFuel targetFuel cx pt fr first p state)
    (right : ∀ value after pt' fr', first sourceFuel state = .ok value after →
      p value after pt' fr' → ∀ residual, residual ≤ targetFuel →
      FuelBoundAt sourceFuel residual cx pt' fr' (second value) q after) :
    FuelBoundAt sourceFuel targetFuel cx pt fr
      (fun n => first n >>= fun value => second value n) q state := by
  intro result final done
  rcases left result final done with success | stopped
  · obtain ⟨value,after,pt',fr',residual,run,matched,bound,continuation⟩ := success
    rcases right value after pt' fr' run matched residual bound result final continuation with success | stopped
    · obtain ⟨value',after',pt'',fr'',residual',run',matched',bound',continuation'⟩ := success
      refine Or.inl ⟨value',after',pt'',fr'',residual',?_,matched',Nat.le_trans bound' bound,continuation'⟩
      change (first sourceFuel >>= fun value => second value sourceFuel) state = _
      rw [bind_apply,run]
      exact run'
    · obtain ⟨stop,after',run',equal⟩ := stopped
      refine Or.inr ⟨stop,after',?_,equal⟩
      change (first sourceFuel >>= fun value => second value sourceFuel) state = _
      rw [bind_apply,run]
      exact run'
  · obtain ⟨stop,after,run,equal⟩ := stopped
    refine Or.inr ⟨stop,after,?_,equal⟩
    change (first sourceFuel >>= fun value => second value sourceFuel) state = _
    rw [bind_apply,run]

theorem FuelBoundAt.def_step {sourceFuel targetFuel : Nat} {cx : FnCtx} {pt : Pt}
    {fr : GIR.Frame} {source : Nat → M α} {state : St} {resultId : ValueId} {op : Op}
    (inject : α → RVal) (instruction : instAt cx.fn pt = some (.def resultId op))
    (operation : FuelBoundM sourceFuel targetFuel
      (fun n => source n >>= fun value => pure (inject value)) (fun n => execOp n cx fr op) state) :
    FuelBoundAt sourceFuel (targetFuel + 1) cx pt fr source
      (fun value _ pt' fr' => pt' = (pt.1,pt.2 + 1) ∧ fr' = fr.set resultId (inject value)) state := by
  intro result final done
  have step : runAt cx pt fr (targetFuel + 1) state =
      (execOp targetFuel cx fr op >>= fun value =>
        runAt cx (pt.1,pt.2 + 1) (fr.set resultId value) targetFuel) state := by
    simp only [runAt,instsAt_cons instruction,exec,setCell_eq,pure_bind]
  rw [step,bind_apply] at done
  cases operationRun : execOp targetFuel cx fr op state with
  | ok value after =>
    rw [operationRun] at done
    have sourceRun := operation (.ok value after) (NonTimeout.ok _ _) operationRun
    change (source sourceFuel >>= fun value => pure (inject value)) state = _ at sourceRun
    rw [bind_apply] at sourceRun
    cases run : source sourceFuel state with
    | stop stop stopped => rw [run] at sourceRun; cases sourceRun
    | ok sourceValue sourceAfter =>
      rw [run] at sourceRun
      cases sourceRun
      exact Or.inl ⟨sourceValue,after,_,_,targetFuel,rfl,⟨rfl,rfl⟩,by omega,done⟩
  | stop stop after =>
    rw [operationRun] at done
    have nonTimeout : NonTimeout (Res.stop stop after : Res RVal) := by
      intro failed impossible
      cases impossible
      exact final after done.symm
    have sourceRun := operation (.stop stop after) nonTimeout operationRun
    change (source sourceFuel >>= fun value => pure (inject value)) state = _ at sourceRun
    rw [bind_apply] at sourceRun
    cases run : source sourceFuel state with
    | ok sourceValue sourceAfter => rw [run] at sourceRun; cases sourceRun
    | stop sourceStop sourceAfter =>
      rw [run] at sourceRun
      cases sourceRun
      exact Or.inr ⟨stop,after,rfl,done.symm⟩

end Goose.Lower
