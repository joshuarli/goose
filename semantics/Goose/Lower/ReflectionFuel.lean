import Goose.Lower.ReflectionSteps

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem ReflectM.at_fuel {source target : Nat → M α} {state : St}
    (reflection : ReflectM source target state) (fuel : Nat) :
    ReflectMFuel fuel source target state := reflection fuel

theorem ReflectAt.at_fuel {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St}
    (reflection : ReflectAt cx pt fr source post state) (fuel : Nat) :
    ReflectAtFuel fuel cx pt fr source post state := reflection fuel

theorem ReflectMFuel.of_eq {source target : Nat → M α} {state : St} {fuel sourceFuel : Nat}
    (equal : target fuel state = source sourceFuel state) :
    ReflectMFuel fuel source target state := by
  intro result _ run
  exact ⟨sourceFuel, equal.symm.trans run⟩

theorem ReflectAtFuel.zero (cx : FnCtx) (pt : Pt) (fr : GIR.Frame) (source : Nat → M α)
    (post : α → St → Pt → GIR.Frame → Prop) (state : St) :
    ReflectAtFuel 0 cx pt fr source post state := by
  intro result nonTimeout run
  exact (nonTimeout state (run.symm.trans rfl)).elim

theorem ReflectAtFuel.ret {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {value : α} {state : St}
    {post : α → St → Pt → GIR.Frame → Prop} (fuel : Nat) (matched : post value state pt fr) :
    ReflectAtFuel fuel cx pt fr (fun _ => pure value) post state :=
  (ReflectAt.ret matched) fuel

theorem ReflectAtFuel.mono {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {source : Nat → M α}
    {p q : α → St → Pt → GIR.Frame → Prop} {state : St} {fuel : Nat}
    (reflection : ReflectAtFuel fuel cx pt fr source p state)
    (weaken : ∀ value after pt' fr', p value after pt' fr' → q value after pt' fr') :
    ReflectAtFuel fuel cx pt fr source q state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout run with success | stopped
  · obtain ⟨n,value,after,pt',fr',residual,sourceRun,matched,bound,targetRun⟩ := success
    exact Or.inl ⟨n,value,after,pt',fr',residual,sourceRun,weaken _ _ _ _ matched,bound,targetRun⟩
  · exact Or.inr stopped

theorem ReflectAtFuel.step {cx : FnCtx} {pt next : Pt} {fr nextFrame : GIR.Frame}
    {source : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St} {fuel : Nat}
    (step : runAt cx pt fr (fuel + 1) state = runAt cx next nextFrame fuel state)
    (reflection : ReflectAtFuel fuel cx next nextFrame source post state) :
    ReflectAtFuel (fuel + 1) cx pt fr source post state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout (step.symm.trans run) with success | stopped
  · obtain ⟨n,value,after,pt',fr',residual,sourceRun,matched,bound,targetRun⟩ := success
    exact Or.inl ⟨n,value,after,pt',fr',residual,sourceRun,matched,by omega,targetRun⟩
  · exact Or.inr stopped

theorem runAt_br0_step {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {blockId : BlockId} {block : GIR.Block}
    (instruction : instAt cx.fn pt = some (.term (.br blockId [])))
    (blockAt : cx.fn.blocks[blockId]? = some block) (parameters : block.params = []) (fuel : Nat) :
    runAt cx pt fr (fuel + 1) = runAt cx (blockId,0) fr fuel := by
  unfold runAt
  rw [instsAt_cons instruction, exec]
  simp only [mapList, pure_bind, enterBlock, blockAt, parameters, List.length_nil, ↓reduceIte, bindParams]
  have next : instsAt cx.fn (blockId,0) = block.insts := by simp [instsAt, blockAt]
  rw [next]

theorem ReflectAtFuel.br0 {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {blockId : BlockId} {block : GIR.Block}
    {source : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St} {fuel : Nat}
    (instruction : instAt cx.fn pt = some (.term (.br blockId [])))
    (blockAt : cx.fn.blocks[blockId]? = some block) (parameters : block.params = [])
    (reflection : ReflectAtFuel fuel cx (blockId,0) fr source post state) :
    ReflectAtFuel (fuel + 1) cx pt fr source post state :=
  ReflectAtFuel.step (congrFun (runAt_br0_step instruction blockAt parameters fuel) state) reflection

theorem ReflectAtFuel.def_step {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source : Nat → M α} {state : St} {fuel : Nat} {resultId : ValueId} {op : Op}
    (inject : α → RVal) (instruction : instAt cx.fn pt = some (.def resultId op))
    (operation : ReflectMFuel fuel (fun n => source n >>= fun value => pure (inject value))
      (fun n => execOp n cx fr op) state) :
    ReflectAtFuel (fuel + 1) cx pt fr source
      (fun value _ pt' fr' => pt' = (pt.1,pt.2 + 1) ∧ fr' = fr.set resultId (inject value)) state := by
  intro result hresult hrun
  have hstep : runAt cx pt fr (fuel + 1) state =
      (execOp fuel cx fr op >>= fun value =>
        runAt cx (pt.1,pt.2 + 1) (fr.set resultId value) fuel) state := by
    simp only [runAt, instsAt_cons instruction, exec, setCell_eq, pure_bind]
  rw [hstep, bind_apply] at hrun
  cases ho : execOp fuel cx fr op state with
  | ok value after =>
      rw [ho] at hrun
      obtain ⟨n,hn⟩ := operation (.ok value after) (NonTimeout.ok _ _) ho
      change (source n >>= fun value => pure (inject value)) state = .ok value after at hn
      rw [bind_apply] at hn
      cases hs : source n state with
      | stop stop stopped => rw [hs] at hn; cases hn
      | ok sourceValue sourceAfter =>
          rw [hs] at hn
          cases hn
          exact Or.inl ⟨n,sourceValue,after,(pt.1,pt.2 + 1),
            fr.set resultId (inject sourceValue),fuel,hs,⟨rfl,rfl⟩,by omega,hrun⟩
  | stop stop after =>
      rw [ho] at hrun
      have hnon : NonTimeout (Res.stop stop after : Res RVal) := by
        intro s h
        cases h
        exact hresult after hrun.symm
      obtain ⟨n,hn⟩ := operation (.stop stop after) hnon ho
      change (source n >>= fun value => pure (inject value)) state = .stop stop after at hn
      rw [bind_apply] at hn
      cases hs : source n state with
      | ok sourceValue sourceAfter => rw [hs] at hn; cases hn
      | stop sourceStop sourceAfter =>
          rw [hs] at hn
          cases hn
          exact Or.inr ⟨n,stop,after,hs,hrun.symm⟩

end Goose.Lower
