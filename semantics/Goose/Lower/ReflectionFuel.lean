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

theorem ReflectMFuel.map {source target : Nat → M α} {state : St} {fuel : Nat}
    (reflection : ReflectMFuel fuel source target state) (inject : α → β) :
    ReflectMFuel fuel (fun n => source n >>= fun value => pure (inject value))
      (fun n => target n >>= fun value => pure (inject value)) state := by
  intro result hresult htarget
  change (target fuel >>= fun value => pure (inject value)) state = result at htarget
  change ∃ n, (source n >>= fun value => pure (inject value)) state = result
  rw [bind_apply] at htarget
  cases ht : target fuel state with
  | ok value after =>
      rw [ht] at htarget
      obtain ⟨n,hn⟩ := reflection (.ok value after) (NonTimeout.ok _ _) ht
      exact ⟨n,by rw [bind_apply, hn]; exact htarget⟩
  | stop stop after =>
      rw [ht] at htarget
      have hnon : NonTimeout (Res.stop stop after : Res α) := by
        intro s h
        cases h
        exact hresult after htarget.symm
      obtain ⟨n,hn⟩ := reflection (.stop stop after) hnon ht
      exact ⟨n,by rw [bind_apply, hn]; exact htarget⟩


theorem ReflectMFuel.of_timeout {source target : Nat → M α} {state after : St} {fuel : Nat}
    (stopped : target fuel state = .stop .timeout after) :
    ReflectMFuel fuel source target state := by
  intro result nonTimeout run
  exact (nonTimeout after (run.symm.trans stopped)).elim

theorem ReflectAtFuel.of_source {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source other : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St} {fuel : Nat}
    (reflection : ReflectAtFuel fuel cx pt fr source post state)
    (equal : ∀ n, ∃ k, other k state = source n state) :
    ReflectAtFuel fuel cx pt fr other post state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout run with success | stopped
  · obtain ⟨n,value,after,pt',fr',residual,sourceRun,matched,bound,targetRun⟩ := success
    obtain ⟨k,equal⟩ := equal n
    exact Or.inl ⟨k,value,after,pt',fr',residual,equal.trans sourceRun,matched,bound,targetRun⟩
  · obtain ⟨n,stop,after,sourceRun,targetRun⟩ := stopped
    obtain ⟨k,equal⟩ := equal n
    exact Or.inr ⟨k,stop,after,equal.trans sourceRun,targetRun⟩

theorem runAt_condbr_step {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {condition : ValueId}
    {yes no : BlockId} {yesBlock noBlock : GIR.Block} {selected : Bool}
    (instruction : instAt cx.fn pt = some (.term (.condbr condition yes [] no [])))
    (value : fr.vals[condition]? = some (.val (.bool selected)))
    (yesAt : cx.fn.blocks[yes]? = some yesBlock) (yesParameters : yesBlock.params = [])
    (noAt : cx.fn.blocks[no]? = some noBlock) (noParameters : noBlock.params = []) (fuel : Nat) :
    runAt cx pt fr (fuel + 1) = runAt cx (if selected then (yes,0) else (no,0)) fr fuel := by
  unfold runAt
  rw [instsAt_cons instruction, exec]
  cases selected
  · simp only [getVal_of value, Core.expectBool, pure_bind, Bool.false_eq_true, ↓reduceIte,
      mapList, enterBlock, noAt, noParameters, List.length_nil, bindParams]
    have next : instsAt cx.fn (no,0) = noBlock.insts := by simp [instsAt, noAt]
    rw [next]
  · simp only [getVal_of value, Core.expectBool, pure_bind, ↓reduceIte,
      mapList, enterBlock, yesAt, yesParameters, List.length_nil, bindParams]
    have next : instsAt cx.fn (yes,0) = yesBlock.insts := by simp [instsAt, yesAt]
    rw [next]

theorem ReflectAtFuel.condbr {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {condition : ValueId}
    {yes no : BlockId} {yesBlock noBlock : GIR.Block} {selected : Bool}
    {source : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St} {fuel : Nat}
    (instruction : instAt cx.fn pt = some (.term (.condbr condition yes [] no [])))
    (value : fr.vals[condition]? = some (.val (.bool selected)))
    (yesAt : cx.fn.blocks[yes]? = some yesBlock) (yesParameters : yesBlock.params = [])
    (noAt : cx.fn.blocks[no]? = some noBlock) (noParameters : noBlock.params = [])
    (reflection : ReflectAtFuel fuel cx (if selected then (yes,0) else (no,0)) fr source post state) :
    ReflectAtFuel (fuel + 1) cx pt fr source post state :=
  ReflectAtFuel.step (congrFun
    (runAt_condbr_step instruction value yesAt yesParameters noAt noParameters fuel) state) reflection

theorem ReflectMFuel.call_op {cx : FnCtx} {fr : GIR.Frame} {callee : FnId}
    {args : List ValueId} {values : List Val} {origin : Option OriginId}
    {source : Nat → M Val} {state : St} {fuel : Nat}
    (arguments : mapList (getVal fr) args = pure values)
    (call : ReflectMFuel fuel source (fun n => callFn n cx.cfg fr.depth callee values) state) :
    ReflectMFuel (fuel + 1) (fun n => source n >>= fun value => pure (RVal.val value))
      (fun n => execOp n cx fr (.call callee args origin)) state := by
  intro result nonTimeout run
  have step : execOp (fuel + 1) cx fr (.call callee args origin) =
      (callFn fuel cx.cfg fr.depth callee values >>= fun value => pure (RVal.val value)) := by
    simp only [execOp, arguments, pure_bind]
  change execOp (fuel + 1) cx fr (.call callee args origin) state = result at run
  rw [step] at run
  exact call.map RVal.val result nonTimeout run

theorem ReflectAtFuel.bind {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source₁ : Nat → M α} {source₂ : α → Nat → M β}
    {p : α → St → Pt → GIR.Frame → Prop} {q : β → St → Pt → GIR.Frame → Prop} {state : St} {fuel : Nat}
    (first : ReflectAtFuel fuel cx pt fr source₁ p state)
    (second : ∀ n value after pt' fr', source₁ n state = .ok value after →
      p value after pt' fr' → ∀ residual, residual ≤ fuel →
      ReflectAtFuel residual cx pt' fr' (source₂ value) q after)
    (mono₁ : FuelMonotone source₁)
    (mono₂ : ∀ value, FuelMonotone (source₂ value)) :
    ReflectAtFuel fuel cx pt fr (fun n => source₁ n >>= fun value => source₂ value n) q state := by
  intro result hresult hrun
  rcases first result hresult hrun with h | h
  · obtain ⟨n,value,after,pt',fr',residual,hn,hp,hle,hr⟩ := h
    rcases second n value after pt' fr' hn hp residual hle result hresult hr with h | h
    · obtain ⟨k,value',after',pt'',fr'',residual',hk,hq,hle',hr'⟩ := h
      refine Or.inl ⟨max n k,value',after',pt'',fr'',residual',?_,hq,Nat.le_trans hle' hle,hr'⟩
      change (source₁ (max n k) >>= fun value => source₂ value (max n k)) state = _
      rw [bind_apply, (mono₁ n (max n k) (Nat.le_max_left _ _) state).1 value after hn]
      exact (mono₂ value k (max n k) (Nat.le_max_right _ _) after).1 value' after' hk
    · obtain ⟨k,stop,after',hk,hr'⟩ := h
      refine Or.inr ⟨max n k,stop,after',?_,hr'⟩
      change (source₁ (max n k) >>= fun value => source₂ value (max n k)) state = _
      rw [bind_apply, (mono₁ n (max n k) (Nat.le_max_left _ _) state).1 value after hn]
      exact ((mono₂ value k (max n k) (Nat.le_max_right _ _) after).2 stop after' hk).resolve_left
        (by cases stop <;> simp [isTimeout] at *; exact (hresult after' hr').elim)
  · obtain ⟨n,stop,after,hn,hr⟩ := h
    refine Or.inr ⟨n,stop,after,?_,hr⟩
    change (source₁ n >>= fun value => source₂ value n) state = _
    rw [bind_apply, hn]

end Goose.Lower
