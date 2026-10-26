import Goose.Lower.ReflectionCallEntry
import Goose.Lower.TypedGlobals

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower Goose.Proofs.Fuel

theorem ReflectAtFuel.complete_value {cx : FnCtx} {pt : Pt} {fr : GIR.Frame}
    {source : Nat → M Val} {post : Val → St → Pt → GIR.Frame → Prop} {state : St} {fuel : Nat}
    (reflection : ReflectAtFuel fuel cx pt fr source post state)
    (terminal : ∀ value after pt' fr', post value after pt' fr' → ReturnEndpoint cx pt' fr' value) :
    ReflectMFuel fuel source (fun n => runAt cx pt fr n) state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout run with success | stopped
  · obtain ⟨n,value,after,pt',fr',residual,sourceRun,matched,bound,continuation⟩ := success
    have endpoint := terminal value after pt' fr' matched
    cases residual with
    | zero => exact (nonTimeout after (continuation.symm.trans rfl)).elim
    | succ extra =>
      have returned := endpoint.run after extra
      exact ⟨n,sourceRun.trans (continuation.symm.trans returned).symm⟩
  · obtain ⟨n,stop,after,sourceRun,targetRun⟩ := stopped
    exact ⟨n,sourceRun.trans targetRun.symm⟩

theorem ReflectMFuel.bind_success {source₁ target₁ : Nat → M α}
    {source₂ target₂ : α → Nat → M β} {state : St} {fuel : Nat}
    (first : ReflectMFuel fuel source₁ target₁ state)
    (second : ∀ n value after, source₁ n state = .ok value after →
      ReflectMFuel fuel (source₂ value) (target₂ value) after)
    (mono₁ : FuelMonotone source₁)
    (mono₂ : ∀ value, FuelMonotone (source₂ value)) :
    ReflectMFuel fuel (fun n => source₁ n >>= fun value => source₂ value n)
      (fun n => target₁ n >>= fun value => target₂ value n) state := by
  intro result nonTimeout run
  change (target₁ fuel >>= fun value => target₂ value fuel) state = result at run
  change ∃ n, (source₁ n >>= fun value => source₂ value n) state = result
  rw [bind_apply] at run
  cases firstRun : target₁ fuel state with
  | ok value after =>
    rw [firstRun] at run
    obtain ⟨n,sourceRun⟩ := first (.ok value after) (NonTimeout.ok _ _) firstRun
    obtain ⟨k,nextRun⟩ := second n value after sourceRun result nonTimeout run
    refine ⟨max n k,?_⟩
    rw [bind_apply,(mono₁ n (max n k) (Nat.le_max_left _ _) state).1 value after sourceRun]
    cases result with
    | ok value' after' => exact (mono₂ value k (max n k) (Nat.le_max_right _ _) after).1 value' after' nextRun
    | stop stop after' =>
      exact ((mono₂ value k (max n k) (Nat.le_max_right _ _) after).2 stop after' nextRun).resolve_left
        (by cases stop <;> simp [isTimeout] at *; exact (nonTimeout after' rfl).elim)
  | stop stop after =>
    rw [firstRun] at run
    have observed : NonTimeout (Res.stop stop after : Res α) := by
      intro next equal
      cases equal
      exact nonTimeout after run.symm
    obtain ⟨n,sourceRun⟩ := first (.stop stop after) observed firstRun
    exact ⟨n,by rw [bind_apply,sourceRun]; exact run⟩

theorem typedGlobal_reflection {cfg : Cfg} {globalId : GlobalId} {global : Core.Global}
    {state : St} {fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (globalAt : cfg.mod.globals[globalId]? = some global)
    (invariant : Core.Sound.StoreInv cfg.mod globalId state)
    (expression : TypedExprReflection fuel cfg [global.ty] global.init) :
    ReflectMFuel (fuel + 1)
      (fun n => freshAct >>= fun act => evalExpr n cfg ⟨#[],act,[],0⟩ global.init)
      (fun n => enterFn n ⟨cfg.profile,lower cfg.mod⟩ 0 (lowerGlobal cfg.mod global).init []) state := by
  obtain ⟨source, typingEq, rootsEq, _, _, _, _⟩ := acceptedGlobalActivation accepted globalAt invariant
  have metadata : SourceResults source.typingEnv source.rootsEnv [global.ty] := by
    intro impl selected
    rw [typingEq] at selected
    cases selected
  let le := lowerEnv cfg.mod #[] [global.ty]
  let lowered := lowerExpr global.init le startLS
  let id := lowered.1
  let middle := lowered.2
  have evaluated : lowerExpr global.init le startLS = (id, middle) := rfl
  let final := (emitTerm (.ret [id] (some global.org)) le middle).2
  have terminated : emitTerm (.ret [id] (some global.org)) le middle = ((), final) := rfl
  let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, (lowerGlobal cfg.mod global).init⟩
  have blocks : cx.fn.blocks = finishBlocks final.blocks := lowerGlobal_blocks cfg.mod global
  have extendedFinal : ExtT final cx.fn.blocks := by rw [blocks]; exact extT_finish final
  have extendedMiddle := extendedFinal.of_adv (adv_emitTerm terminated)
  have extendedInitial := extendedMiddle.of_adv (advB_lowerExpr global.init _ _ _ _ evaluated)
  obtain ⟨entryBlock, entryAt, entryParams⟩ := extendedInitial.params
    (b := 0) (blk := ⟨[], #[]⟩) rfl
  let frame : GIR.Frame := ⟨state.nextAct, [], {}, 0⟩
  have related : Rel cfg ⟨#[], state.nextAct, [], 0⟩ cx frame startLS :=
    ⟨rfl, by simp [cx, lowerGlobal], rfl, rfl, rfl, rfl⟩
  have simulation := expression ⟨#[], state.nextAct, [], 0⟩
    { state with nextAct := state.nextAct + 1 } source metadata startLS middle id (0, 0) cx frame
    evaluated startLS_pp extendedMiddle related rfl rfl startLS_generated
  have completed := simulation.complete_value (fun value _ point endpoint P => by
    obtain ⟨_,_,_,instruction⟩ := emitTerm_facts terminated P.pp extendedFinal
    exact ⟨[id],some global.org,instruction,Or.inr ⟨id,rfl,P.has (id,.val value) (by simp)⟩⟩)
  intro result nonTimeout run
  change enterFn (fuel + 1) ⟨cfg.profile,lower cfg.mod⟩ 0 cx.fn [] state = result at run
  rw [enterFn_nil _ _ _ _ _ rfl entryAt entryParams] at run
  obtain ⟨n,sourceRun⟩ := completed result nonTimeout run
  exact ⟨n,sourceRun⟩

theorem typedInitializers_reflection {cfg : Cfg} {fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ (id : GlobalId) (global : Core.Global), cfg.mod.globals[id]? = some global →
      TypedExprReflection fuel cfg [global.ty] global.init) (count : Nat) :
    ∀ first state, first + count ≤ cfg.mod.globals.size →
      InitializedGlobals cfg.mod first state →
      ReflectMFuel (fuel + 1) (fun n => Core.initGlobals n cfg (List.range' first count))
        (fun n => GIR.initGlobals n ⟨cfg.profile,lower cfg.mod⟩ (List.range' first count)) state := by
  induction count with
  | zero =>
    intro first state bounded initialized
    simp only [List.range'_zero,Core.initGlobals,GIR.initGlobals]
    exact ReflectMFuel.of_eq (sourceFuel := 0) rfl
  | succ count previous =>
    intro first state bounded initialized
    have present : first < cfg.mod.globals.size := by omega
    let global := cfg.mod.globals[first]
    have globalAt : cfg.mod.globals[first]? = some global := by simp [global,present]
    have loweredAt : (lower cfg.mod).globals[first]? = some (lowerGlobal cfg.mod global) := by
      simp [lower,Array.getElem?_map,globalAt]
    simp only [List.range'_succ,Core.initGlobals,GIR.initGlobals,Core.lookupGlobal,
      GIR.lookupInit,globalAt,loweredAt,pure_bind]
    refine ReflectMFuel.bind_success
      (typedGlobal_reflection accepted globalAt initialized.invariant (expressions first global globalAt)) ?_ ?_ ?_
    · intro n value after evaluated
      have nextInitialized := initialized.afterInitializer accepted globalAt n evaluated
      refine ReflectMFuel.bind_success (ReflectMFuel.of_eq (sourceFuel := 0) rfl) ?_
        (fun _ _ _ => MonoM.refl _) ?_
      · intro k ignored next bound
        have nextEq : next = {after with store := after.store.introduce (.global first) value} :=
          (Res.ok.inj bound).2.symm
        subst next
        exact previous (first + 1) _ (by omega) nextInitialized
      · intro ignored n k bound
        exact Goose.Proofs.Fuel.MonoM.initGlobals n k bound cfg _
    · intro n k bound
      exact MonoM.bind (MonoM.refl _) (fun act => (Goose.Proofs.Fuel.monoAll n k bound).expr cfg _ _)
    · intro value n k bound
      exact MonoM.bind (MonoM.refl _) (fun _ => Goose.Proofs.Fuel.MonoM.initGlobals n k bound cfg _)

theorem typedGlobals_reflection {cfg : Cfg} {fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init) :
    ReflectMFuel fuel (fun n => Core.initGlobals n cfg (List.range cfg.mod.globals.size))
      (fun n => GIR.initGlobals n ⟨cfg.profile,lower cfg.mod⟩ (List.range cfg.mod.globals.size)) St.initial := by
  cases fuel with
  | succ fuel =>
    simpa only [List.range_eq_range'] using typedInitializers_reflection accepted (expressions fuel rfl)
      cfg.mod.globals.size 0 St.initial (by omega) (InitializedGlobals.initial _)
  | zero =>
    cases count : cfg.mod.globals.size with
    | zero =>
      simp only [count,List.range_zero,Core.initGlobals,GIR.initGlobals]
      exact ReflectMFuel.of_eq (sourceFuel := 0) rfl
    | succ count =>
      have present : 0 < cfg.mod.globals.size := by omega
      have globalAt : cfg.mod.globals[0]? = some cfg.mod.globals[0] := by simp [present]
      have loweredAt : (lower cfg.mod).globals[0]? = some (lowerGlobal cfg.mod cfg.mod.globals[0]) := by
        simp [lower,Array.getElem?_map,globalAt]
      apply ReflectMFuel.of_timeout
      simp only [List.range_eq_range',count,List.range'_succ,GIR.initGlobals,GIR.lookupInit,
        loweredAt,pure_bind,enterFn,bind_apply]
      rfl

end Goose.Lower
