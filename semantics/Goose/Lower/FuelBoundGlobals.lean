import Goose.Lower.FuelBoundCallEntry
import Goose.Lower.TypedGlobals

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower Goose.Proofs.Fuel

theorem typedGlobal_fuelBound {cfg : Cfg} {globalId : GlobalId} {global : Core.Global}
    {state : St} {sourceFuel fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (globalAt : cfg.mod.globals[globalId]? = some global)
    (invariant : Core.Sound.StoreInv cfg.mod globalId state)
    (expression : TypedExprFuelBound sourceFuel fuel cfg [global.ty] global.init) :
    FuelBoundM sourceFuel (fuel + 1)
      (fun n => freshAct >>= fun act => evalExpr n cfg ⟨#[],act,[],0⟩ global.init)
      (fun n => enterFn n ⟨cfg.profile,lower cfg.mod⟩ 0 (lowerGlobal cfg.mod global).init []) state := by
  obtain ⟨source, typingEq, rootsEq, _, _⟩ := acceptedGlobalActivation accepted globalAt invariant
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
  exact completed result nonTimeout run

theorem typedInitializers_fuelBound {cfg : Cfg} {sourceFuel fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ (id : GlobalId) (global : Core.Global), cfg.mod.globals[id]? = some global →
      TypedExprFuelBound sourceFuel fuel cfg [global.ty] global.init) (count : Nat) :
    ∀ first state, first + count ≤ cfg.mod.globals.size →
      InitializedGlobals cfg.mod first state →
      FuelBoundM sourceFuel (fuel + 1) (fun n => Core.initGlobals n cfg (List.range' first count))
        (fun n => GIR.initGlobals n ⟨cfg.profile,lower cfg.mod⟩ (List.range' first count)) state := by
  induction count with
  | zero =>
    intro first state bounded initialized
    simp only [List.range'_zero,Core.initGlobals,GIR.initGlobals]
    exact FuelBoundM.of_eq rfl
  | succ count previous =>
    intro first state bounded initialized
    have present : first < cfg.mod.globals.size := by omega
    let global := cfg.mod.globals[first]
    have globalAt : cfg.mod.globals[first]? = some global := by simp [global,present]
    have loweredAt : (lower cfg.mod).globals[first]? = some (lowerGlobal cfg.mod global) := by
      simp [lower,Array.getElem?_map,globalAt]
    simp only [List.range'_succ,Core.initGlobals,GIR.initGlobals,Core.lookupGlobal,
      GIR.lookupInit,globalAt,loweredAt,pure_bind]
    refine FuelBoundM.bind_success
      (typedGlobal_fuelBound accepted globalAt initialized.invariant (expressions first global globalAt)) ?_
    intro value after evaluated
    have nextInitialized := initialized.afterInitializer accepted globalAt sourceFuel evaluated
    refine FuelBoundM.bind_success (FuelBoundM.of_eq rfl) ?_
    intro ignored next bound
    have nextEq : next = {after with store := after.store.introduce (.global first) value} :=
      (Res.ok.inj bound).2.symm
    subst next
    exact previous (first + 1) _ (by omega) nextInitialized

theorem typedGlobals_fuelBound {cfg : Cfg} {sourceFuel fuel : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprFuelBound sourceFuel residual cfg [global.ty] global.init) :
    FuelBoundM sourceFuel fuel (fun n => Core.initGlobals n cfg (List.range cfg.mod.globals.size))
      (fun n => GIR.initGlobals n ⟨cfg.profile,lower cfg.mod⟩ (List.range cfg.mod.globals.size)) St.initial := by
  cases fuel with
  | succ fuel =>
    simpa only [List.range_eq_range'] using typedInitializers_fuelBound accepted (expressions fuel rfl)
      cfg.mod.globals.size 0 St.initial (by omega) (InitializedGlobals.initial _)
  | zero =>
    cases count : cfg.mod.globals.size with
    | zero =>
      simp only [count,List.range_zero,Core.initGlobals,GIR.initGlobals]
      exact FuelBoundM.of_eq rfl
    | succ count =>
      have present : 0 < cfg.mod.globals.size := by omega
      have globalAt : cfg.mod.globals[0]? = some cfg.mod.globals[0] := by simp [present]
      have loweredAt : (lower cfg.mod).globals[0]? = some (lowerGlobal cfg.mod cfg.mod.globals[0]) := by
        simp [lower,Array.getElem?_map,globalAt]
      apply FuelBoundM.of_timeout
      simp only [List.range_eq_range',count,List.range'_succ,GIR.initGlobals,GIR.lookupInit,
        loweredAt,pure_bind,enterFn,bind_apply]
      rfl

end Goose.Lower
