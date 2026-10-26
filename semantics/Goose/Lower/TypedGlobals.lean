import Goose.Lower.TypedExpressions
import Goose.Lower.SourceContexts
import Goose.Lower.FunctionTail

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower

theorem startLS_generated : GeneratedBuilderState startLS := by
  refine ⟨?_, ?_, ?_⟩
  · simp [startLS, LS.DenseDefinitions, LS.defs, BlockB.defs]
  · intro block current
    change some 0 = some block at current
    cases current
    decide
  · intro index block row target successor
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    have zero : index = 0 := by
      change index < 1 at bound
      nat_omega
    subst index
    have equal : block = ⟨[], #[]⟩ := (Option.some.inj row).symm
    subst block
    simp [Validation.cfgBlock, GIR.Block.terms] at successor

theorem typedGlobal_simulation {cfg : Cfg} {globalId : GlobalId} {global : Core.Global}
    {state : St} {n : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (globalAt : cfg.mod.globals[globalId]? = some global)
    (invariant : Core.Sound.StoreInv cfg.mod globalId state)
    (hexpr : TypedExprClaim n cfg [global.ty] global.init) :
    EventualM (freshAct >>= fun act => evalExpr n cfg ⟨#[], act, [], 0⟩ global.init)
      (fun fuel => enterFn fuel ⟨cfg.profile, lower cfg.mod⟩ 0 (lowerGlobal cfg.mod global).init []) state := by
  obtain ⟨source, typingEq, rootsEq, _, _, _⟩ := acceptedGlobalActivation accepted globalAt invariant
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
  have simulation := hexpr ⟨#[], state.nextAct, [], 0⟩
    { state with nextAct := state.nextAct + 1 } source metadata startLS middle id (0, 0) cx frame
    evaluated startLS_pp extendedMiddle related rfl rfl startLS_generated
  have completed := simulation.complete_ret1 (r := id) (org := some global.org)
    (fun value _ point endpoint _ P => by
      obtain ⟨_, _, _, instruction⟩ := emitTerm_facts terminated P.pp extendedFinal
      exact ⟨instruction, P.has (id, .val value) (by simp)⟩)
  refine ⟨?_, ?_⟩
  · intro value after done
    obtain ⟨K, run⟩ := completed.1 value after done
    refine ⟨K + 1, fun fuel enough => ?_⟩
    obtain ⟨remaining, rfl⟩ : ∃ remaining, fuel = remaining + 1 := ⟨fuel - 1, by omega⟩
    change enterFn (remaining + 1) ⟨cfg.profile, lower cfg.mod⟩ 0
      (lowerGlobal cfg.mod global).init [] state = _
    rw [enterFn_nil _ _ _ _ _ rfl entryAt entryParams]
    exact run remaining (by omega)
  · intro reason after done finalReason
    obtain ⟨K, run⟩ := completed.2 reason after done finalReason
    refine ⟨K + 1, fun fuel enough => ?_⟩
    obtain ⟨remaining, rfl⟩ : ∃ remaining, fuel = remaining + 1 := ⟨fuel - 1, by omega⟩
    change enterFn (remaining + 1) ⟨cfg.profile, lower cfg.mod⟩ 0
      (lowerGlobal cfg.mod global).init [] state = _
    rw [enterFn_nil _ _ _ _ _ rfl entryAt entryParams]
    exact run remaining (by omega)

theorem typedInitializers_simulation {cfg : Cfg} (n : Nat)
    (accepted : Core.validate cfg.mod = .ok ())
    (hexpr : ∀ (id : GlobalId) (global : Core.Global), cfg.mod.globals[id]? = some global →
      TypedExprClaim n cfg [global.ty] global.init) (count : Nat) :
    ∀ first state, first + count ≤ cfg.mod.globals.size →
      InitializedGlobals cfg.mod first state →
      EventualM (Core.initGlobals n cfg (List.range' first count))
        (fun fuel => GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range' first count)) state := by
  induction count with
  | zero =>
    intro first state bounded initialized
    simp only [List.range'_zero, Core.initGlobals, GIR.initGlobals]
    exact EventualM.refl _ _
  | succ count previous =>
    intro first state bounded initialized
    have present : first < cfg.mod.globals.size := by omega
    let global := cfg.mod.globals[first]
    have globalAt : cfg.mod.globals[first]? = some global := by simp [global, present]
    have loweredAt : (lower cfg.mod).globals[first]? = some (lowerGlobal cfg.mod global) := by
      simp [lower, Array.getElem?_map, globalAt]
    simp only [List.range'_succ, Core.initGlobals, GIR.initGlobals, Core.lookupGlobal,
      GIR.lookupInit, globalAt, loweredAt, pure_bind, bind_assoc]
    refine EventualM.bind (typedGlobal_simulation accepted globalAt initialized.invariant
      (hexpr first global globalAt)) fun value after evaluated => ?_
    have nextInitialized := initialized.afterInitializer accepted globalAt n evaluated
    refine EventualM.bind (EventualM.refl (bindRoot (.global first) value) after)
      fun unit next bound => ?_
    have nextEq : next = { after with store := after.store.introduce (.global first) value } := by
      exact (Res.ok.inj bound).2.symm
    subst next
    exact previous (first + 1) _ (by omega) nextInitialized


theorem typedGlobals_simulation {cfg : Cfg} (n : Nat)
    (accepted : Core.validate cfg.mod = .ok ())
    (hexpr : ∀ (id : GlobalId) (global : Core.Global), cfg.mod.globals[id]? = some global →
      TypedExprClaim n cfg [global.ty] global.init) :
    EventualM (Core.initGlobals n cfg (List.range cfg.mod.globals.size))
      (fun fuel => GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩
        (List.range cfg.mod.globals.size)) St.initial := by
  simpa only [List.range_eq_range'] using
    typedInitializers_simulation n accepted hexpr cfg.mod.globals.size 0 St.initial
      (by omega) (InitializedGlobals.initial _)


end Goose.Lower
