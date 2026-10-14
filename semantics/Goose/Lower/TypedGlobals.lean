import Goose.Lower.TypedExpressions
import Goose.Lower.SourceContexts
import Goose.Lower.FunctionTail

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower

theorem typedGlobal_simulation {cfg : Cfg} {globalId : GlobalId} {global : Core.Global}
    {state : St} {n : Nat}
    (accepted : Core.validate cfg.mod = .ok ())
    (globalAt : cfg.mod.globals[globalId]? = some global)
    (invariant : Core.Sound.StoreInv cfg.mod globalId state)
    (hexpr : TypedExprClaim n cfg [global.ty] global.init) :
    EventualM (freshAct >>= fun act => evalExpr n cfg ⟨#[], act, [], 0⟩ global.init)
      (fun fuel => enterFn fuel ⟨cfg.profile, lower cfg.mod⟩ 0 (lowerGlobal cfg.mod global).init []) state := by
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
  have simulation := hexpr ⟨#[], state.nextAct, [], 0⟩
    { state with nextAct := state.nextAct + 1 } source metadata startLS middle id (0, 0) cx frame
    evaluated startLS_pp extendedMiddle related rfl rfl
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

end Goose.Lower
