import Goose.Lower.Finish
import Goose.Lower.Leaf

namespace Goose.Proofs.Lower

open Goose.Core Goose.GIR Goose.Lower

theorem extT_finish (ls : LS) : ExtT ls (finishBlocks ls.blocks) := by
  refine ⟨by simp [finishBlocks], fun i blk hi => ?_⟩
  refine ⟨⟨blk.params, blk.insts.toList⟩, ?_, rfl, [], by simp⟩
  simp [finishBlocks, Array.getElem?_map, hi]

def bodyTail (impl : Impl) (le : LEnv) (v : ValueId) (ls1 : LS) : LS :=
  (finishFunction impl v le ls1).2

theorem bodyTail_cases (impl : Impl) (le : LEnv) (v : ValueId) (ls1 : LS)
    (hd : impl.body.diverges le.mod.noReturn = false) :
    (ls1.cur = none ∧ bodyTail impl le v ls1 = ls1) ∨
    (∃ b, ls1.cur = some b ∧
      emitTerm (.ret (if impl.body.value.isSome then [v] else []) none) le ls1 =
        ((), bodyTail impl le v ls1)) := by
  cases hc : ls1.cur with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    unfold bodyTail
    rw [finishFunction_nondivergent impl le ls1 v hd]
    simp [bind_run, isLive_none hc, pure_run]
  | some b =>
    right
    refine ⟨b, rfl, ?_⟩
    unfold bodyTail
    rw [finishFunction_nondivergent impl le ls1 v hd]
    simp [bind_run, isLive_run hc]

theorem enterFn_nil (cfg : GCfg) (fn : Func) (depth k0 : Nat) (s : St) {blk : GIR.Block}
    (hp : fn.params = []) (hb : fn.blocks[0]? = some blk) (hbp : blk.params = []) :
    enterFn (k0 + 1) cfg depth fn [] s =
      runAt ⟨cfg, fn⟩ (0, 0) ⟨s.nextAct, [], {}, depth⟩ k0 { s with nextAct := s.nextAct + 1 } := by
  have hi : instsAt fn (0, 0) = blk.insts := by simp [instsAt, hb]
  simp only [enterFn, hp, List.length_nil, List.map_nil, ↓reduceIte, enterBlock, hb, hbp, bindParams,
    pure_bind, runAt, hi]
  rfl

/-- The state at the start of a function whose entry block has no parameter. -/
def startLS : LS := { blocks := #[⟨[], #[]⟩], vals := #[], cur := some 0, stack := [] }

theorem startLS_pp : startLS.pp = some (0, 0) := rfl

theorem lowerGlobal_blocks (m : Core.Module) (g : Core.Global) :
    (lowerGlobal m g).init.blocks = finishBlocks (emitTerm
      (.ret [(lowerExpr g.init (lowerEnv m #[] [g.ty]) startLS).1] (some g.org)) (lowerEnv m #[] [g.ty])
      (lowerExpr g.init (lowerEnv m #[] [g.ty]) startLS).2).2.blocks := rfl

theorem lowerGlobal_blocks_nonempty (m : Core.Module) (g : Core.Global) :
    0 < (lowerGlobal m g).init.blocks.size := by
  let le := lowerEnv m #[] [g.ty]
  let run := lowerExpr g.init le startLS
  let v := run.1
  let ls1 := run.2
  have hlower : lowerExpr g.init le startLS = (v, ls1) := rfl
  have hadv1 : startLS.Adv ls1 := advB_lowerExpr g.init le startLS v ls1 hlower
  let endRun := emitTerm (.ret [v] (some g.org)) le ls1
  let ls2 := endRun.2
  have hemit : emitTerm (.ret [v] (some g.org)) le ls1 = ((), ls2) := by rfl
  have hadv2 : ls1.Adv ls2 := adv_emitTerm hemit
  have hsize : startLS.blocks.size ≤ ls2.blocks.size := (hadv1.trans hadv2).ext.1
  have hpos : 0 < ls2.blocks.size := Nat.lt_of_lt_of_le (by simp [startLS]) hsize
  rw [lowerGlobal_blocks]
  simp only [finishBlocks, Array.size_map]
  change 0 < ls2.blocks.size
  exact hpos


end Goose.Proofs.Lower
