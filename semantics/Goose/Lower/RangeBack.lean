import Goose.Lower.RangeRuntime

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem rangeBack_goes (cx : FnCtx) (le : LEnv) (ls ls' : LS) (pt : Pt) (fr : Frame)
    (counter hb : ValueId) (hint ty : IntTy) (i : Int)
    (hback : rangeBack hint counter hb le ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks)
    (hc : counter < ls.vals.size)
    (hcounter : fr.vals[counter]? = some (.val (.int ty i)))
    (hheader : ∃ block, cx.fn.blocks[hb]? = some block ∧
      block.params = [(counter, .data (.int ty))]) :
    ∃ fr', Goes cx pt fr (hb, 0) fr' ∧ Same counter fr fr' ∧
      fr'.vals[counter]? = some (.val (.int ty (i + 1))) ∧
      fr'.act = fr.act ∧ fr'.scopes = fr.scopes ∧ fr'.depth = fr.depth := by
  obtain ⟨_, hcur, _, _⟩ := LS.pp_some hpp
  rw [rangeBack, bind_run, isLive_run hcur] at hback
  simp only [ite_true, bind_eq] at hback
  obtain ⟨next, lsNext, hnext, hterm⟩ := hback
  have hextNext := hext.of_adv (adv_emitTerm hterm)
  obtain ⟨hnextId, _, _, hppNext, hnextInst⟩ := emitDef_facts hnext hpp hextNext
  obtain ⟨_, _, _, htermInst⟩ := emitTerm_facts hterm hppNext hext
  have hiNext : instAt cx.fn pt = some (.def next (.next hint counter)) := by
    rw [instAt_eq]
    exact hnextInst
  have hnextPure : execPure cx fr (.next hint counter) =
      pure (.val (.int ty (i + 1))) := by
    simp [execPure, getVal_of hcounter, expectInt]
  have gnext := Goes.def_pure hiNext (by simp) hnextPure
  have hiTerm : instAt cx.fn (pt.1, pt.2 + 1) = some (.term (.br hb [next])) := by
    rw [instAt_eq]
    exact htermInst
  obtain ⟨block, hblock, hparams⟩ := hheader
  have gback := goes_br1 hiTerm hblock hparams (Frame.set_get fr next (.val (.int ty (i + 1))))
  let after := (fr.set next (.val (.int ty (i + 1)))).set counter
    (.val (.int ty (i + 1)))
  refine ⟨after, gnext.trans gback, ?_, Frame.set_get _ _ _, rfl, rfl, rfl⟩
  have hnextBound : counter ≤ next := by rw [hnextId]; exact Nat.le_of_lt hc
  exact (Same.set fr hnextBound _).trans (Same.set _ (Nat.le_refl counter) _) (Nat.le_refl _)

end Goose.Lower
