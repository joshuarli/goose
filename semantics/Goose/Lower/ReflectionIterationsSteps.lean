import Goose.Lower.ReflectionBranchesSteps
import Goose.Lower.RangeBack

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem runAt_defPure_step {cx : FnCtx} {pt : Pt} {fr : Frame} {r : ValueId} {op : Op}
    {value : RVal} (instruction : instAt cx.fn pt = some (.def r op))
    (noncall : ∀ f args org, op ≠ .call f args org) (equal : execPure cx fr op = pure value)
    (fuel : Nat) : runAt cx pt fr (fuel + 1) =
      runAt cx (pt.1,pt.2 + 1) (fr.set r value) fuel := by
  have operation : ∀ n, execOp n cx fr op = execPure cx fr op := by
    intro n
    cases op with
    | call f args org => exact (noncall f args org rfl).elim
    | _ => unfold execOp; rfl
  unfold runAt
  rw [instsAt_cons instruction,exec,operation,equal]
  simp only [pure_bind,setCell_eq]

theorem rangeBack_exact (cx : FnCtx) (le : LEnv) (ls ls' : LS) (pt : Pt) (fr : Frame)
    (counter hb : ValueId) (hint ty : IntTy) (i : Int)
    (hback : rangeBack hint counter hb le ls = ((),ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hc : counter < ls.vals.size)
    (hcounter : fr.vals[counter]? = some (.val (.int ty i)))
    (hheader : ∃ block, cx.fn.blocks[hb]? = some block ∧
      block.params = [(counter,.data (.int hint))]) :
    ∃ fr', runAt cx pt fr 1 = (Core.timeout : M Val) ∧ (∀ fuel, runAt cx pt fr (fuel + 2) = runAt cx (hb,0) fr' fuel) ∧
      Same counter fr fr' ∧ fr'.vals[counter]? = some (.val (.int ty (i + 1))) ∧
      fr'.act = fr.act ∧ fr'.scopes = fr.scopes ∧ fr'.depth = fr.depth := by
  obtain ⟨_,hcur,_,_⟩ := LS.pp_some hpp
  rw [rangeBack,bind_run,isLive_run hcur] at hback
  simp only [ite_true,bind_eq] at hback
  obtain ⟨next,lsNext,hnext,hterm⟩ := hback
  have hextNext := hext.of_adv (adv_emitTerm hterm)
  obtain ⟨hnextId,_,_,hppNext,hnextInst⟩ := emitDef_facts hnext hpp hextNext
  obtain ⟨_,_,_,htermInst⟩ := emitTerm_facts hterm hppNext hext
  have hiNext : instAt cx.fn pt = some (.def next (.next hint counter)) := hnextInst
  have nextPure : execPure cx fr (.next hint counter) = pure (.val (.int ty (i + 1))) := by
    simp [execPure,getVal_of hcounter,expectInt]
  have hiTerm : instAt cx.fn (pt.1,pt.2 + 1) = some (.term (.br hb [next])) := htermInst
  obtain ⟨block,hblock,hparams⟩ := hheader
  let after := (fr.set next (.val (.int ty (i + 1)))).set counter (.val (.int ty (i + 1)))
  refine ⟨after,?_,?_,?_,Frame.set_get _ _ _,rfl,rfl,rfl⟩
  · rw [runAt_defPure_step hiNext (by simp) nextPure 0]
    rfl
  · intro fuel
    rw [show fuel + 2 = (fuel + 1) + 1 by omega,
      runAt_defPure_step hiNext (by simp) nextPure,
      runAt_br1_step hiTerm hblock hparams (Frame.set_get _ _ _)]
  · have nextBound : counter ≤ next := by rw [hnextId]; exact Nat.le_of_lt hc
    exact (Same.set fr nextBound _).trans (Same.set _ (Nat.le_refl counter) _) (Nat.le_refl _)

end Goose.Lower
