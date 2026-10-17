import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem rangeCompare_facts {t : IntTy} {i b c : ValueId} {hb : BlockId}
    {le : LEnv} {ls ls' : LS} {T : Array GIR.Block}
    (h : emitDef (.cmp .lt t i b) le ls = (c, ls'))
    (hpp : ls.pp = some (hb, 0)) (hext : ExtT ls' T) :
    c = ls.vals.size ∧ ls'.vals.size = ls.vals.size + 1 ∧ ls'.stack = ls.stack ∧
      ls'.pp = some (hb, 1) ∧ instAtT T (hb, 0) = some (.def c (.cmp .lt t i b)) := by
  obtain ⟨rfl, hv, hs, hp, hi⟩ := emitDef_facts h hpp hext
  exact ⟨rfl, hv, hs, by simpa using hp, hi⟩

theorem rangeHeader_id (t : IntTy) (le : LEnv) (ls : LS) :
    (newBlock [.data (.int t)] le ls).1 = (ls.blocks.size, [ls.vals.size]) := by
  rw [newBlock1_run]

theorem rangeHeader_size (t : IntTy) (le : LEnv) (ls : LS) :
    (newBlock [.data (.int t)] le ls).2.vals.size = ls.vals.size + 1 := by
  rw [newBlock1_run]
  simp

theorem lowerRange_unfold {t : IntTy} {i b : ValueId} {hb : BlockId}
    {body : Nat → BlockId → B ValueId}
    {le : LEnv} {ls ls' : LS}
    (h : lowerRange t i b hb body le ls = ((), ls')) :
    ∃ c ls1 tb xb lsf ls2 rBody lsBody lsBack,
      emitDef (.cmp .lt t i b) le ls = (c, ls1) ∧
      fork c le ls1 = ((tb, xb), lsf) ∧
      ls2 = { lsf with cur := some tb } ∧
      body ls1.stack.length xb le ls2 = (rBody, lsBody) ∧
      rangeBack t i hb le lsBody = ((), lsBack) ∧
      ls' = { lsBack with cur := some xb } := by
  unfold lowerRange at h
  simp only [bind_eq] at h
  obtain ⟨c, ls1, hcmp, hloop⟩ := h
  unfold loopBody at hloop
  simp only [bind_eq] at hloop
  obtain ⟨d, lsG, hg, ⟨tb, xb⟩, lsf, hf, u2, ls2, hs2, rBody, lsBody, hbody,
    u4, lsBack, hback, hExit⟩ := hloop
  rw [get_apply] at hg
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
  rw [setCur_run] at hs2 hExit
  have e2 : ls2 = { lsf with cur := some tb } := (Prod.mk.inj hs2).2.symm
  have eExit : ls' = { lsBack with cur := some xb } := (Prod.mk.inj hExit).2.symm
  exact ⟨c, ls1, tb, xb, lsf, ls2, rBody, lsBody, lsBack,
    hcmp, hf, e2, hbody, hback, eExit⟩

def RangeInv (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (counter bound : ValueId)
    (t : IntTy) (upper : Int) (base : Frame) (current : Int) (fr : Frame) : Prop :=
  Same counter base fr ∧
  fr.vals[counter]? = some (.val (.int t current)) ∧
  fr.vals[bound]? = some (.val (.int t upper)) ∧
  Rel cfg env cx fr ls


end Goose.Lower
