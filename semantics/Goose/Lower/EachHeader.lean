import Goose.Lower.Each

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem eachHeader_setup (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (input withHeader closed header : LS) (fr : Frame) (pt : Pt)
    (start hb : Nat) (params : List ValueId)
    (hnew : newBlock [.data (.int .i64)] le input = ((hb, params), withHeader))
    (hterm : emitTerm (.br hb [start]) le withHeader = ((), closed))
    (hset : setCur (some hb) le closed = ((), header))
    (hpp : input.pp = some pt) (hext : ExtT header cx.fn.blocks)
    (hrel : Rel cfg env cx fr input)
    (hstart : fr.vals[start]? = some (.val (.int .i64 0))) :
    let counter := params.headD 0
    let frHeader := fr.set counter (.val (.int .i64 0))
    counter = input.vals.size ∧ counter < header.vals.size ∧
      header.stack = input.stack ∧ header.pp = some (hb, 0) ∧
      (∃ block, cx.fn.blocks[hb]? = some block ∧ block.params = [(counter, .data (.int .i64))]) ∧
      Goes cx pt fr (hb, 0) frHeader ∧ Same counter fr frHeader ∧
      frHeader.vals[counter]? = some (.val (.int .i64 0)) ∧ Rel cfg env cx frHeader header := by
  dsimp only
  have hsetEq : header = { closed with cur := some hb } := by
    rw [setCur_run] at hset
    exact (Prod.mk.inj hset).2.symm
  have hextClosed : ExtT closed cx.fn.blocks := by simpa [hsetEq, ExtT] using hext
  have hextWith := hextClosed.of_adv (adv_emitTerm hterm)
  have hnewEq := hnew
  rw [newBlock1_run] at hnewEq
  obtain ⟨hids, hstate⟩ := Prod.mk.inj hnewEq
  obtain ⟨hhb, hparams⟩ := Prod.mk.inj hids
  have hcounter : params.headD 0 = input.vals.size := by rw [← hparams]; rfl
  have hsize : withHeader.vals.size = input.vals.size + 1 := by rw [← hstate]; simp
  have hstack : withHeader.stack = input.stack := by rw [← hstate]
  have hcur : withHeader.cur = input.cur := by rw [← hstate]
  obtain ⟨inputBlock, hcurInput, hlookupInput, hpointInput⟩ := LS.pp_some hpp
  have hltInput : pt.1 < input.blocks.size := (Array.getElem?_eq_some_iff.mp hlookupInput).1
  have hlookupWith : withHeader.blocks[pt.1]? = some inputBlock := by
    rw [← hstate]
    exact (getElem?_push_lt hltInput).trans hlookupInput
  have hppWith : withHeader.pp = some pt := by
    have h := LS.pp_eq (hcur.trans hcurInput) hlookupWith
    rw [← hpointInput] at h
    exact h
  obtain ⟨hvalsClosed, hstackClosed, _, hinst⟩ := emitTerm_facts hterm hppWith hextClosed
  have hheaderWith : withHeader.blocks[hb]? =
      some ⟨[(params.headD 0, .data (.int .i64))], #[]⟩ := by
    rw [hcounter, ← hhb, ← hstate]
    simp
  have hne : withHeader.cur ≠ some hb := by
    rw [hcur, hcurInput]
    intro he
    have hi := Option.some.inj he
    rw [← hhb] at hi
    exact Nat.ne_of_lt hltInput hi
  have hheaderClosed := (adv_emitTerm hterm).keep hb _ hne hheaderWith
  have hppHeader : header.pp = some (hb, 0) := by rw [hsetEq]; exact LS.pp_cur hheaderClosed
  obtain ⟨target, htarget, htargetParams⟩ := hextClosed.params hheaderClosed
  have hiTerm : instAt cx.fn pt = some (.term (.br hb [start])) := hinst
  have hstackHeader : header.stack = input.stack := by
    rw [hsetEq]
    exact hstackClosed.trans hstack
  have hcounterBound : params.headD 0 < header.vals.size := by
    rw [hsetEq]
    change params.headD 0 < closed.vals.size
    rw [hvalsClosed, hsize, hcounter]
    exact Nat.lt_succ_self _
  exact ⟨hcounter, hcounterBound, hstackHeader, hppHeader,
    ⟨target, htarget, htargetParams⟩, goes_br1 hiTerm htarget htargetParams hstart,
    Same.set fr (Nat.le_refl _) _, Frame.set_get _ _ _,
    (hrel.set (params.headD 0) _).stack_eq hstackHeader⟩

end Goose.Lower
