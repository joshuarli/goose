import Goose.Lower.Loops
import Goose.Lower.Prefix

namespace Goose.Lower

open Goose.Core Goose.GIR

private theorem goes_cmp_pure {cx : FnCtx} {pt : Pt} {fr : Frame} {r : ValueId}
    {t : IntTy} {i b : ValueId} {x : RVal}
    (hi : instAt cx.fn pt = some (.def r (.cmp .lt t i b)))
    (hx : execPure cx fr (.cmp .lt t i b) = pure x) :
    Goes cx pt fr (pt.1, pt.2 + 1) (fr.set r x) := by
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  simp only [execOp, hx, pure_bind, setCell_eq]

private theorem goes_next_pure {cx : FnCtx} {pt : Pt} {fr : Frame} {r : ValueId}
    {t : IntTy} {i : ValueId} {x : RVal}
    (hi : instAt cx.fn pt = some (.def r (.next t i)))
    (hx : execPure cx fr (.next t i) = pure x) :
    Goes cx pt fr (pt.1, pt.2 + 1) (fr.set r x) := by
  refine ⟨1, fun j => ?_⟩
  unfold runAt
  rw [instsAt_cons hi, exec]
  simp only [execOp, hx, pure_bind, setCell_eq]

/-! ### Builder facts for a lowered counting loop -/

/-- The first instruction in a range header compares the current counter with the sampled bound. -/
theorem rangeCompare_facts {t : IntTy} {i b c : ValueId} {hb : BlockId}
    {le : LEnv} {ls ls' : LS} {T : Array GIR.Block}
    (h : emitDef (.cmp .lt t i b) le ls = (c, ls'))
    (hpp : ls.pp = some (hb, 0)) (hext : ExtT ls' T) :
    c = ls.vals.size ∧ ls'.vals.size = ls.vals.size + 1 ∧ ls'.stack = ls.stack ∧
      ls'.pp = some (hb, 1) ∧ instAtT T (hb, 0) = some (.def c (.cmp .lt t i b)) := by
  obtain ⟨rfl, hv, hs, hp, hi⟩ := emitDef_facts h hpp hext
  exact ⟨rfl, hv, hs, by simpa using hp, hi⟩

/-- A fresh range header's parameter is the first value after the current builder prefix. -/
theorem rangeHeader_id (t : IntTy) (le : LEnv) (ls : LS) :
    (newBlock [.data (.int t)] le ls).1 = (ls.blocks.size, [ls.vals.size]) := by
  rw [newBlock1_run]

theorem rangeHeader_size (t : IntTy) (le : LEnv) (ls : LS) :
    (newBlock [.data (.int t)] le ls).2.vals.size = ls.vals.size + 1 := by
  rw [newBlock1_run]
  simp

/-- Expose the concrete compare, fork, body, back edge and exit cursor emitted by `lowerRange`. -/
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

/-- A range header keeps the cells before its counter stable and names the current counter and
sampled upper bound independently. -/
def RangeInv (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (counter bound : ValueId)
    (t : IntTy) (upper : Int) (base : Frame) (current : Int) (fr : Frame) : Prop :=
  Same counter base fr ∧
  fr.vals[counter]? = some (.val (.int t current)) ∧
  fr.vals[bound]? = some (.val (.int t upper)) ∧
  Rel cfg env cx fr ls

/-- The lowered range loop simulates every finite successful Core execution. The loop invariant
keeps the values below the header parameter stable and names the changing counter and fixed upper
bound as separate cells. -/
theorem lowerRange_sim (n : Nat) (x : VarId) (t : IntTy) (counter bound : ValueId) (hb : BlockId)
    (body : Core.Block) (org : OriginId) (upper : Int)
    (hokB : blockOk body = true) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (hscope : ∃ lv, env.vars[x]? = some lv ∧ lv.scope = body.scope)
    (le : LEnv) (ls ls' : LS)
    (hlow : lowerRange t counter bound hb
      (fun d xb => lowerBlock (some ⟨d, xb, .next hb t counter⟩) [(x, counter, org)] false body)
      le ls = ((), ls'))
    (hpp : ls.pp = some (hb, 0)) (hext : ExtT ls' cx.fn.blocks)
    (hheader : ∃ blk, cx.fn.blocks[hb]? = some blk ∧
      blk.params = [(counter, .data (.int t))])
    (hboundLt : bound < counter) (hcounterLt : counter < ls.vals.size) :
    ∀ (base : Frame) (start : Int) (fr : Frame),
      RangeInv cfg env cx ls counter bound t upper base start fr →
      SimG cx (hb, 0) fr (execRange n cfg env x t start upper body)
        (fun flow _ fr' => flow = .normal .unit ∧ Same counter base fr' ∧
          fr'.vals[bound]? = some (.val (.int t upper)) ∧ Rel cfg env cx fr' ls') := by
  let bodyB := fun d xb =>
    lowerBlock (some ⟨d, xb, .next hb t counter⟩) [(x, counter, org)] false body
  change lowerRange t counter bound hb bodyB le ls = ((), ls') at hlow
  obtain ⟨c, ls1, tb, xb, lsf, ls2, rBody, lsBody, lsBack,
      hcmp, hfork, e2, hbody, hback, eExit⟩ := lowerRange_unfold hlow
  have aBack := advB_rangeBack t counter hb le lsBody () lsBack hback
  have hextBack : ExtT lsBack cx.fn.blocks := by
    rw [eExit] at hext
    exact hext
  have hextBody : ExtT lsBody cx.fn.blocks := hextBack.of_adv aBack
  have aBody := advB_lowerBlock (some ⟨ls1.stack.length, xb, .next hb t counter⟩)
    [(x, counter, org)] false body le ls2 rBody lsBody hbody
  have hext2 : ExtT ls2 cx.fn.blocks := hextBody.of_adv aBody
  have hextFork : ExtT lsf cx.fn.blocks := by
    simpa [ExtT, e2] using hext2
  obtain ⟨_, hcur, _, _⟩ := LS.pp_some hpp
  have hcur1 : ls1.cur = some hb := by
    have hrun := emitDef_run (.cmp .lt t counter bound) le hcur
    rw [hrun] at hcmp
    have hstate := (Prod.mk.inj hcmp).2
    calc
      ls1.cur = ls.cur := by simpa using (congrArg LS.cur hstate).symm
      _ = some hb := hcur
  have aFork := adv_fork hcur1 hfork
  have hext1 : ExtT ls1 cx.fn.blocks := hextFork.of_adv aFork
  obtain ⟨hcId, hcSize, hcmpStack, hppCmp, hcmpInst⟩ :=
    rangeCompare_facts hcmp hpp hext1
  obtain ⟨htb, hxb, hszFork, hvalsFork, hstackFork, hcurFork, htermFork, htb0, hxb0⟩ :=
    fork_facts hfork hppCmp hextFork
  obtain ⟨Ttb, hTtb, hTtbp⟩ := hextFork.params htb0
  obtain ⟨Txb, hTxb, hTxbp⟩ := hextFork.params hxb0
  have hiCmp : instAt cx.fn (hb, 0) = some (.def c (.cmp .lt t counter bound)) := by
    rw [instAt_eq]
    exact hcmpInst
  have hiBranch : instAt cx.fn (hb, 1) = some (.term (.condbr c tb [] xb [])) := by
    rw [instAt_eq]
    exact htermFork
  have hls2Val : ls2.vals.size = ls.vals.size + 1 := by
    rw [e2]
    change lsf.vals.size = _
    rw [hvalsFork, hcSize]
  intro base start fr hInitial
  let headerInv := fun current fr =>
    RangeInv cfg env cx ls counter bound t upper base current fr
  let bodyInv := headerInv
  let post : Flow → Pt → Frame → Prop := fun flow _ fr' =>
    flow = Flow.normal .unit ∧ Same counter base fr' ∧
      fr'.vals[bound]? = some (.val (.int t upper)) ∧ Rel cfg env cx fr' ls'
  have hc : RangeBranch cx (hb, 0) (tb, 0) upper headerInv bodyInv post := by
    intro current fr hinv
    rcases hinv with ⟨hsame, hcounter, hbound, hrel⟩
    have hcmpPure : execPure cx fr (.cmp .lt t counter bound) =
        pure (.val (.bool (current < upper))) := by
      have h := (execPure_cmp (cx := cx) (fr := fr) (op := .lt) hcounter hbound).1 t
      rw [h]
      simp [expectComparable, expectSameTy, evalCmp]
    have gcmp := goes_cmp_pure hiCmp hcmpPure
    let frCmp := fr.set c (.val (.bool (current < upper)))
    have htest : frCmp.vals[c]? = some (.val (.bool (current < upper))) :=
      Frame.set_get _ _ _
    have hcurrentCmp : frCmp.vals[counter]? = some (.val (.int t current)) := by
      have hne : counter ≠ c := by rw [hcId]; exact Nat.ne_of_lt hcounterLt
      simpa [frCmp, Frame.set, Std.HashMap.getElem?_insert, hne.symm] using hcounter
    have hboundCmp : frCmp.vals[bound]? = some (.val (.int t upper)) := by
      have hne : bound ≠ c := by
        rw [hcId]
        exact Nat.ne_of_lt (Nat.lt_trans hboundLt hcounterLt)
      simpa [frCmp, Frame.set, Std.HashMap.getElem?_insert, hne.symm] using hbound
    have hsameCmp0 : Same counter fr frCmp := by
      have hle : counter ≤ c := by rw [hcId]; exact Nat.le_of_lt hcounterLt
      change Same counter fr (fr.set c (.val (.bool (current < upper))))
      exact Same.set (k := counter) fr (r := c) hle _
    have hsameCmp : Same counter base frCmp :=
      hsame.trans hsameCmp0 (Nat.le_refl _)
    have hrelCmp : Rel cfg env cx frCmp ls := by
      simpa [frCmp] using hrel.set c (.val (.bool (current < upper)))
    by_cases hlt : current < upper
    · simp only [hlt, ↓reduceIte]
      have htestTrue : frCmp.vals[c]? = some (.val (.bool true)) := by
        simpa [hlt] using htest
      have gbr := goes_condbr_then0 hiBranch htestTrue hTtb hTtbp rfl
      refine ⟨frCmp, ?_, gcmp.trans gbr⟩
      exact ⟨hsameCmp, hcurrentCmp, hboundCmp, hrelCmp⟩
    · simp only [hlt, ↓reduceIte]
      have htestFalse : frCmp.vals[c]? = some (.val (.bool false)) := by
        simpa [hlt] using htest
      have gbr := goes_condbr_else0 hiBranch htestFalse hTxb hTxbp rfl
      refine ⟨(xb, 0), frCmp, ?_, gcmp.trans gbr⟩
      refine ⟨rfl, hsameCmp, hboundCmp, ?_⟩
      have hstackOut : ls'.stack = ls.stack := by
        rw [eExit]
        exact aBack.stack.trans (aBody.stack.trans (by rw [e2]; exact hstackFork.trans hcmpStack))
      exact hrelCmp.stack_eq hstackOut
  have hbdy : RangeBody cx cfg env x t body (hb, 0) (tb, 0) headerInv bodyInv := by
    intro fuel current fr hinv
    rcases hinv with ⟨hsame, hcounter, hbound, hrel⟩
    have hstack2 : ls2.stack = ls.stack := by
      rw [e2]
      exact hstackFork.trans hcmpStack
    have hrel2 : Rel cfg env cx fr ls2 := hrel.stack_eq hstack2
    have hpre : PreRel fr [(x, counter, org)] [(x, .int t current)] := by
      simp [PreRel, hcounter]
    have hscopeBody : ∀ p ∈ ([(x, counter, org)] : List (SlotId × ValueId × OriginId)),
        ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = body.scope := by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact hscope
    have hpp2 : ls2.pp = some (tb, 0) := by
      rw [e2]
      exact LS.pp_cur htb0
    have hblock := blockPreClaim fuel (some ⟨ls1.stack.length, xb, .next hb t counter⟩)
      [(x, counter, org)] [(x, .int t current)] false body cfg env hokB hscopeBody
      le ls2 rBody lsBody (tb, 0) cx fr hbody hpp2 hextBody hrel2 hpre
    refine SimG.mono hblock fun flow ptBody frBody hresult => ?_
    rcases hresult with ⟨v, rfl, _, P⟩
    obtain ⟨blkBody, hcurBody, hblkBody, hptBody⟩ := LS.pp_some P.pp
    have hcounterBase : counter < ls2.vals.size := by
      rw [hls2Val]
      exact Nat.lt_trans hcounterLt (Nat.lt_succ_self _)
    have hboundBase : bound < ls2.vals.size := by
      rw [hls2Val]
      exact Nat.lt_trans (Nat.lt_trans hboundLt hcounterLt) (Nat.lt_succ_self _)
    have hcellBody : frBody.vals[counter]? = some (.val (.int t current)) := by
      rw [P.same counter hcounterBase, hcounter]
    have hboundBody : frBody.vals[bound]? = some (.val (.int t upper)) := by
      rw [P.same bound hboundBase, hbound]
    have hnLt : counter < lsBody.vals.size :=
      Nat.lt_of_lt_of_le hcounterBase P.mono
    have hbackLive : ∃ next lsN,
        emitDef (.next t counter) le lsBody = (next, lsN) ∧
        emitTerm (.br hb [next]) le lsN = ((), lsBack) := by
      rw [rangeBack] at hback
      rw [bind_run, isLive_run hcurBody] at hback
      simp only [ite_true, bind_eq] at hback
      exact hback
    obtain ⟨next, lsN, hnext, hterm⟩ := hbackLive
    have hextN : ExtT lsN cx.fn.blocks := hextBack.of_adv (adv_emitTerm hterm)
    obtain ⟨hnextId, hnextSize, hnextStack, hnextPp, hnextInst⟩ :=
      emitDef_facts hnext P.pp hextN
    obtain ⟨_, _, _, htermInst⟩ := emitTerm_facts hterm hnextPp hextBack
    have hiNext : instAt cx.fn ptBody = some (.def next (.next t counter)) := by
      rw [instAt_eq]
      exact hnextInst
    have hnextPure : execPure cx frBody (.next t counter) =
        pure (.val (.int t (current + 1))) := by
      simp [execPure, getVal_of hcellBody, expectInt]
    have gnext := goes_next_pure hiNext hnextPure
    have hcellNext : (frBody.set next (.val (.int t (current + 1)))).vals[next]? =
        some (.val (.int t (current + 1))) := Frame.set_get _ _ _
    have hheaderBlk := hheader
    rcases hheaderBlk with ⟨headerBlk, hheaderBlk, hheaderParams⟩
    have hiTerm : instAt cx.fn (ptBody.1, ptBody.2 + 1) =
        some (.term (.br hb [next])) := by
      rw [instAt_eq]
      exact htermInst
    have gback := goes_br1 hiTerm hheaderBlk hheaderParams hcellNext
    let frHeader := (frBody.set next (.val (.int t (current + 1)))).set counter
      (.val (.int t (current + 1)))
    have hsameToBody : Same counter base frBody := by
      exact hsame.trans (P.same.mono (Nat.le_of_lt hcounterBase)) (Nat.le_refl _)
    have hnextLt : counter < next := by rw [hnextId]; exact hnLt
    have hsameNext : Same counter frBody (frBody.set next (.val (.int t (current + 1)))) :=
      Same.set (k := counter) frBody (r := next) (Nat.le_of_lt hnextLt) _
    have hsameHeader : Same counter
        (frBody.set next (.val (.int t (current + 1)))) frHeader :=
      Same.set _ (Nat.le_refl _) _
    have hsameFinal : Same counter base frHeader :=
      hsameToBody.trans (hsameNext.trans hsameHeader (Nat.le_refl _)) (Nat.le_refl _)
    have hupperHeader : frHeader.vals[bound]? = some (.val (.int t upper)) := by
      have hboundNext : (frBody.set next (.val (.int t (current + 1)))).vals[bound]? =
          some (.val (.int t upper)) := by
        have hne : next ≠ bound := Nat.ne_of_gt (Nat.lt_trans hboundLt hnextLt)
        simpa [Frame.set, Std.HashMap.getElem?_insert, hne] using hboundBody
      have hne : counter ≠ bound := Nat.ne_of_gt hboundLt
      simpa [frHeader, Frame.set, Std.HashMap.getElem?_insert, hne] using hboundNext
    have hcounterHeader : frHeader.vals[counter]? = some (.val (.int t (current + 1))) :=
      Frame.set_get _ _ _
    have hstackHeader : ls.stack = lsBody.stack := by
      calc
        ls.stack = ls1.stack := hcmpStack.symm
        _ = lsf.stack := hstackFork.symm
        _ = ls2.stack := by rw [e2]
        _ = lsBody.stack := aBody.stack.symm
    have hrelHeader : Rel cfg env cx frHeader ls := by
      have hrelBody : Rel cfg env cx frBody lsBody := P.rel
      have hrelNext : Rel cfg env cx (frBody.set next (.val (.int t (current + 1)))) lsN :=
        (hrelBody.set next _).stack_eq hnextStack
      have hrelBack : Rel cfg env cx frHeader lsBack :=
        (hrelNext.set counter _).stack_eq (by
          have := (adv_emitTerm hterm).stack
          exact this)
      exact hrelBack.stack_eq (hstackHeader.trans aBack.stack.symm)
    refine ⟨v, frHeader, rfl, ⟨hsameFinal, hcounterHeader, hupperHeader, hrelHeader⟩,
      gnext.trans gback⟩
  have hsim := range_sim cx cfg env x t upper body (hb, 0) (tb, 0)
    headerInv bodyInv post hc hbdy
  exact hsim n start fr hInitial

end Goose.Lower
