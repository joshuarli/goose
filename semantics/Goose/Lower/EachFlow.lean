import Goose.Lower.EachRuntime
import Goose.Lower.GeneratedLoopFrames

namespace Goose.Lower

open Goose.Core Goose.GIR

def EachFlowPost (cfg : Cfg) (env : Env) (cx : FnCtx) (output : LS)
    (counter : ValueId) (base : Frame) (flow : Flow) (pt : Pt) (fr : Frame) : Prop :=
  (flow = .normal .unit ∧ output.pp = some pt ∧ Same counter base fr ∧ Rel cfg env cx fr output) ∨
    ReturnedAt cx flow pt fr

theorem eachLoopFlow_to_step (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (header input withValue output back finalBuilder : LS) (base before beforeBlock after : Frame)
    (counter view sampled hb exit depth value result : Nat) (owner : Option ValueId)
    (vw : ViewVal) (i : Nat) (element : Val) (block : Core.Block) (flow : Flow)
    (ptValue ptAfter : Pt)
    (hinv : EachInv cfg env cx input counter view sampled owner vw base i before)
    (PValue : Post cfg env cx input before withValue beforeBlock ptValue [(value, .val element)])
    (hflow : LoopFlowPost cfg env cx withValue beforeBlock output
      ⟨depth, exit, .next hb .i64 counter⟩ block result flow ptAfter after)
    (hcounterInput : counter < input.vals.size) (hviewBound : view < counter)
    (hownerBound : vw.resizable = true → owner.getD 0 < counter)
    (hsampleBound : vw.resizable = false → sampled < counter)
    (hstackHeader : header.stack = input.stack) (hstackFinal : finalBuilder.stack = input.stack)
    (hppExit : finalBuilder.pp = some (exit, 0))
    (hback : rangeBack .i64 counter hb le output = ((), back)) (hextBack : ExtT back cx.fn.blocks)
    (hheader : ∃ target, cx.fn.blocks[hb]? = some target ∧
      target.params = [(counter, .data (.int .i64))]) :
    EachStepPost cx (hb, 0) (EachInv cfg env cx header counter view sampled owner vw base)
      (EachFlowPost cfg env cx finalBuilder counter base) i flow ptAfter after := by
  have hcounterValue : beforeBlock.vals[counter]? = some (.val (.int .i64 i)) := by
    rw [PValue.same counter hcounterInput]
    exact hinv.counterValue
  have hcounterWith : counter < withValue.vals.size := Nat.lt_of_lt_of_le hcounterInput PValue.mono
  have hsameValue : Same counter base beforeBlock :=
    hinv.values.trans (PValue.same.mono (Nat.le_of_lt hcounterInput)) (Nat.le_refl _)
  rcases hflow with ⟨normal, rfl, PBlock⟩ | hreturned | ⟨rfl, hbreak⟩ | ⟨rfl, hcontinue⟩
  · have P := PValue.comp PBlock
    have hinvBody := hinv.of_post P hcounterInput hviewBound hownerBound hsampleBound
    have hcounterBody : counter < output.vals.size := Nat.lt_of_lt_of_le hcounterInput P.mono
    obtain ⟨nextFrame, hgo, hsame, hcell, hact, hscopes, hdepth⟩ :=
      eachBack_goes cx le output back ptAfter after counter hb i hback PBlock.pp hextBack
        hcounterBody hinvBody.counterValue hheader
    have hrel : Rel cfg env cx nextFrame header :=
      ⟨hinv.rel.prof, hinv.rel.slots, hact.trans hinvBody.rel.act,
        hscopes.trans hinvBody.rel.scopes, hdepth.trans hinvBody.rel.depth,
        hstackHeader.trans hinv.rel.stack⟩
    exact ⟨nextFrame, hinvBody.reentry hsame hcell hrel hviewBound hownerBound hsampleBound, hgo⟩
  · obtain ⟨returned, org, hreturn, hsite⟩ := hreturned
    subst flow
    exact Or.inr ⟨returned, org, rfl, hsite⟩
  · obtain ⟨hpoint, hframe⟩ := hbreak
    have hsame : Same counter base after := hsameValue.trans
      (hframe.values.mono (Nat.le_of_lt hcounterWith)) (Nat.le_refl _)
    have hrel : Rel cfg env cx after finalBuilder :=
      ⟨hinv.rel.prof, hinv.rel.slots, hframe.activation.trans PValue.rel.act,
        hframe.scopesEqual, hframe.depth.trans PValue.rel.depth,
        hstackFinal.trans hinv.rel.stack⟩
    exact Or.inl ⟨rfl, hpoint.symm ▸ hppExit, hsame, hrel⟩
  · obtain ⟨runtimeTy, current, hbefore, hnext⟩ := hcontinue
    have hvalue : RVal.val (.int runtimeTy current) = .val (.int .i64 i) :=
      Option.some.inj (hbefore.symm.trans hcounterValue)
    obtain ⟨htype, hcurrent⟩ := Val.int.inj (RVal.val.inj hvalue)
    subst runtimeTy
    subst current
    have hsame : Same counter before after :=
      (PValue.same.mono (Nat.le_of_lt hcounterInput)).trans hnext.values (Nat.le_refl _)
    have hrel : Rel cfg env cx after header :=
      ⟨hinv.rel.prof, hinv.rel.slots, hnext.activation.trans PValue.rel.act,
        hnext.scopesEqual, hnext.depth.trans PValue.rel.depth,
        hstackHeader.trans hinv.rel.stack⟩
    have hcell : after.vals[counter]? = some (.val (.int .i64 (i + 1 : Nat))) := by
      simpa using hnext.counterValue
    exact ⟨after, hinv.reentry hsame hcell hrel hviewBound hownerBound hsampleBound,
      hnext.point.symm ▸ Goes.refl cx (hb, 0) after⟩

theorem lowerEach_sim_at (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (ls ls' : LS) (counter view sampled hb : ValueId) (owner : Option ValueId)
    (vw : ViewVal) (base : Frame) (x : VarId) (idx : Option VarId) (byRef : Bool)
    (block : Core.Block) (body : Nat → BlockId → B ValueId)
    (allowed bodyAllowed : Nat → St → Prop) (post : Flow → Pt → Frame → Prop)
    (hlow : lowerEach vw.resizable owner sampled hb counter body le ls = ((), ls'))
    (hadv : ∀ d xb, AdvB (body d xb))
    (hpp : ls.pp = some (hb, 0)) (hext : ExtT ls' cx.fn.blocks)
    (hc : counter < ls.vals.size) (hv : view < counter)
    (ho : vw.resizable = true → owner.getD 0 < counter)
    (hs : vw.resizable = false → sampled < counter)
    (hexit : ∀ pt fr, ls'.pp = some pt → Same counter base fr → Rel cfg env cx fr ls' →
      post (.normal .unit) pt fr)
    (henter : ∀ i s len s', allowed i s →
      (if vw.resizable then lengthLoc vw.loc else pure vw.len) s = .ok len s' →
      i < len → bodyAllowed i s)
    (hretain : ∀ k, k < n → ∀ i s flow s', bodyAllowed i s →
      eachIterationCore k cfg env x idx byRef block vw i s = .ok flow s' →
      (match flow with | .normal _ | .cont => allowed (i + 1) s' | _ => True))
    (hbody : ∀ d xb input result output back tb,
      body d xb le input = (result, output) → input.pp = some (tb, 0) →
      rangeBack .i64 counter hb le output = ((), back) → ExtT back cx.fn.blocks →
      ExtT output cx.fn.blocks → counter < input.vals.size → input.stack = ls.stack →
      d = input.stack.length → ls'.pp = some (xb, 0) →
      (∃ block, cx.fn.blocks[xb]? = some block ∧ block.params = []) →
      ∀ fuel, fuel < n → ∀ i fr s,
        EachInv cfg env cx input counter view sampled owner vw base i fr → bodyAllowed i s →
        SimEAt cx (tb, 0) fr (eachIterationCore fuel cfg env x idx byRef block vw i)
          (EachStepPost cx (hb, 0)
            (EachInv cfg env cx ls counter view sampled owner vw base) post i) s) :
    ∀ i fr s, EachInv cfg env cx ls counter view sampled owner vw base i fr → allowed i s →
      SimEAt cx (hb, 0) fr (execEach n cfg env x idx byRef block vw i >>= prepareReturn env) post s := by
  obtain ⟨len, lsLen, cmp, lsCmp, tb, xb, lsf, input, result, output, lsBack,
    hLen, hCmp, hFork, hInput, hBody, hBack, hExit⟩ := lowerEach_unfold hlow
  have aBody := hadv lsCmp.stack.length xb le input result output hBody
  have aBack := advB_rangeBack .i64 counter hb le output () lsBack hBack
  have hextBack : ExtT lsBack cx.fn.blocks := by simpa [hExit, ExtT] using hext
  have hextOutput := hextBack.of_adv aBack
  have hextInput := hextOutput.of_adv aBody
  have hextFork : ExtT lsf cx.fn.blocks := by simpa [hInput, ExtT] using hextInput
  have hbranch := lowerEach_branch_sim cfg env cx le ls lsLen lsCmp lsf input output lsBack ls'
    counter view sampled len cmp hb tb xb owner vw base body result
    hLen hCmp hFork hInput hBody aBody hBack hExit hpp hext hc hv ho hs
  have hbranch' : EachBranch cx vw (hb, 0) (tb, 0)
      (EachInv cfg env cx ls counter view sampled owner vw base)
      (EachInv cfg env cx input counter view sampled owner vw base) post := by
    intro i fr hinv
    exact (hbranch i fr hinv).mono fun length pt' fr' h => by
      by_cases hi : i < length
      · simpa only [hi, ite_true] using h
      · simp only [hi, ite_false] at h ⊢
        exact hexit pt' fr' h.2.1 h.2.2.1 h.2.2.2
  have aLen := advB_eachLen vw.resizable owner sampled le ls len lsLen hLen
  have aCmp := adv_emitDef hCmp
  obtain ⟨block0, hcur, hlookup, _⟩ := LS.pp_some hpp
  have hcurLen : lsLen.cur = some hb := by
    cases hr : vw.resizable <;> simp only [eachLen, hr, Bool.false_eq_true, ite_false, ite_true] at hLen
    · rw [pure_run] at hLen
      have he := (Prod.mk.inj hLen).2
      simpa [← he] using hcur
    · rw [emitDef_run _ le hcur] at hLen
      have he := (Prod.mk.inj hLen).2
      simpa using (congrArg LS.cur he).symm.trans hcur
  have hcurCmp : lsCmp.cur = some hb := by
    rw [emitDef_run _ le hcurLen] at hCmp
    have he := (Prod.mk.inj hCmp).2
    simpa using (congrArg LS.cur he).symm.trans hcurLen
  obtain ⟨blockCmp, hlookupCmp, _, _, _⟩ := (aLen.trans aCmp).ext.2 hb block0 hlookup
  have hextCmp := hextFork.of_adv (adv_fork hcurCmp hFork)
  have hfacts := fork_facts hFork (LS.pp_eq hcurCmp hlookupCmp) hextFork
  have hppInput : input.pp = some (tb, 0) := by
    rw [hInput]
    exact LS.pp_cur hfacts.2.2.2.2.2.2.2.1
  have hcounterInput : counter < input.vals.size := by
    rw [hInput]
    change counter < lsf.vals.size
    rw [hfacts.2.2.2.1]
    exact Nat.lt_of_lt_of_le hc (aLen.trans aCmp).vals
  have hstackInput : input.stack = ls.stack := by
    rw [hInput]
    exact hfacts.2.2.2.2.1.trans (aCmp.stack.trans aLen.stack)
  have hdepth : lsCmp.stack.length = input.stack.length := by
    rw [hInput]
    exact congrArg List.length hfacts.2.2.2.2.1.symm
  have hxbBack : lsBack.blocks[xb]? = some ⟨[], #[]⟩ := by
    refine (aBody.trans aBack).keep xb ⟨[], #[]⟩ ?_ ?_
    · rw [hInput]
      intro he
      have hb : tb = xb := Option.some.inj he
      have hids := fork_ids hFork
      have hpair := hids.1
      have ht := (Prod.mk.inj hpair).1
      have hx := (Prod.mk.inj hpair).2
      nat_omega
    · rw [hInput]
      exact hfacts.2.2.2.2.2.2.2.2
  have hppExit : ls'.pp = some (xb, 0) := by rw [hExit]; exact LS.pp_cur hxbBack
  obtain ⟨exitBlock, hExitBlock, hExitParams⟩ := hextBack.params hxbBack
  exact each_sim_at n cx cfg env x idx byRef block vw (hb, 0) (tb, 0)
    _ _ allowed bodyAllowed post hbranch' henter (hbody lsCmp.stack.length xb input result output lsBack tb hBody hppInput
      hBack hextBack hextOutput hcounterInput hstackInput hdepth hppExit
      ⟨exitBlock, hExitBlock, hExitParams⟩) hretain

def EachBlockCallback (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (header : LS) (counter view sampled hb : ValueId) (owner : Option ValueId)
    (vw : ViewVal) (base : Frame) (x : VarId) (idx : Option VarId) (byRef : Bool)
    (block : Core.Block) (org : OriginId) (bodyAllowed : Nat → St → Prop) : Prop :=
  ∀ fuel, fuel < n → ∀ depth exit input withElem withValue blockOutput elem value result
      tb i fr s ev state ptValue frValue,
      emitDef (.refElem view counter) le input = (elem, withElem) →
      eachElemValue x byRef elem le withElem = (value, withValue) →
      lowerBlock (some ⟨depth, exit, .next hb .i64 counter⟩)
        (eachIRPre x idx value counter org) false block le withValue = (result, blockOutput) →
      ExtT blockOutput cx.fn.blocks → counter < input.vals.size → input.stack = header.stack →
      depth = input.stack.length → LoopTargets cx.fn ⟨depth, exit, .next hb .i64 counter⟩ →
      input.pp = some (tb, 0) →
      EachInv cfg env cx input counter view sampled owner vw base i fr → bodyAllowed i s →
      (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) s = .ok ev state →
      Post cfg env cx input fr withValue frValue ptValue [(value, .val ev)] →
      PreRel frValue (eachIRPre x idx value counter org) (eachCorePre x idx ev i) →
      GeneratedBuilderState withValue →
      LoopBuilderFrames (some ⟨depth, exit, .next hb .i64 counter⟩) withValue →
      SimEAt cx ptValue frValue (execBlock fuel cfg env (eachCorePre x idx ev i) block >>=
        prepareReturn env)
        (LoopFlowPost cfg env cx withValue frValue blockOutput
          ⟨depth, exit, .next hb .i64 counter⟩ block result) state

theorem lowerEach_flow_sim_at (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (header output : LS) (counter view sampled hb : ValueId) (owner : Option ValueId)
    (vw : ViewVal) (base : Frame) (x : VarId) (idx : Option VarId) (byRef : Bool)
    (block : Core.Block) (org : OriginId) (allowed bodyAllowed : Nat → St → Prop)
    (hlow : lowerEach vw.resizable owner sampled hb counter
      (eachBodyBuilder x idx byRef block org view counter hb) le header = ((), output))
    (hpp : header.pp = some (hb, 0)) (hext : ExtT output cx.fn.blocks)
    (generatedHeader : GeneratedBuilderState header)
    (hheader : ∃ target, cx.fn.blocks[hb]? = some target ∧
      target.params = [(counter, .data (.int .i64))])
    (hc : counter < header.vals.size) (hv : view < counter)
    (ho : vw.resizable = true → owner.getD 0 < counter)
    (hs : vw.resizable = false → sampled < counter)
    (henter : ∀ i s len s', allowed i s →
      (if vw.resizable then lengthLoc vw.loc else pure vw.len) s = .ok len s' →
      i < len → bodyAllowed i s)
    (hretain : ∀ k, k < n → ∀ i s flow s', bodyAllowed i s →
      eachIterationCore k cfg env x idx byRef block vw i s = .ok flow s' →
      (match flow with | .normal _ | .cont => allowed (i + 1) s' | _ => True))
    (hblock : EachBlockCallback n cfg env cx le header counter view sampled hb owner vw base
      x idx byRef block org bodyAllowed) :
    ∀ i fr s, EachInv cfg env cx header counter view sampled owner vw base i fr → allowed i s →
      SimEAt cx (hb, 0) fr (execEach n cfg env x idx byRef block vw i >>= prepareReturn env)
        (EachFlowPost cfg env cx output counter base) s := by
  have aBody : ∀ depth exit, AdvB (eachBodyBuilder x idx byRef block org view counter hb depth exit) := by
    intro depth exit
    exact AdvB.bind (advB_emitDef _) fun elem =>
      AdvB.bind (advB_eachElemValue x byRef elem) fun value => advB_lowerBlock _ _ _ block
  have hstackOutput := (advB_lowerEach vw.resizable owner sampled hb counter aBody
    le header () output hlow).stack
  obtain ⟨len, lsLen, cmp, lsCmp, tb, xb, lsf, input, result, blockOutput, lsBack,
    hLen, hCmp, hFork, hInput, hBody, hBack, hExit⟩ := lowerEach_unfold hlow
  have aBody := aBody lsCmp.stack.length xb le input result blockOutput hBody
  have aBack := advB_rangeBack .i64 counter hb le blockOutput () lsBack hBack
  have hextBack : ExtT lsBack cx.fn.blocks := by simpa [hExit, ExtT] using hext
  have hextOutput := hextBack.of_adv aBack
  have hextInput := hextOutput.of_adv aBody
  have hextFork : ExtT lsf cx.fn.blocks := by simpa [hInput, ExtT] using hextInput
  have hbranch := lowerEach_branch_sim cfg env cx le header lsLen lsCmp lsf input blockOutput lsBack output
    counter view sampled len cmp hb tb xb owner vw base
    (eachBodyBuilder x idx byRef block org view counter hb) result
    hLen hCmp hFork hInput hBody aBody hBack hExit hpp hext hc hv ho hs
  have hbranch' : EachBranch cx vw (hb, 0) (tb, 0)
      (EachInv cfg env cx header counter view sampled owner vw base)
      (EachInv cfg env cx input counter view sampled owner vw base) (EachFlowPost cfg env cx output counter base) := by
    intro i fr hinv
    exact (hbranch i fr hinv).mono fun length pt' fr' h => by
      by_cases hi : i < length
      · simpa only [hi, ite_true] using h
      · simp only [hi, ite_false] at h ⊢
        exact Or.inl ⟨rfl, h.2.1, h.2.2.1, h.2.2.2⟩
  have aLen := advB_eachLen vw.resizable owner sampled le header len lsLen hLen
  have aCmp := adv_emitDef hCmp
  obtain ⟨block0, hcur, hlookup, _⟩ := LS.pp_some hpp
  have hcurLen : lsLen.cur = some hb := by
    cases hr : vw.resizable <;> simp only [eachLen, hr, Bool.false_eq_true, ite_false, ite_true] at hLen
    · rw [pure_run] at hLen
      have he := (Prod.mk.inj hLen).2
      simpa [← he] using hcur
    · rw [emitDef_run _ le hcur] at hLen
      have he := (Prod.mk.inj hLen).2
      simpa using (congrArg LS.cur he).symm.trans hcur
  have hcurCmp : lsCmp.cur = some hb := by
    rw [emitDef_run _ le hcurLen] at hCmp
    have he := (Prod.mk.inj hCmp).2
    simpa using (congrArg LS.cur he).symm.trans hcurLen
  obtain ⟨blockCmp, hlookupCmp, _, _, _⟩ := (aLen.trans aCmp).ext.2 hb block0 hlookup
  have hextCmp := hextFork.of_adv (adv_fork hcurCmp hFork)
  have hfacts := fork_facts hFork (LS.pp_eq hcurCmp hlookupCmp) hextFork
  have hppInput : input.pp = some (tb, 0) := by
    rw [hInput]
    exact LS.pp_cur hfacts.2.2.2.2.2.2.2.1
  have hcounterInput : counter < input.vals.size := by
    rw [hInput]
    change counter < lsf.vals.size
    rw [hfacts.2.2.2.1]
    exact Nat.lt_of_lt_of_le hc (aLen.trans aCmp).vals
  have hstackInput : input.stack = header.stack := by
    rw [hInput]
    exact hfacts.2.2.2.2.1.trans (aCmp.stack.trans aLen.stack)
  have hdepth : lsCmp.stack.length = input.stack.length := by
    rw [hInput]
    exact congrArg List.length hfacts.2.2.2.2.1.symm
  have hxbBack : lsBack.blocks[xb]? = some ⟨[], #[]⟩ := by
    refine (aBody.trans aBack).keep xb ⟨[], #[]⟩ ?_ ?_
    · rw [hInput]
      intro he
      have hb : tb = xb := Option.some.inj he
      have hids := fork_ids hFork
      have hpair := hids.1
      have ht := (Prod.mk.inj hpair).1
      have hx := (Prod.mk.inj hpair).2
      nat_omega
    · rw [hInput]
      exact hfacts.2.2.2.2.2.2.2.2
  have hppExit : output.pp = some (xb, 0) := by rw [hExit]; exact LS.pp_cur hxbBack
  obtain ⟨exitBlock, hExitBlock, hExitParams⟩ := hextBack.params hxbBack
  have hbodyEach : ∀ fuel, fuel < n → ∀ i fr s,
      EachInv cfg env cx input counter view sampled owner vw base i fr → bodyAllowed i s →
      SimEAt cx (tb, 0) fr (eachIterationCore fuel cfg env x idx byRef block vw i)
        (EachStepPost cx (hb, 0)
          (EachInv cfg env cx header counter view sampled owner vw base)
          (EachFlowPost cfg env cx output counter base) i) s := by
    intro fuel hfuel i fr s hinv hallowed
    unfold eachBodyBuilder at hBody
    simp only [bind_eq] at hBody
    obtain ⟨elem, withElem, hElem, value, withValue, hValue, hBlock⟩ := hBody
    have htargets : LoopTargets cx.fn ⟨lsCmp.stack.length, xb, .next hb .i64 counter⟩ :=
      ⟨⟨exitBlock, hExitBlock, hExitParams⟩, hheader⟩
    have hGeneratedInput : GeneratedBuilderState input := by
      have hsetInput : setCur (some tb) le lsf = ((), input) := by
        rw [setCur_run, hInput]
      have hids := fork_ids hFork
      have htb : tb = lsCmp.blocks.size := by simpa using congrArg Prod.fst hids.1
      have htbBound : tb < lsf.blocks.size := by
        calc
          tb < lsCmp.blocks.size + 2 := by
            rw [htb]
            change lsCmp.blocks.size < Nat.succ (Nat.succ lsCmp.blocks.size)
            exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
          _ = lsf.blocks.size := hids.2.symm
      exact (generatedHeader.eachLen vw.resizable owner sampled hLen).emitDef
        (.cmp .lt .i64 counter len) hCmp |>.fork cmp hFork |>.setCur (some tb)
          (by intro current hcurrent; simp at hcurrent; subst current; exact htbBound) hsetInput
    have hGeneratedWithElem := hGeneratedInput.emitDef (.refElem view counter) hElem
    have hGeneratedWithValue := hGeneratedWithElem.eachElemValue x byRef elem hValue
    have aElem := advB_emitDef (.refElem view counter) le input elem withElem hElem
    have aValue := advB_eachElemValue x byRef elem le withElem value withValue hValue
    have hcmpLeValue : lsCmp.blocks.size ≤ withValue.blocks.size := by
      have hinputLe := aElem.trans aValue |>.ext.1
      have hids := fork_ids hFork
      have hlsfLe : lsCmp.blocks.size ≤ lsf.blocks.size := by rw [hids.2]; omega
      have hinputBlocks : input.blocks = lsf.blocks := by simp [hInput]
      rw [hinputBlocks] at hinputLe
      exact Nat.le_trans hlsfLe hinputLe
    have hheaderBound : hb < withValue.blocks.size := by
      have hheaderBound := (Array.getElem?_eq_some_iff.mp hlookup).1
      exact Nat.lt_of_lt_of_le hheaderBound (Nat.le_trans (aLen.trans aCmp).ext.1 hcmpLeValue)
    have hxbBound : xb < withValue.blocks.size := by
      have hids := fork_ids hFork
      have hxb : xb = lsCmp.blocks.size + 1 := by simpa using congrArg Prod.snd hids.1
      have hBound : xb < lsf.blocks.size := by
        calc
          xb < lsCmp.blocks.size + 2 := by
            rw [hxb]
            change Nat.succ lsCmp.blocks.size < Nat.succ (Nat.succ lsCmp.blocks.size)
            exact Nat.lt_succ_self _
          _ = lsf.blocks.size := hids.2.symm
      have hinputLe := aElem.trans aValue |>.ext.1
      have hinputBlocks : input.blocks = lsf.blocks := by simp [hInput]
      rw [hinputBlocks] at hinputLe
      exact Nat.lt_of_lt_of_le hBound hinputLe
    have hloopBounds : LoopBuilderTargets
        (some ⟨lsCmp.stack.length, xb, .next hb .i64 counter⟩) withValue := by
      simp only [LoopBuilderTargets]
      exact ⟨hxbBound, hheaderBound⟩
    have aBlock := advB_lowerBlock _ _ _ block le withValue result blockOutput hBlock
    have hextWithValue := hextOutput.of_adv aBlock
    have hframes := LoopBuilderFrames.of_functionTargets htargets hloopBounds hextWithValue
    have htargets' : LoopTargets cx.fn ⟨lsCmp.stack.length, xb, .next hb .i64 counter⟩ := htargets
    refine eachIteration_sim_at fuel cfg env cx le input withElem withValue blockOutput fr (tb, 0) s
      view counter elem value result vw i x idx byRef block ⟨lsCmp.stack.length, xb, .next hb .i64 counter⟩
      org _ hElem hValue hBlock hppInput hextOutput hinv.rel hinv.viewValue hinv.counterValue
      hcounterInput ?_
    intro ev state ptValue frValue hsource PValue hpre
    have hbodySim := hblock fuel hfuel lsCmp.stack.length xb input withElem withValue blockOutput elem value
      result tb i fr s ev state ptValue frValue hElem hValue hBlock hextOutput hcounterInput
      hstackInput hdepth htargets' hppInput hinv hallowed hsource PValue hpre
      hGeneratedWithValue hframes
    exact hbodySim.mono fun flow _ ptAfter after _ hflow =>
      eachLoopFlow_to_step cfg env cx le header input withValue blockOutput lsBack output base fr
        frValue after counter view sampled hb xb lsCmp.stack.length value result owner vw i ev block flow
        ptValue ptAfter hinv PValue hflow hcounterInput hv ho hs hstackInput.symm
        (hstackOutput.trans hstackInput.symm) hppExit hBack hextBack hheader
  exact each_sim_at n cx cfg env x idx byRef block vw (hb, 0) (tb, 0)
    _ _ allowed bodyAllowed (EachFlowPost cfg env cx output counter base) hbranch' henter hbodyEach hretain

end Goose.Lower
