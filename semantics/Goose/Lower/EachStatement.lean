import Goose.Lower.EachHeader
import Goose.Lower.EachRuntime

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem stmt_each_normal_sim_at (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (le : LEnv) (ls ls' : LS) (fr : Frame) (pt : Pt) (s : St)
    (lc : Option LoopCtx) (x : VarId) (idx : Option VarId) (source : View)
    (byRef : Bool) (body : Core.Block) (org : OriginId) (hok : blockOk body = true)
    (sourceEnv after : TEnv) (sc next next' : Nat) (hvars : sourceEnv.vars = env.vars)
    (htype : tyStmt sourceEnv sc (.forEach x idx source byRef body org) next = .ok (after, next'))
    (penv : PEnv) (world : Core.Sound.World) (element : Ty)
    (hsource : ∀ owner view output,
      lowerEachSource source le ls = ((owner, view), output) → ExtT output cx.fn.blocks →
      SimEAt cx pt fr (evalView n cfg env source)
        (fun vw pt' fr' => Post cfg env cx ls fr output fr' pt' (EachSourceCells owner view vw)) s)
    (hsourceAliases : ∀ vw state, evalView n cfg env source s = .ok vw state →
      Core.Sound.ViewAliases cfg.mod world penv env state.store source vw element)
    (hsourceMode : ∀ owner view output,
      lowerEachSource source le ls = ((owner, view), output) →
      ∀ vw state, evalView n cfg env source s = .ok vw state →
      (regrowOf owner le output).1 = eachSourceRegrows penv.access source)
    (hlow : lowerStmt lc (.forEach x idx source byRef body org) le ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.forEach x idx source byRef body org) >>= prepareReturn env)
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) s := by
  have aAll := advB_lowerStmt lc (.forEach x idx source byRef body org) le ls () ls' hlow
  obtain ⟨owner, view, lsSource, regrow, sampled, lsSampled, start, lsStart,
    hSource, hRegrow, hSampled, hStart, hLive⟩ :=
    lowerStmt_each_unfold lc x idx source byRef body org le ls ls' hlow
  have aLive : lsStart.Adv ls' := advB_whenLive () (fun _ =>
    advB_header1 (.data (.int .i64)) start
      (tail := fun hb counter => lowerEach regrow owner sampled hb counter
        (eachBodyBuilder x idx byRef body org view counter hb))
      (fun hb counter => advB_lowerEach regrow owner sampled hb counter
        (fun _ _ => by
          unfold eachBodyBuilder
          exact AdvB.bind (advB_emitDef _) fun elem =>
            AdvB.bind (advB_eachElemValue x byRef elem) fun value => advB_lowerBlock _ _ _ body)))
    le lsStart () ls' hLive
  have hextStart := hext.of_adv aLive
  have hextSampled := hextStart.of_adv (adv_emitDef hStart)
  have hextSource := hextSampled.of_adv (advB_eachSampled regrow view le lsSource sampled lsSampled hSampled)
  simp only [execStmt, bind_assoc]
  refine SimEAt.bind (hsource owner view lsSource hSource hextSource)
    fun vw sourceState sourcePoint sourceFrame hSourceRun PSource => ?_
  have hmode : regrow = vw.resizable := by
    have hm := hsourceMode owner view lsSource hSource vw sourceState hSourceRun
    rw [hRegrow] at hm
    exact hm.trans (eachSourceRegrows_of_aliases (hsourceAliases vw sourceState hSourceRun))
  have hview : sourceFrame.vals[view]? = some (.view vw) :=
    PSource.has (view, _) (by simp [EachSourceCells])
  have hsampleSim := eachSampled_sim PSource hview regrow hSampled hextSampled
  have hunit : (execEach n cfg env x idx byRef body vw 0 >>= prepareReturn env) =
      (pure () >>= fun _ => execEach n cfg env x idx byRef body vw 0 >>= prepareReturn env) := by simp
  rw [hunit]
  refine SimEAt.bind (SimEAt.of_simG hsampleSim sourceState)
    fun _ sampleState samplePoint sampleFrame hSampleRun PSampled => ?_
  have hSampleState : sampleState = sourceState := (Res.ok.inj (by simpa only [pure_apply] using hSampleRun)).2.symm
  subst sampleState
  have hstartSim := leaf_def_keep (c := pure ()) PSampled hStart hextStart (by simp)
    (fun _ => RVal.val (.int .i64 0)) (by simp [execPure])
  rw [hunit]
  refine SimEAt.bind (SimEAt.of_simG hstartSim sourceState)
    fun _ startState startPoint startFrame hStartRun PStart => ?_
  have hStartState : startState = sourceState := (Res.ok.inj (by simpa only [pure_apply] using hStartRun)).2.symm
  subst startState
  obtain ⟨_, hcurStart, _, _⟩ := LS.pp_some PStart.pp
  rw [whenLive_some _ _ _ hcurStart] at hLive
  simp only [bind_eq] at hLive
  obtain ⟨⟨hb, params⟩, lsNew, hNew, u1, lsClosed, hTerm, u2, lsHeader, hSet, hEach⟩ := hLive
  have aEach := advB_lowerEach regrow owner sampled hb (params.headD 0)
    (fun _ _ => by
      exact AdvB.bind (advB_emitDef _) fun elem =>
        AdvB.bind (advB_eachElemValue x byRef elem) fun value => advB_lowerBlock _ _ _ body)
    le lsHeader () ls' hEach
  have hextHeader := hext.of_adv aEach
  have hstartCell : startFrame.vals[start]? = some (.val (.int .i64 0)) := PStart.has (start, _) (by simp)
  obtain ⟨hCounter, hCounterBound, hStack, hPoint, hHeader, hEnter, hSameEnter, hCounterCell, hRelHeader⟩ :=
    eachHeader_setup cfg env cx le lsStart lsNew lsClosed lsHeader startFrame startPoint start hb params
      hNew hTerm hSet PStart.pp hextHeader PStart.rel hstartCell
  let counter := params.headD 0
  let headerFrame := startFrame.set counter (.val (.int .i64 0))
  have hCounter' : counter = lsStart.vals.size := hCounter
  have hviewCell : (view, .view vw) ∈
      ((start, RVal.val (.int .i64 0)) ::
        (if regrow then EachSourceCells owner view vw
          else (sampled, .val (.int .i64 vw.len)) :: EachSourceCells owner view vw)) := by
    cases regrow <;> simp [EachSourceCells]
  have hviewBound : view < counter := by rw [hCounter']; exact PStart.lt (view, _) hviewCell
  have hviewHeader : headerFrame.vals[view]? = some (.view vw) := by
    rw [hSameEnter view hviewBound]
    exact PStart.has (view, _) hviewCell
  have hownerHeader : vw.resizable = true → headerFrame.vals[owner.getD 0]? = some (.val (.ref vw.loc)) := by
    intro hr
    have hgrow : regrow = true := hmode.trans hr
    cases ho : owner with
    | none => rw [ho, regrowOf_none] at hRegrow; cases (Prod.mk.inj hRegrow).1.trans hgrow
    | some r =>
      have hmem : (r, RVal.val (.ref vw.loc)) ∈
          ((start, RVal.val (.int .i64 0)) ::
            (if regrow then EachSourceCells owner view vw
              else (sampled, .val (.int .i64 vw.len)) :: EachSourceCells owner view vw)) := by
        simp [EachSourceCells, ho, hgrow]
      have hrBound : r < counter := by rw [hCounter']; exact PStart.lt (r, _) hmem
      simp only [ho, Option.getD_some]
      rw [hSameEnter r hrBound]
      exact PStart.has (r, _) hmem
  have hownerBound : vw.resizable = true → owner.getD 0 < counter := by
    intro hr
    have hgrow : regrow = true := hmode.trans hr
    cases ho : owner with
    | none => rw [ho, regrowOf_none] at hRegrow; cases (Prod.mk.inj hRegrow).1.trans hgrow
    | some r =>
      simp only [ho, Option.getD_some]
      rw [hCounter']
      exact PStart.lt (r, .val (.ref vw.loc)) (by simp [EachSourceCells, ho, hgrow])
  have hsampleBound : vw.resizable = false → sampled < counter := by
    intro hr
    have hfixed : regrow = false := hmode.trans hr
    rw [hCounter']
    exact PStart.lt (sampled, .val (.int .i64 vw.len)) (by simp [hfixed])
  have hsampleHeader : vw.resizable = false → headerFrame.vals[sampled]? = some (.val (.int .i64 vw.len)) := by
    intro hr
    have hfixed : regrow = false := hmode.trans hr
    rw [hSameEnter sampled (hsampleBound hr)]
    exact PStart.has (sampled, _) (by simp [hfixed])
  have hinit : EachInv cfg env cx lsHeader counter view sampled owner vw startFrame 0 headerFrame :=
    ⟨hSameEnter, hCounterCell, hviewHeader, hownerHeader, hsampleHeader, hRelHeader⟩
  have hscopes := tyStmt_each_scopes sourceEnv sc x idx source byRef body org next next' after htype
  rw [hvars] at hscopes
  have hscope : (∃ lv, env.vars[x]? = some lv ∧ lv.scope = body.scope) ∧
      (∀ j, idx = some j → ∃ lv, env.vars[j]? = some lv ∧ lv.scope = body.scope) :=
    ⟨hscopes.1, fun j hj => by obtain ⟨lv, hv, hs, _⟩ := hscopes.2 j hj; exact ⟨lv, hv, hs⟩⟩
  rw [hmode] at hEach
  apply SimEAt.goes hEnter
  refine ((lowerEach_normal_sim n cfg env cx le lsHeader ls' counter view sampled hb
    owner vw startFrame x idx byRef body org hok hscope hEach hPoint hext hHeader hCounterBound
    hviewBound hownerBound hsampleBound 0 headerFrame hinit).at_state sourceState).mono ?_
  intro flow state pt' fr' _ hresult
  obtain ⟨hflow, hpp', hsame, hrel'⟩ := hresult
  have hprefix : ls.vals.size ≤ counter := by rw [hCounter']; exact PStart.mono
  exact ⟨hflow, Post.nil hpp' aAll.vals (PStart.same.trans (hsame.mono hprefix) (Nat.le_refl _)) hrel'⟩

end Goose.Lower
