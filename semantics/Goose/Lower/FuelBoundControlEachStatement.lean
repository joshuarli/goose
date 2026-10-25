import Goose.Lower.FuelBoundControlEach
import Goose.Lower.FuelBoundControlEachSource
import Goose.Lower.ReflectionIterationsEachSource

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedStatementFuelBound_each_of_mode {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {x : VarId} {idx : Option VarId} {sourceView : View} {byRef : Bool} {body : Core.Block} {org : OriginId}
    {lc : Option LoopCtx} (child : EachSourceChildFuelBound sourceFuel fuel cfg results sourceView)
    (eachs : ∀ residual, residual < fuel → TypedEachFuelBound sourceFuel residual cfg results x idx sourceView byRef body org)
    (mode : ∀ env state (source : StmtSource cfg env (.forEach x idx sourceView byRef body org) state)
      input point owner irView middle finalPoint, input.pp = some point → GeneratedBuilderState input →
      lowerEachSource sourceView (lowerEnv cfg.mod env.vars results) input = ((owner,irView),middle) →
      middle.pp = some finalPoint → (regrowOf owner (lowerEnv cfg.mod env.vars results) middle).1 =
        eachSourceRegrows source.rootsEnv.access sourceView) :
    TypedStatementFuelBound (sourceFuel + 2) fuel cfg results lc (.forEach x idx sourceView byRef body org) := by
  intro env s source metadata lexical ls ls' pt cx fr hlow hpp hext hrel moduleEq resultsEq depth targets
    counterOuter generated frames
  obtain ⟨plan⟩ := source.eachPlan
  let le := lowerEnv cfg.mod env.vars results
  have aAll := advB_lowerStmt lc (.forEach x idx sourceView byRef body org) le ls () ls' hlow
  obtain ⟨owner, view, lsSource, regrow, sampled, lsSampled, start, lsStart,
    hSource, hRegrow, hSampled, hStart, hLive⟩ :=
    lowerStmt_each_unfold lc x idx sourceView byRef body org le ls ls' hlow
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
  have first := plan.sourceFuelBound results metadata child cx moduleEq resultsEq ls lsSource fr pt
    owner view hSource hpp hextSource hrel generated
  have generatedSource := generated.lowerEachSource sourceView hSource
  have generatedSampled := generatedSource.eachSampled regrow view hSampled
  have generatedStart := generatedSampled.emitDef (.constInt .i64 0) hStart
  have composition : FuelBoundAt (sourceFuel + 1) fuel cx pt fr
      (fun n => execStmt (n + 1) cfg env (.forEach x idx sourceView byRef body org) >>= prepareReturn env)
      (fun flow _ pt' fr' => StmtFlowPost cfg env cx ls fr ls' flow pt' fr') s := by
    simp only [execStmt,bind_assoc]
    refine first.bind ?_
    · intro vw sourceState sourcePoint sourceFrame hSourceRun PSource prefixFuel prefixBound
      have runtime := plan.initial (sourceFuel + 1) vw hSourceRun
      have hmode : regrow = vw.resizable := by
        have equal := mode env s source ls pt owner view lsSource sourcePoint hpp generated hSource PSource.pp
        rw [hRegrow] at equal
        exact equal.trans (eachSourceRegrows_of_aliases runtime.aliases)
      have hview : sourceFrame.vals[view]? = some (.view vw) := PSource.has (view,_) (by simp [EachSourceCells])
      have sampleReflection := eachSampled_fuelBoundAt (sourceFuel + 1) prefixFuel sourceState PSource hview regrow hSampled hextSampled
      have inserted : FuelBoundAt (sourceFuel + 1) prefixFuel cx sourcePoint sourceFrame
          (fun n => (pure () : M Unit) >>= fun _ => (pure () : M Unit) >>= fun _ =>
            execEach n cfg env x idx byRef body vw 0 >>= prepareReturn env)
          (fun flow _ pt' fr' => StmtFlowPost cfg env cx ls fr ls' flow pt' fr') sourceState := by
        refine sampleReflection.bind ?_
        · intro ignoredUnit sampleState samplePoint sampleFrame hSampleRun PSampled startFuel startBound
          have unchanged : sampleState = sourceState := (Res.ok.inj hSampleRun).2.symm
          subst sampleState
          have startReflection := leaf_def_keep_fuelBoundAt (fuel := startFuel) (state := sourceState)
            PSampled hStart hextStart (by simp) (source := fun _ => pure ()) (sourceFuel := sourceFuel + 1)
            (fun _ => RVal.val (.int .i64 0)) (by simp [execPure])
          refine startReflection.bind ?_
          · intro ignoredUnit startState startPoint startFrame hStartRun PStart remaining remainingBound
            have unchanged : startState = sourceState := (Res.ok.inj hStartRun).2.symm
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
                simp only [Option.getD_some]
                rw [hSameEnter r hrBound]
                exact PStart.has (r, _) hmem
            have hownerBound : vw.resizable = true → owner.getD 0 < counter := by
              intro hr
              have hgrow : regrow = true := hmode.trans hr
              cases ho : owner with
              | none => rw [ho, regrowOf_none] at hRegrow; cases (Prod.mk.inj hRegrow).1.trans hgrow
              | some r =>
                simp only [Option.getD_some]
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
            have entry := eachHeader_reflection_entry hNew hTerm hSet PStart.pp hextHeader generatedStart
            rw [hmode] at hEach
            cases remaining with
            | zero => exact FuelBoundAt.zero (sourceFuel + 1) _ _ _ _ _ _
            | succ eachFuel =>
              obtain ⟨headerBlock,headerAt,headerParams⟩ := hHeader
              apply FuelBoundAt.br1 entry.2 headerAt headerParams hstartCell
              have iteration := eachs eachFuel (by omega) env s source plan metadata cx lsHeader ls' counter view sampled hb owner vw
                startFrame hEach hPoint hext ⟨headerBlock,headerAt,headerParams⟩ hCounterBound hviewBound hownerBound
                hsampleBound moduleEq resultsEq entry.1 0 headerFrame sourceState hinit runtime
              have lifted := iteration.source_mono
                (fun n k bound => ((monoAll n k bound).each cfg env x idx byRef body vw 0).bind (fun _ => MonoM.refl _))
                (by omega : sourceFuel ≤ sourceFuel + 1)
              refine lifted.mono ?_
              intro flow state pt' fr' result
              rcases result with ⟨hflow,hpp',hsame,hrel'⟩ | hreturn
              · have hprefix : ls.vals.size ≤ counter := by rw [hCounter']; exact PStart.mono
                exact Or.inl ⟨hflow,Post.nil hpp' aAll.vals
                  (PStart.same.trans (hsame.mono hprefix) (Nat.le_refl _)) hrel'⟩
              · exact Or.inr hreturn
      simpa only [pure_bind] using inserted
  have reflected : FuelBoundAt (sourceFuel + 1) fuel cx pt fr
      (fun n => execStmt (n + 1) cfg env (.forEach x idx sourceView byRef body org) >>= prepareReturn env)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls' lc flow pt' fr') s :=
    composition.mono (fun flow after pt' fr' post =>
      post.elim (fun normal => Or.inl normal) (fun returned => Or.inr (Or.inl returned)))
  refine reflected.of_source (otherFuel := sourceFuel + 2) ?_
  rw [prepareLoopFlow_stmtEach]

theorem typedStatementFuelBound_each_value {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {x : VarId} {idx : Option VarId} {expr : Expr} {byRef : Bool} {body : Core.Block} {org : OriginId}
    {loop : Option LoopCtx} (child : TypedExprFuelBound sourceFuel fuel cfg results expr)
    (eachs : ∀ residual, residual < fuel → TypedEachFuelBound sourceFuel residual cfg results x idx (.val expr) byRef body org) :
    TypedStatementFuelBound (sourceFuel + 2) fuel cfg results loop (.forEach x idx (.val expr) byRef body org) := by
  apply typedStatementFuelBound_each_of_mode (sourceView := .val expr) child eachs
  intro env state source input point owner irView middle finalPoint atPoint generated lowering finalAt
  exact eachSourceMode_val source.rootsEnv.access lowering

theorem typedStatementFuelBound_each_place {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {x : VarId} {idx : Option VarId} {place : Place} {byRef : Bool} {body : Core.Block} {org : OriginId}
    {loop : Option LoopCtx} (child : TypedPlaceFuelBound sourceFuel fuel cfg results place)
    (eachs : ∀ residual, residual < fuel → TypedEachFuelBound sourceFuel residual cfg results x idx (.of place) byRef body org) :
    TypedStatementFuelBound (sourceFuel + 2) fuel cfg results loop (.forEach x idx (.of place) byRef body org) := by
  apply typedStatementFuelBound_each_of_mode (sourceView := .of place) child eachs
  intro env state source input point owner irView middle finalPoint atPoint generated lowering finalAt
  obtain ⟨plan⟩ := source.eachPlan
  obtain ⟨childSource,typing,roots⟩ := plan.viewSource.ofChild
  have mode := eachSourceMode_of_live_place childSource (placeOwnerShape_generated cfg results place) lowering generated finalAt
  simpa only [roots,plan.viewRoots] using mode



end Goose.Lower
