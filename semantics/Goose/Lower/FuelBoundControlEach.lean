import Goose.Lower.FuelBoundControlEachEffects
import Goose.Lower.ReflectionIterationsSteps
import Goose.Lower.FuelBoundTyped
import Goose.Lower.EachTypedStatement

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private def fuelBoundEachTail (n : Nat) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (block : Core.Block) (vw : ViewVal) (i : Nat) (flow : Flow) : M Flow :=
  match flow with
  | .normal _ | .cont => execEach n cfg env x idx byRef block vw (i + 1) >>= prepareReturn env
  | .brk => pure (.normal .unit)
  | .ret value => pure (.ret value)

theorem typedEachFuelBound_step {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {x : VarId} {idx : Option VarId} {viewSource : View} {byRef : Bool} {block : Core.Block} {org : OriginId}
    (blocks : ∀ residual, residual < fuel → ∀ loop pre pre',
      TypedBlockFuelBound sourceFuel residual cfg results (some loop) pre pre' false block)
    (reentry : ∀ residual, residual < fuel → TypedEachFuelBound sourceFuel residual cfg results x idx viewSource byRef block org) :
    TypedEachFuelBound (sourceFuel + 1) fuel cfg results x idx viewSource byRef block org := by
  intro env initial source plan metadata cx ls ls' counter view sampled hb owner vw base hlow hpp hext hheader
    hc hv ho hs moduleEq resultsEq generated i fr s hinv runtime
  let le := lowerEnv cfg.mod env.vars results
  let bodyB := eachBodyBuilder x idx byRef block org view counter hb
  have hlowOriginal := hlow
  change lowerEach vw.resizable owner sampled hb counter bodyB le ls = ((),ls') at hlow
  have hadv : ∀ depth exit, AdvB (bodyB depth exit) := by
    intro depth exit
    exact AdvB.bind (advB_emitDef _) fun elem =>
      AdvB.bind (advB_eachElemValue x byRef elem) fun value => advB_lowerBlock _ _ _ block
  obtain ⟨len,lsLen,cmp,lsCmp,tb,xb,lsf,input,result,output,lsBack,
    hLen,hCmp,hFork,hInput,hBody,hBack,hExit⟩ := lowerEach_unfold hlow
  have aBody := hadv lsCmp.stack.length xb le input result output hBody
  have aBack := advB_rangeBack .i64 counter hb le output () lsBack hBack
  have hextBack : ExtT lsBack cx.fn.blocks := by simpa [hExit,ExtT] using hext
  have hextOutput := hextBack.of_adv aBack
  have hextInput := hextOutput.of_adv aBody
  have hextFork : ExtT lsf cx.fn.blocks := by simpa [hInput,ExtT] using hextInput
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
  have hextLen := hextCmp.of_adv aCmp
  have stackFinal : ls'.stack = ls.stack :=
    (advB_lowerEach vw.resizable owner sampled hb counter hadv le ls () ls' hlow).stack
  have generatedLen := generated.eachLen vw.resizable owner sampled hLen
  have generatedCmp := generatedLen.emitDef (.cmp .lt .i64 counter len) hCmp
  have generatedFork := generatedCmp.fork cmp hFork
  have generatedInput : GeneratedBuilderState input := by
    rw [hInput]
    exact ⟨generatedFork.dense,by
      intro current same
      have equal := Option.some.inj same
      rw [← equal]
      exact (Array.getElem?_eq_some_iff.mp hfacts.2.2.2.2.2.2.2.1).1,generatedFork.targets⟩
  have headerBound : hb < input.blocks.size := by
    rw [hInput]
    exact Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hlookup).1
      (Nat.le_trans (aLen.trans aCmp).ext.1 (advB_fork cmp _ _ _ _ hFork).ext.1)
  have exitBound : xb < input.blocks.size := by
    rw [hInput]; exact (Array.getElem?_eq_some_iff.mp hfacts.2.2.2.2.2.2.2.2).1
  have bodyTargets : LoopTargets cx.fn ⟨lsCmp.stack.length,xb,.next hb .i64 counter⟩ :=
    ⟨⟨exitBlock,hExitBlock,hExitParams⟩,hheader⟩
  have bodyFrames : LoopBuilderFrames (some ⟨lsCmp.stack.length,xb,.next hb .i64 counter⟩) input := by
    apply LoopBuilderFrames.of_functionTargets bodyTargets ⟨exitBound,headerBound⟩ hextInput
  dsimp only [bodyB,eachBodyBuilder] at hBody
  simp only [bind_eq] at hBody
  obtain ⟨elem,withElem,hElem,value,withValue,hValue,hBlock⟩ := hBody
  have aBlock := advB_lowerBlock (some ⟨lsCmp.stack.length,xb,.next hb .i64 counter⟩)
    (eachIRPre x idx value counter org) false block le withValue result output hBlock
  have hextValue := hextOutput.of_adv aBlock
  have hextElem := hextValue.of_adv (advB_eachElemValue x byRef elem _ _ _ _ hValue)
  have generatedElem := generatedInput.emitDef (.refElem view counter) hElem
  have generatedValue := generatedElem.of_runs (Validation.dense_eachElemValue x byRef elem)
    (generatedTargets_eachElemValue none x byRef elem) trivial hValue
  have framesValue := (bodyFrames.mono (adv_emitDef hElem).ext).mono
    (advB_eachElemValue x byRef elem _ _ _ _ hValue).ext
  have contextDepth : lsCmp.stack.length = env.scopes.length := by
    rw [hdepth,hstackInput,hinv.rel.stack,List.length_map]
  have lengthReflection := eachLen_fuelBoundAt sourceFuel fuel s runtime.typedView hinv hc hv ho hs hLen hpp hextLen
  have reflected : FuelBoundAt sourceFuel fuel cx (hb,0) fr
      (fun n => preparedEach n cfg env x idx byRef block vw i)
      (fun flow _ pt' fr' => EachFlowPost cfg env cx ls' counter base flow pt' fr') s := by
    unfold preparedEach
    refine lengthReflection.bind ?_
    · intro length afterLength ptLen frLen lengthRun lengthPost remaining remainingBound
      have unchanged : afterLength = s := eachLength_state lengthRun
      subst afterLength
      obtain ⟨PLength,invariantLen⟩ := lengthPost
      have hcounter := invariantLen.counterValue
      have hlength : frLen.vals[len]? = some (.val (.int .i64 length)) := PLength.has (len,_) (by simp)
      have comparePure : execPure cx frLen (.cmp .lt .i64 counter len) =
          pure (.val (.bool (i < length))) := by
        have typed := (execPure_cmp (cx := cx) (fr := frLen) (op := .lt) hcounter hlength).1 IntTy.i64
        rw [typed]
        simp [expectComparable,expectSameTy,evalCmp]
      obtain ⟨_,_,_,ppCmp,instructionCmp⟩ := emitDef_facts hCmp PLength.pp hextCmp
      have instruction : instAt cx.fn ptLen = some (.def cmp (.cmp .lt .i64 counter len)) := instructionCmp
      let comparedFrame := frLen.set cmp (.val (.bool (i < length)))
      have PCompare : Post cfg env cx ls fr lsCmp comparedFrame (ptLen.1,ptLen.2 + 1)
          [(cmp,.val (.bool (i < length)))] :=
        (Post.def_leaf PLength hCmp hextCmp (.val (.bool (i < length)))).1
      have invariantCmp := hinv.of_post PCompare hc hv ho hs
      obtain ⟨Ttb,hTtb,hTtbp⟩ := hextFork.params hfacts.2.2.2.2.2.2.2.1
      have branchAt : instAt cx.fn (ptLen.1,ptLen.2 + 1) = some (.term (.condbr cmp tb [] xb [])) := by
        have pointEq : (ptLen.1,ptLen.2 + 1) = (hb,blockCmp.insts.size) :=
          Option.some.inj (ppCmp.symm.trans (LS.pp_eq hcurCmp hlookupCmp))
        rw [pointEq]
        exact hfacts.2.2.2.2.2.2.1
      have condition : comparedFrame.vals[cmp]? = some (.val (.bool (i < length))) := Frame.set_get _ _ _
      have invariantInput : EachInv cfg env cx input counter view sampled owner vw base i comparedFrame :=
        { invariantCmp with rel := invariantCmp.rel.stack_eq (by rw [hInput]; exact hfacts.2.2.2.2.1) }
      cases remaining with
      | zero => exact FuelBoundAt.zero sourceFuel _ _ _ _ _ _
      | succ compareFuel =>
        refine FuelBoundAt.step (congrFun
          (runAt_defPure_step instruction (by simp) comparePure compareFuel) s) ?_
        change FuelBoundAt sourceFuel compareFuel cx (ptLen.1,ptLen.2 + 1) comparedFrame _ _ s
        cases compareFuel with
        | zero => exact FuelBoundAt.zero sourceFuel _ _ _ _ _ _
        | succ branchFuel =>
          by_cases inside : i < length
          · have trueValue : comparedFrame.vals[cmp]? = some (.val (.bool true)) := by
              simpa [inside] using condition
            simp only [inside,ite_true]
            apply FuelBoundAt.condbr_take0 branchAt trueValue hTtb hTtbp rfl
            have location := eachElement_typed_location runtime.typedView lengthRun inside
            have elemPure := execPure_eachElem (cx := cx) invariantInput.viewValue invariantInput.counterValue
            have elemInstruction := (Post.def_leaf (Post.init invariantInput.rel hppInput)
              hElem hextElem (.val (.ref ⟨vw.loc.root,vw.loc.path ++ [vw.start + i]⟩))).2
            let elemFrame := comparedFrame.set elem (.val (.ref ⟨vw.loc.root,vw.loc.path ++ [vw.start + i]⟩))
            have PElem : Post cfg env cx input comparedFrame withElem elemFrame (tb,1)
                [(elem,.val (.ref ⟨vw.loc.root,vw.loc.path ++ [vw.start + i]⟩))] :=
              (Post.def_leaf (Post.init invariantInput.rel hppInput) hElem hextElem _).1
            cases branchFuel with
            | zero => exact FuelBoundAt.zero sourceFuel _ _ _ _ _ _
            | succ elementFuel =>
              refine FuelBoundAt.step (congrFun
                (runAt_defPure_step elemInstruction (by simp) elemPure elementFuel) s) ?_
              have elementReflection := eachElemValue_fuelBoundAt sourceFuel elementFuel s PElem x byRef le hValue hextValue
              refine elementReflection.bind ?_
              · intro element elementState ptValue valueFrame elementRun PValue bodyFuel bodyBound
                have elementStateEq := (eachElement_success location elementRun).1
                subst elementState
                obtain ⟨child,typing,roots,world,observation,_,_,future,retained,may,_⟩ :=
                  runtime.bodySource i element location elementRun
                have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
                  rw [typing,roots]; exact metadata
                have childLoops : LoopSourceMatches child.typingEnv
                    (some ⟨lsCmp.stack.length,xb,.next hb .i64 counter⟩) := by
                  rw [LoopSourceMatches,typing]; simp
                have counterValue : valueFrame.vals[counter]? = some (.val (.int .i64 i)) := by
                  rw [PValue.same counter hcounterInput]; exact invariantInput.counterValue
                have pre : PreRel valueFrame (eachIRPre x idx value counter org) (eachCorePre x idx element i) := by
                  have cell := PValue.has (value,.val element) (by simp)
                  cases idx <;> simp [PreRel,eachIRPre,eachCorePre,cell,counterValue]
                have bodyReflection := blocks bodyFuel (by omega) _ _ _ env s child childMetadata childLoops
                  withValue output result ptValue cx valueFrame hBlock PValue.pp hextOutput PValue.rel pre moduleEq resultsEq
                  (by change lsCmp.stack.length ≤ env.scopes.length; omega) bodyTargets
                  ⟨Nat.lt_of_lt_of_le hcounterInput PValue.mono,.i64,i,counterValue⟩ generatedValue framesValue
                rw [prepareLoopFlow_at_depth env _ contextDepth] at bodyReflection
                change FuelBoundAt sourceFuel bodyFuel cx ptValue valueFrame
                  (fun n => (execBlock n cfg env (eachCorePre x idx element i) block >>= prepareReturn env) >>=
                    fuelBoundEachTail n cfg env x idx byRef block vw i) _ s
                refine bodyReflection.bind ?_
                · intro flow after ptAfter afterFrame done matched backFuel backBound
                  have invariantValue := invariantInput.of_post PValue hcounterInput hv ho hs
                  have counterWith := Nat.lt_of_lt_of_le hcounterInput PValue.mono
                  rcases matched with ⟨v,rfl,_,PBlock⟩ | returned | ⟨loopContext,loopEq,transfer⟩
                  · simp only [fuelBoundEachTail]
                    have raw := preparedReturn_nonreturn_success done (by intro v h; cases h)
                    have nextRuntime := runtime.afterBody child typing roots world observation future retained may
                      sourceFuel (.normal v) raw
                    have invariantBody := invariantValue.of_post PBlock counterWith hv ho hs
                    obtain ⟨nextFrame,oneTimeout,exactBack,sameNext,nextValue,activation,scopes,frameDepth⟩ :=
                      rangeBack_exact cx le output lsBack ptAfter afterFrame counter hb .i64 .i64 (i : Int)
                        hBack PBlock.pp hextBack (Nat.lt_of_lt_of_le counterWith PBlock.mono)
                        invariantBody.counterValue hheader
                    have nextRel : Rel cfg env cx nextFrame ls :=
                      ⟨hinv.rel.prof,hinv.rel.slots,activation.trans invariantBody.rel.act,
                        scopes.trans invariantBody.rel.scopes,frameDepth.trans invariantBody.rel.depth,hinv.rel.stack⟩
                    have nextInvariant := invariantBody.reentry sameNext (by simpa using nextValue) nextRel hv ho hs
                    cases backFuel with
                    | zero => exact FuelBoundAt.zero sourceFuel _ _ _ _ _ _
                    | succ backFuel =>
                      cases backFuel with
                      | zero =>
                        intro result nonTimeout run
                        exact (nonTimeout after (run.symm.trans (congrFun oneTimeout after))).elim
                      | succ nextFuel =>
                        have nextReflection := reentry nextFuel (by omega) env initial source plan metadata cx
                          ls ls' counter view sampled hb owner vw base hlowOriginal hpp hext hheader hc hv ho hs
                          moduleEq resultsEq generated (i + 1) nextFrame after nextInvariant nextRuntime
                        intro result nonTimeout run
                        have run' : runAt cx (hb,0) nextFrame nextFuel after = result := by
                          rw [← exactBack nextFuel]; exact run
                        rcases nextReflection result nonTimeout run' with success | stopped
                        · obtain ⟨v,final,pt',fr',residual,sourceRun,post,bound,targetRun⟩ := success
                          exact Or.inl ⟨v,final,pt',fr',residual,sourceRun,post,by omega,targetRun⟩
                        · exact Or.inr stopped
                  · obtain ⟨v,origin,rfl,site⟩ := returned
                    exact FuelBoundAt.ret (Or.inr ⟨v,origin,rfl,site⟩)
                  · obtain rfl := Option.some.inj loopEq
                    rcases transfer with ⟨rfl,pointEq,exitFrame⟩ | ⟨rfl,continued⟩
                    · simp only [fuelBoundEachTail]
                      have sameFinal := invariantValue.values.trans
                        (exitFrame.values.mono (Nat.le_of_lt counterWith)) (Nat.le_refl _)
                      have finalRel : Rel cfg env cx afterFrame ls' :=
                        ⟨hinv.rel.prof,hinv.rel.slots,exitFrame.activation.trans PValue.rel.act,
                          by simpa [contextDepth] using exitFrame.scopesEqual,
                          exitFrame.depth.trans PValue.rel.depth,stackFinal.trans hinv.rel.stack⟩
                      exact FuelBoundAt.ret (Or.inl ⟨rfl,pointEq.symm ▸ hppExit,sameFinal,finalRel⟩)
                    · simp only [fuelBoundEachTail]
                      obtain ⟨runtimeTy,old,beforeValue,next⟩ := continued
                      have valueEq := Option.some.inj (beforeValue.symm.trans counterValue)
                      obtain ⟨typeEq,indexEq⟩ := Val.int.inj (RVal.val.inj valueEq)
                      subst runtimeTy
                      subst old
                      have nextRel : Rel cfg env cx afterFrame ls :=
                        ⟨hinv.rel.prof,hinv.rel.slots,next.activation.trans PValue.rel.act,
                          by simpa [contextDepth] using next.scopesEqual,
                          next.depth.trans PValue.rel.depth,hinv.rel.stack⟩
                      have nextInvariant := invariantValue.reentry next.values
                        (by simpa using next.counterValue) nextRel hv ho hs
                      have raw := preparedReturn_nonreturn_success done (by intro v h; cases h)
                      have nextRuntime := runtime.afterBody child typing roots world observation future retained may sourceFuel .cont raw
                      have nextReflection := reentry backFuel (by omega) env initial source plan metadata cx
                        ls ls' counter view sampled hb owner vw base hlowOriginal hpp hext hheader hc hv ho hs
                        moduleEq resultsEq generated (i + 1) afterFrame after nextInvariant nextRuntime
                      rw [next.point]
                      exact nextReflection
          · have falseValue : comparedFrame.vals[cmp]? = some (.val (.bool false)) := by
              simpa [inside] using condition
            simp only [inside,ite_false]
            apply FuelBoundAt.condbr_take0 branchAt falseValue hExitBlock hExitParams rfl
            exact FuelBoundAt.ret (Or.inl ⟨rfl,hppExit,invariantCmp.values,
              invariantCmp.rel.stack_eq (stackFinal.trans (aCmp.stack.trans aLen.stack).symm)⟩)
  exact reflected.of_source (otherFuel := sourceFuel + 1)
    (congrFun (prepareReturn_execEach sourceFuel cfg env x idx byRef block vw i) s)


#print axioms typedEachFuelBound_step

end Goose.Lower
