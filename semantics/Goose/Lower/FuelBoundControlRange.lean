import Goose.Lower.FuelBoundTyped
import Goose.Lower.FuelBoundControlSteps
import Goose.Lower.ReflectionIterationsSteps
import Goose.Lower.RangeStatements

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private def fuelBoundRangeTail (n : Nat) (cfg : Cfg) (env : Env) (x : VarId) (ty : IntTy)
    (current upper : Int) (body : Core.Block) (flow : Flow) : M Flow :=
  match flow with
  | .normal _ | .cont => execRange n cfg env x ty (current + 1) upper body >>= prepareReturn env
  | .brk => pure (.normal .unit)
  | .ret value => pure (.ret value)

theorem typedRangeFuelBound_step {n fuel : Nat} {cfg : Cfg} {results : List Ty}
    {x : VarId} {lo hi : Expr} {block : Core.Block} {org : OriginId}
    (blocks : ∀ residual, residual < fuel → ∀ loop pre pre',
      TypedBlockFuelBound n residual cfg results (some loop) pre pre' false block)
    (reentry : ∀ residual, residual < fuel → TypedRangeFuelBound n residual cfg results x lo hi block org) :
    TypedRangeFuelBound (n + 1) fuel cfg results x lo hi block org := by
  intro env initial source plan metadata cx header output counter bound hb hint upper base lowered atHeader
    extension headerBlock boundBeforeCounter counterInHeader moduleEq resultsEq generated current frame state
    invariant runtime
  let le := lowerEnv cfg.mod env.vars results
  let runtimeType := plan.intTy
  have loweredOriginal := lowered
  let bodyB := fun depth xb =>
    lowerBlock (some ⟨depth, xb, .next hb hint counter⟩)
      [(x, counter, org)] false block
  change lowerRange hint counter bound hb bodyB le header = ((), output) at lowered
  obtain ⟨condition, compared, bodyPoint, exit, forked, input, result, bodyOutput, back,
      hcompare, hfork, hinput, hlowerBody, hback, hexit⟩ := lowerRange_unfold lowered
  have backAdvances := advB_rangeBack hint counter hb le bodyOutput () back hback
  have extensionBack : ExtT back cx.fn.blocks := by
    simpa [hexit, ExtT] using extension
  have extensionBody := extensionBack.of_adv backAdvances
  have bodyAdvances' := advB_lowerBlock
    (some ⟨compared.stack.length, exit, .next hb hint counter⟩)
    [(x, counter, org)] false block le input result bodyOutput hlowerBody
  have extensionInput := extensionBody.of_adv bodyAdvances'
  have extensionFork : ExtT forked cx.fn.blocks := by
    simpa [hinput, ExtT] using extensionInput
  obtain ⟨entryBlock, entryLive, _, _⟩ := LS.pp_some atHeader
  have conditionLive : compared.cur = some hb := by
    have run := emitDef_run (.cmp .lt hint counter bound) le entryLive
    rw [run] at hcompare
    have stateEq := (Prod.mk.inj hcompare).2
    calc
      compared.cur = header.cur := by simpa using (congrArg LS.cur stateEq).symm
      _ = some hb := entryLive
  have extensionForked := extensionFork.of_adv (adv_fork conditionLive hfork)
  obtain ⟨conditionId, compareSize, compareStack, comparePoint, compareInstruction⟩ :=
    rangeCompare_facts hcompare atHeader extensionForked
  obtain ⟨_, _, _, forkValues, forkStack, _,
    forkTerm, bodyBlockLive, exitBlockLive⟩ := fork_facts hfork comparePoint extensionFork
  obtain ⟨bodyTarget, bodyTargetLive, bodyParams⟩ := extensionFork.params bodyBlockLive
  obtain ⟨exitTarget, exitTargetLive, exitParams⟩ := extensionFork.params exitBlockLive
  have compareAt : instAt cx.fn (hb, 0) = some (.def condition (.cmp .lt hint counter bound)) := by
    rw [instAt_eq]
    exact compareInstruction
  have branchAt : instAt cx.fn (hb, 1) = some (.term (.condbr condition bodyPoint [] exit [])) := by
    rw [instAt_eq]
    exact forkTerm
  have inputValueSize : input.vals.size = header.vals.size + 1 := by
    rw [hinput]
    change forked.vals.size = _
    rw [forkValues, compareSize]
  have inputStack : input.stack = header.stack := by
    rw [hinput]
    exact forkStack.trans compareStack
  have bodyPointInput : input.pp = some (bodyPoint, 0) := by
    rw [hinput]
    exact LS.pp_cur bodyBlockLive
  have bodyDepth : compared.stack.length = input.stack.length := by
    rw [inputStack]
    exact congrArg List.length compareStack
  have bodyCounterBound : counter < input.vals.size := by
    rw [inputValueSize]
    exact Nat.lt_trans counterInHeader (Nat.lt_succ_self _)
  have bodyTargets : ∀ depth,
      LoopTargets cx.fn ⟨depth, exit, .next hb hint counter⟩ := by
    intro depth
    exact ⟨⟨exitTarget, exitTargetLive, exitParams⟩, headerBlock⟩
  have outputExitBlock : back.blocks[exit]? = some ⟨[], #[]⟩ := by
    refine (bodyAdvances'.trans backAdvances).keep exit ⟨[], #[]⟩ ?_ ?_
    · rw [hinput]
      intro sameBlock
      have blockEq : bodyPoint = exit := Option.some.inj sameBlock
      have ids := fork_ids hfork
      obtain ⟨bodyId, exitId⟩ := Prod.mk.inj ids.1
      have bodyLess : bodyPoint < exit := by
        rw [bodyId, exitId]
        exact Nat.lt_succ_self _
      exact (Nat.ne_of_lt bodyLess) blockEq
    · rw [hinput]
      exact exitBlockLive
  have exitPoint : output.pp = some (exit, 0) := by
    rw [hexit]
    exact LS.pp_cur outputExitBlock
  have headerStackOutput : output.stack = header.stack := by
    rw [hexit]
    exact backAdvances.stack.trans
      (bodyAdvances'.stack.trans (by rw [hinput]; exact forkStack.trans compareStack))
  obtain ⟨same,counterValue,boundValue,related⟩ := invariant
  have comparePure : execPure cx frame (.cmp .lt hint counter bound) =
      pure (.val (.bool (current < upper))) := by
    have typedCompare := (execPure_cmp (cx := cx) (fr := frame) (op := .lt)
      counterValue boundValue).1 hint
    rw [typedCompare]
    simp [expectComparable,expectSameTy,evalCmp]
  let comparedFrame := frame.set condition (.val (.bool (current < upper)))
  have conditionValue : comparedFrame.vals[condition]? = some (.val (.bool (current < upper))) :=
    Frame.set_get _ _ _
  have counterCompared : comparedFrame.vals[counter]? = some (.val (.int plan.intTy current)) := by
    have different : counter ≠ condition := by rw [conditionId]; exact Nat.ne_of_lt counterInHeader
    simpa [comparedFrame,Frame.set,Std.HashMap.getElem?_insert,different.symm] using counterValue
  have boundCompared : comparedFrame.vals[bound]? = some (.val (.int plan.intTy upper)) := by
    have different : bound ≠ condition := by
      rw [conditionId]; exact Nat.ne_of_lt (Nat.lt_trans boundBeforeCounter counterInHeader)
    simpa [comparedFrame,Frame.set,Std.HashMap.getElem?_insert,different.symm] using boundValue
  have sameComparedLocal : Same counter frame comparedFrame := by
    apply Same.set
    rw [conditionId]; exact Nat.le_of_lt counterInHeader
  have sameCompared := same.trans sameComparedLocal (Nat.le_refl _)
  have relatedCompared : Rel cfg env cx comparedFrame header := related.set _ _
  have inputRel := relatedCompared.stack_eq inputStack
  have inputInvariant : RangeInv cfg env cx input counter bound plan.intTy upper base current comparedFrame :=
    ⟨sameCompared,counterCompared,boundCompared,inputRel⟩
  have compareGenerated := generated.emitDef (.cmp .lt hint counter bound) hcompare
  have forkGenerated := compareGenerated.fork condition hfork
  have inputGenerated : GeneratedBuilderState input := by
    rw [hinput]
    exact ⟨forkGenerated.dense,by
      intro current equal
      have eq := Option.some.inj equal
      rw [← eq]
      exact (Array.getElem?_eq_some_iff.mp bodyBlockLive).1,forkGenerated.targets⟩
  have headerBound : hb < input.blocks.size := by
    obtain ⟨b,_,located,_⟩ := LS.pp_some atHeader
    rw [hinput]
    exact Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp located).1
      (Nat.le_trans (adv_emitDef hcompare).ext.1 (advB_fork condition _ _ _ _ hfork).ext.1)
  have exitBound : exit < input.blocks.size := by
    rw [hinput]; exact (Array.getElem?_eq_some_iff.mp exitBlockLive).1
  have bodyFrames : LoopBuilderFrames
      (some ⟨compared.stack.length,exit,.next hb hint counter⟩) input := by
    apply LoopBuilderFrames.of_functionTargets (bodyTargets compared.stack.length) ?_ extensionInput
    exact ⟨exitBound,headerBound⟩
  have contextDepth : compared.stack.length = env.scopes.length := by
    rw [compareStack,related.stack,List.length_map]
  have reflection : FuelBoundAt n fuel cx (hb,0) frame
      (fun n => preparedRange n cfg env x plan.intTy current upper block)
      (fun flow _ pt' fr' => RangeFlowPost cfg env cx output counter base flow pt' fr') state := by
    cases fuel with
    | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
    | succ compareFuel =>
      refine FuelBoundAt.step (congrFun
        (runAt_defPure_step compareAt (by simp) comparePure compareFuel) state) ?_
      cases compareFuel with
      | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
      | succ branchFuel =>
        change FuelBoundAt n (branchFuel + 1) cx (hb,1) comparedFrame _ _ state
        by_cases inside : current < upper
        · have trueValue : comparedFrame.vals[condition]? = some (.val (.bool true)) := by
            simpa [inside] using conditionValue
          unfold preparedRange
          simp only [inside,ite_true]
          apply FuelBoundAt.condbr_take0 branchAt trueValue bodyTargetLive bodyParams rfl
          obtain ⟨child,typing,roots,world,observation,_,_,future,retained,may,_⟩ := runtime.bodyChild rfl current
          have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
            rw [typing,roots]; exact metadata
          have childLoops : LoopSourceMatches child.typingEnv
              (some ⟨compared.stack.length,exit,.next hb hint counter⟩) := by
            rw [LoopSourceMatches,typing]; simp
          have bodyReflection := blocks branchFuel (by omega) _ _ _ env state child childMetadata childLoops
            input bodyOutput result (bodyPoint,0) cx comparedFrame hlowerBody bodyPointInput extensionBody inputRel
            (by simp [PreRel,counterCompared]) moduleEq resultsEq (by change compared.stack.length ≤ env.scopes.length; omega)
            (bodyTargets _) ⟨bodyCounterBound,plan.intTy,current,counterCompared⟩ inputGenerated bodyFrames
          rw [prepareLoopFlow_at_depth env _ contextDepth] at bodyReflection
          change FuelBoundAt n branchFuel cx (bodyPoint,0) comparedFrame
            (fun n => (execBlock n cfg env [(x,.int plan.intTy current)] block >>= prepareReturn env) >>=
              fuelBoundRangeTail n cfg env x plan.intTy current upper block) _ state
          refine bodyReflection.bind ?_
          · intro flow after point afterFrame done matched remaining remainingBound
            rcases matched with ⟨value,rfl,_,P⟩ | returned | ⟨loopContext,loopEq,transfer⟩
            · simp only [fuelBoundRangeTail]
              have raw := preparedReturn_nonreturn_success done (by intro v h; cases h)
              have nextRuntime := runtime.afterBody rfl child typing roots world observation future retained may
                n (.normal value) raw (Or.inr ⟨value,rfl⟩)
              have counterBody : afterFrame.vals[counter]? = some (.val (.int plan.intTy current)) := by
                rw [P.same counter bodyCounterBound]; exact counterCompared
              have boundBody : afterFrame.vals[bound]? = some (.val (.int plan.intTy upper)) := by
                rw [P.same bound (Nat.lt_trans boundBeforeCounter bodyCounterBound)]; exact boundCompared
              obtain ⟨nextFrame,oneTimeout,exactBack,sameNext,nextValue,activation,scopes,frameDepth⟩ :=
                rangeBack_exact cx le bodyOutput back point afterFrame counter hb hint plan.intTy current
                  hback P.pp extensionBack (Nat.lt_of_lt_of_le bodyCounterBound P.mono) counterBody headerBlock
              have nextBoundValue : nextFrame.vals[bound]? = some (.val (.int plan.intTy upper)) := by
                rw [sameNext bound boundBeforeCounter]; exact boundBody
              have nextRel : Rel cfg env cx nextFrame header :=
                ⟨related.prof,related.slots,activation.trans P.rel.act,scopes.trans P.rel.scopes,
                  frameDepth.trans P.rel.depth,related.stack⟩
              have nextInvariant : RangeInv cfg env cx header counter bound plan.intTy upper base
                  (current + 1) nextFrame :=
                ⟨(sameCompared.trans (P.same.mono (Nat.le_of_lt bodyCounterBound)) (Nat.le_refl _)).trans
                  sameNext (Nat.le_refl _),nextValue,nextBoundValue,nextRel⟩
              cases remaining with
              | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
              | succ remaining =>
                cases remaining with
                | zero =>
                  intro result nonTimeout run
                  exact (nonTimeout after (run.symm.trans (congrFun oneTimeout after))).elim
                | succ nextFuel =>
                  have nextReflection := reentry nextFuel (by omega) env initial source plan metadata cx
                    header output counter bound hb hint upper base loweredOriginal atHeader extension headerBlock
                    boundBeforeCounter counterInHeader moduleEq resultsEq generated
                    (current + 1) nextFrame after nextInvariant nextRuntime
                  intro result nonTimeout run
                  have run' : runAt cx (hb,0) nextFrame nextFuel after = result := by
                    rw [← exactBack nextFuel]; exact run
                  rcases nextReflection result nonTimeout run' with success | stopped
                  · obtain ⟨v,final,pt',fr',residual,sourceRun,post,bound,targetRun⟩ := success
                    exact Or.inl ⟨v,final,pt',fr',residual,sourceRun,post,by omega,targetRun⟩
                  · exact Or.inr stopped
            · obtain ⟨value,origin,rfl,site⟩ := returned
              exact FuelBoundAt.ret (Or.inr ⟨value,origin,rfl,site⟩)
            · obtain rfl := Option.some.inj loopEq
              rcases transfer with ⟨rfl,pointEq,exitFrame⟩ | ⟨rfl,continued⟩
              · simp only [fuelBoundRangeTail]
                have sameFinal := sameCompared.trans
                  (exitFrame.values.mono (Nat.le_of_lt bodyCounterBound)) (Nat.le_refl _)
                have finalRelated : Rel cfg env cx afterFrame output :=
                  ⟨related.prof,related.slots,exitFrame.activation.trans inputRel.act,
                    by simpa [contextDepth] using exitFrame.scopesEqual,
                    exitFrame.depth.trans inputRel.depth,headerStackOutput.trans related.stack⟩
                exact FuelBoundAt.ret (Or.inl ⟨rfl,pointEq.symm ▸ exitPoint,sameFinal,finalRelated⟩)
              · simp only [fuelBoundRangeTail]
                obtain ⟨runtimeTy,old,beforeValue,next⟩ := continued
                have valueEq := Option.some.inj (beforeValue.symm.trans counterCompared)
                obtain ⟨typeEq,currentEq⟩ := Val.int.inj (RVal.val.inj valueEq)
                subst runtimeTy
                subst old
                have nextRel : Rel cfg env cx afterFrame header :=
                  ⟨related.prof,related.slots,next.activation.trans inputRel.act,
                    by simpa [contextDepth] using next.scopesEqual,
                    next.depth.trans inputRel.depth,related.stack⟩
                have boundNext : afterFrame.vals[bound]? = some (.val (.int plan.intTy upper)) := by
                  rw [next.values bound boundBeforeCounter]; exact boundCompared
                have nextInvariant : RangeInv cfg env cx header counter bound plan.intTy upper base
                    (current + 1) afterFrame :=
                  ⟨sameCompared.trans next.values (Nat.le_refl _),next.counterValue,boundNext,nextRel⟩
                have raw := preparedReturn_nonreturn_success done (by intro v h; cases h)
                have nextRuntime := runtime.afterBody rfl child typing roots world observation future retained may
                  n .cont raw (Or.inl rfl)
                have nextReflection := reentry remaining (by omega) env initial source plan metadata cx
                  header output counter bound hb hint upper base loweredOriginal atHeader extension headerBlock
                  boundBeforeCounter counterInHeader moduleEq resultsEq generated
                  (current + 1) afterFrame after nextInvariant nextRuntime
                rw [next.point]
                exact nextReflection
        · have falseValue : comparedFrame.vals[condition]? = some (.val (.bool false)) := by
            simpa [inside] using conditionValue
          unfold preparedRange
          simp only [inside,ite_false]
          apply FuelBoundAt.condbr_take0 branchAt falseValue exitTargetLive exitParams rfl
          exact FuelBoundAt.ret (Or.inl ⟨rfl,exitPoint,sameCompared,
            relatedCompared.stack_eq headerStackOutput⟩)
  exact reflection.of_source
    (congrFun (prepareReturn_execRange n cfg env x plan.intTy current upper block) state)

end Goose.Lower
