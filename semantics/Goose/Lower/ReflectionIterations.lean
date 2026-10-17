import Goose.Lower.ReflectionIterationsRange
import Goose.Lower.ReflectionIterationsEachStatement
import Goose.Lower.RangeFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedStatementReflection_range {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {x : VarId} {lo hi : Expr} {body : Core.Block} {origin : OriginId} {loop : Option LoopCtx}
    (lowerClaim : TypedExprReflection fuel cfg results lo)
    (upperClaim : ∀ residual, residual ≤ fuel → TypedExprReflection residual cfg results hi)
    (ranges : ∀ residual, residual < fuel → TypedRangeReflection residual cfg results x lo hi body origin) :
    TypedStatementReflection fuel cfg results loop (.forRange x lo hi body origin) := by
  intro env initial source metadata lexical input output point cx frame lowered atPoint extension related
    module returned depth targets counterOuter generated frames
  let plan := source.rangePlan
  obtain ⟨lowerSource, lowerTyping, lowerRoots, lowerType, lowerWorld,
    lowerObservation, lowerFuture, lowerMay, lowerPath, lowerPlans, lowerContext⟩ := plan.lowerChild
  have lowerMetadata : SourceResults lowerSource.typingEnv lowerSource.rootsEnv results := by
    rw [lowerTyping, lowerRoots]
    exact metadata
  have lowerChildMetadata : lowerSource.typingEnv = source.typingEnv ∧
      lowerSource.rootsEnv = source.rootsEnv ∧ lowerSource.ty = .int plan.intTy ∧
      lowerSource.world = source.world ∧ lowerSource.observation = source.observation ∧
      lowerSource.context.outputFuture =
        (source.context.child rfl 0 (.expression lo) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      lowerSource.context.mayShrink source.world.ownerP source.observation =
        source.context.mayShrink source.world.ownerP source.observation ∧
      lowerSource.path = source.path ++ [0] ∧ lowerSource.plans = source.plans ∧
      HEq lowerSource.context (source.context.child rfl 0 (.expression lo) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])) :=
    ⟨lowerTyping, lowerRoots, lowerType, lowerWorld, lowerObservation, lowerFuture,
      lowerMay, lowerPath, lowerPlans, lowerContext⟩
  have allAdvances := advB_lowerStmt loop (.forRange x lo hi body origin)
    (lowerEnv cfg.mod env.vars results) input () output lowered
  simp only [lowerStmt, bind_eq] at lowered
  obtain ⟨lowerId, afterLowerBuilder, lowerBuilder, upperId, afterUpperBuilder,
    upperBuilder, live⟩ := lowered
  have liveAdvances : afterUpperBuilder.Adv output := advB_whenLive () (fun _ =>
    AdvB.bind (advB_intTyOf lowerId) fun hint =>
      advB_header1 (.data (.int hint)) lowerId
        (tail := fun hb counter => lowerRange hint counter upperId hb (fun depth exit =>
          lowerBlock (some ⟨depth, exit, .next hb hint counter⟩)
            [(x, counter, origin)] false body))
        (fun hb counter => advB_lowerRange hint counter upperId hb
          (fun depth exit => advB_lowerBlock
            (some ⟨depth, exit, .next hb hint counter⟩)
            [(x, counter, origin)] false body)))
    (lowerEnv cfg.mod env.vars results) afterUpperBuilder () output live
  have extensionUpper : ExtT afterUpperBuilder cx.fn.blocks := extension.of_adv liveAdvances
  have extensionLower : ExtT afterLowerBuilder cx.fn.blocks :=
    extensionUpper.of_adv (advB_lowerExpr hi _ _ _ _ upperBuilder)
  have first := lowerClaim env initial lowerSource lowerMetadata input afterLowerBuilder lowerId
    point cx frame lowerBuilder atPoint extensionLower related module returned generated
  have composition : ReflectAtFuel fuel cx point frame
      (fun n => execStmt (n + 1) cfg env (.forRange x lo hi body origin) >>= prepareReturn env)
      (fun flow _ pt' fr' => StmtFlowPost cfg env cx input frame output flow pt' fr') initial := by
    simp only [execStmt,bind_assoc]
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env lo) ?_
    · intro nLower lowerValue lowerState lowerPoint lowerFrame lowerDone lowerPost upperFuel upperBound
      have lowerTyped := (lowerSource.result nLower lowerValue lowerDone).typed
      rw [lowerType] at lowerTyped
      obtain ⟨start, rfl⟩ := Core.Sound.hasTy_int lowerTyped
      simp only [Core.expectInt, pure_bind]
      have lowerResult := lowerSource.result nLower (.int plan.intTy start) lowerDone
      obtain ⟨upperSource, upperTyping, upperRoots, upperType, upperWorld,
        upperObservation, upperFuture, upperRetained, upperMay, upperPath, upperPlans,
        upperContext⟩ := plan.upperChild lowerSource lowerChildMetadata lowerResult
      have upperMetadata : SourceResults upperSource.typingEnv upperSource.rootsEnv results := by
        rw [upperTyping, upperRoots]
        exact metadata
      have upperChildMetadata : upperSource.typingEnv = source.typingEnv ∧
          upperSource.rootsEnv = source.rootsEnv ∧ upperSource.ty = .int plan.intTy ∧
          upperSource.world = source.world ∧ upperSource.observation = source.observation ∧
          upperSource.context.outputFuture =
            (source.context.child rfl 1 (.expression hi) .expression
              (by simp [DemandNode.child?, DemandNode.children])
              (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
          upperSource.context.retained =
            (source.context.child rfl 1 (.expression hi) .expression
              (by simp [DemandNode.child?, DemandNode.children])
              (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).retained ∧
          upperSource.context.mayShrink source.world.ownerP source.observation =
            source.context.mayShrink source.world.ownerP source.observation ∧
          upperSource.path = source.path ++ [1] ∧ upperSource.plans = source.plans ∧
          HEq upperSource.context (source.context.child rfl 1 (.expression hi) .expression
            (by simp [DemandNode.child?, DemandNode.children])
            (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])) :=
        ⟨upperTyping, upperRoots, upperType, upperWorld, upperObservation, upperFuture,
          upperRetained, upperMay, upperPath, upperPlans, upperContext⟩
      have second := upperClaim upperFuel upperBound env lowerState upperSource upperMetadata afterLowerBuilder
        afterUpperBuilder upperId lowerPoint cx lowerFrame upperBuilder lowerPost.pp extensionUpper lowerPost.rel
        module returned (generated.lowerExpr lo lowerBuilder)
      refine second.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env hi) ?_
      · intro nUpper upperValue upperState upperPoint upperFrame upperDone upperPost remaining remainingBound
        have upperTyped := (upperSource.result nUpper upperValue upperDone).typed
        rw [upperType] at upperTyped
        obtain ⟨upper, rfl⟩ := Core.Sound.hasTy_int upperTyped
        have upperResult := upperSource.result nUpper (.int plan.intTy upper) upperDone
        simp only [Core.expectSameTy, ite_true, pure_bind]
        obtain ⟨upperBlock, upperCurrent, upperLookup, upperIndex⟩ := LS.pp_some upperPost.pp
        rw [whenLive_some _ _ _ upperCurrent] at live
        simp only [bind_eq] at live
        obtain ⟨hint, typeState, typeOf, ⟨hb, parameters⟩, newState, newBlock,
          unit1, termState, term, unit2, header, setHeader, lowerRangeBuilder⟩ := live
        have typeStateEq := intTyOf_eq typeOf
        subst typeState
        have rangeAdvances := advB_lowerRange hint (parameters.headD 0) upperId hb
          (fun depth exit => advB_lowerBlock
            (some ⟨depth, exit, .next hb hint (parameters.headD 0)⟩)
            [(x, parameters.headD 0, origin)] false body)
          (lowerEnv cfg.mod env.vars results) header () output lowerRangeBuilder
        have extensionHeader : ExtT header cx.fn.blocks := extension.of_adv rangeAdvances
        have headerState : header = { termState with cur := some hb } := by
          rw [setCur_run] at setHeader
          exact (Prod.mk.inj setHeader).2.symm
        have extensionTerm : ExtT termState cx.fn.blocks := by
          rw [headerState] at extensionHeader
          exact extensionHeader
        have extensionNew : ExtT newState cx.fn.blocks := extensionTerm.of_adv (adv_emitTerm term)
        have newBlockRun := newBlock
        rw [newBlock1_run] at newBlockRun
        obtain ⟨newIds, newValues⟩ := Prod.mk.inj newBlockRun
        obtain ⟨headerId, parameterIds⟩ := Prod.mk.inj newIds
        let counter := parameters.headD 0
        have counterId : counter = afterUpperBuilder.vals.size := by
          change parameters.headD 0 = afterUpperBuilder.vals.size
          rw [← parameterIds]
          rfl
        have newValuesSize : newState.vals.size = afterUpperBuilder.vals.size + 1 := by
          rw [← newValues]
          simp
        have newStack : newState.stack = afterUpperBuilder.stack := by rw [← newValues]
        have newCurrent : newState.cur = afterUpperBuilder.cur := by rw [← newValues]
        have upperBlockLive : afterUpperBuilder.blocks[upperPoint.1]? = some upperBlock := upperLookup
        have upperBlockIndex : upperPoint.1 < afterUpperBuilder.blocks.size :=
          (Array.getElem?_eq_some_iff.mp upperBlockLive).1
        have lookupNew : newState.blocks[upperPoint.1]? = some upperBlock := by
          rw [← newValues]
          exact (getElem?_push_lt upperBlockIndex).trans upperBlockLive
        have upperPointNew : newState.pp = some upperPoint := by
          have current := newCurrent.trans upperCurrent
          have h := LS.pp_eq current lookupNew
          have point : (upperPoint.1, upperBlock.insts.size) = upperPoint := by
            cases upperPoint with
            | mk id index => simp_all
          exact point ▸ h
        have compareFacts := emitTerm_facts term upperPointNew extensionTerm
        have headerBlockOld : newState.blocks[hb]? =
            some ⟨[(counter, .data (.int hint))], #[]⟩ := by
          rw [counterId, ← headerId, ← newValues]
          simp
        have headerCurrentNe : newState.cur ≠ some hb := by
          rw [newCurrent, upperCurrent]
          intro same
          have equal := Option.some.inj same
          have upperBlockLess : upperPoint.1 < afterUpperBuilder.blocks.size := upperBlockIndex
          rw [← headerId] at equal
          exact Nat.ne_of_lt upperBlockLess equal
        have headerBlockPreserved := (adv_emitTerm term).keep hb _ headerCurrentNe headerBlockOld
        have headerPoint : header.pp = some (hb, 0) := by
          rw [headerState]
          exact LS.pp_cur headerBlockPreserved
        obtain ⟨headerTarget, headerTargetLive, headerParams⟩ := extensionTerm.params headerBlockPreserved
        have lowerCell : upperFrame.vals[lowerId]? =
            some (.val (.int plan.intTy start)) := by
          rw [upperPost.same lowerId (lowerPost.lt (lowerId, .val (.int plan.intTy start)) (by simp))]
          exact lowerPost.has (lowerId, .val (.int plan.intTy start)) (by simp)
        have upperCell : upperFrame.vals[upperId]? = some (.val (.int plan.intTy upper)) :=
          upperPost.has (upperId, .val (.int plan.intTy upper)) (by simp)
        have boundBeforeCounter : upperId < counter := by
          rw [counterId]
          exact upperPost.lt (upperId, .val (.int plan.intTy upper)) (by simp)
        have counterInHeader : counter < header.vals.size := by
          rw [headerState]
          change counter < termState.vals.size
          rw [compareFacts.1]
          simp only [counterId]
          rw [newValuesSize]
          exact Nat.lt_succ_self _
        let counterFrame := upperFrame.set counter (.val (.int plan.intTy start))
        have upperHeader : counterFrame.vals[upperId]? = some (.val (.int plan.intTy upper)) := by
          have different : counter ≠ upperId := Nat.ne_of_gt boundBeforeCounter
          simpa [counterFrame, Frame.set, Std.HashMap.getElem?_insert, different] using upperCell
        have headerStack : header.stack = afterUpperBuilder.stack := by
          rw [headerState]
          exact compareFacts.2.1.trans newStack
        have headerRelated : Rel cfg env cx counterFrame header :=
          (upperPost.rel.set counter (.val (.int plan.intTy start))).stack_eq headerStack
        have headerSame : Same counter upperFrame counterFrame :=
          Same.set (k := counter) upperFrame (r := counter) (Nat.le_refl _) _
        have initialInvariant :
            RangeInv cfg env cx header counter upperId plan.intTy upper upperFrame start counterFrame :=
          ⟨headerSame, Frame.set_get _ _ _, upperHeader, headerRelated⟩
        have runtimeState := plan.afterUpper upperSource upperChildMetadata upperResult
        have generatedLower := generated.lowerExpr lo lowerBuilder
        have generatedUpper := generatedLower.lowerExpr hi upperBuilder
        have generatedNew := generatedUpper.newBlock [.data (.int hint)] newBlock
        have generatedTerm := generatedNew.emitTerm (.br hb [lowerId])
          (by
            intro target member
            simp only [Term.successors,List.mem_singleton] at member
            subst target
            exact (Array.getElem?_eq_some_iff.mp headerBlockOld).1) term
        have generatedHeader := generatedTerm.setCur (some hb)
          (by intro current equal; have same := Option.some.inj equal; rw [← same]
              exact (Array.getElem?_eq_some_iff.mp headerBlockPreserved).1) setHeader
        have hiTerm : instAt cx.fn upperPoint = some (.term (.br hb [lowerId])) := compareFacts.2.2.2
        have combinedPost := lowerPost.comp upperPost
        have valuePrefix : input.vals.size ≤ counter := by rw [counterId]; exact combinedPost.mono
        cases remaining with
        | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
        | succ rangeFuel =>
          apply ReflectAtFuel.br1 hiTerm headerTargetLive headerParams lowerCell
          refine (ranges rangeFuel (by omega) env initial source plan metadata cx header output counter upperId hb
            hint upper upperFrame lowerRangeBuilder headerPoint extension
            ⟨headerTarget,headerTargetLive,headerParams⟩ boundBeforeCounter counterInHeader module returned
            generatedHeader start counterFrame upperState initialInvariant runtimeState).mono ?_
          intro flow after point' frame' result
          rcases result with ⟨normal,pointEq,same,relatedFinal⟩ | returnedAt
          · exact Or.inl ⟨normal,Post.nil pointEq allAdvances.vals
              (combinedPost.same.trans (same.mono valuePrefix) (Nat.le_refl _)) relatedFinal⟩
          · exact Or.inr returnedAt
      · intro upperValue n k bound
        refine (MonoM.refl _).bind (fun ⟨upperTy,upper⟩ => ?_)
        exact (MonoM.refl _).bind (fun _ =>
          ((monoAll n k bound).range cfg env x plan.intTy start upper body).bind (fun _ => MonoM.refl _))
    · intro lowerValue n k bound
      refine (MonoM.refl _).bind (fun ⟨ty,start⟩ => ?_)
      refine ((monoAll n k bound).expr cfg env hi).bind (fun upperValue => ?_)
      refine (MonoM.refl _).bind (fun ⟨upperTy,upper⟩ => ?_)
      exact (MonoM.refl _).bind (fun _ =>
        ((monoAll n k bound).range cfg env x ty start upper body).bind (fun _ => MonoM.refl _))
  have reflected : ReflectAtFuel fuel cx point frame
      (fun n => execStmt (n + 1) cfg env (.forRange x lo hi body origin) >>= prepareReturn env)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx input frame output loop flow pt' fr') initial :=
    composition.mono (fun flow after pt' fr' post =>
    post.elim (fun normal => Or.inl normal) (fun returned => Or.inr (Or.inl returned)))
  refine reflected.of_source (fun n => ⟨n + 1,?_⟩)
  rw [prepareLoopFlow_stmtRange]

end Goose.Lower
