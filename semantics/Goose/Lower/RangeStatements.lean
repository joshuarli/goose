import Goose.Lower.RangeFlow
import Goose.Lower.RangeSources
import Goose.Lower.EachSource
import Goose.Lower.TypedStatements

namespace Goose.Lower

open Goose.Core Goose.Core.Sound Goose.GIR

theorem RangePlan.blockCallback {n : Nat} {cfg : Cfg} {env : Env} {initial : St}
    {x : VarId} {lo hi : Expr} {body : Core.Block} {origin : OriginId}
    {source : StmtSource cfg env (.forRange x lo hi body origin) initial}
    (plan : RangePlan source) (results : List Ty)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (blocks : ∀ fuel, fuel < n → ∀ loop pre pre',
      TypedBlockLoopSimulation fuel cfg results (some loop) pre pre' false body)
    (cx : FnCtx) (module : cx.cfg.mod = lower cfg.mod) (returned : cx.fn.results = results)
    (header : LS) (base : Frame) (counter bound hb : ValueId)
    (hint runtimeType : IntTy) (upper : Int)
    (runtimeTypeEq : runtimeType = plan.intTy) :
    RangeBlockCallback n cfg env cx (lowerEnv cfg.mod env.vars results) header counter bound hb
      hint runtimeType upper base x body origin (fun _ state => RangeLoopState plan state) := by
  intro fuel smaller depth exit input result output current frame state bodyPoint lowered point
    extension stack depthEq counterBound targets invariant allowed pre generated frames
  obtain ⟨bodySource, typing, roots, _, _, _, _, _, _, _, _⟩ :=
    allowed.bodyChild runtimeTypeEq current
  have bodyMetadata : SourceResults bodySource.typingEnv bodySource.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  let loop : LoopCtx := ⟨depth, exit, .next hb hint counter⟩
  have lexical : bodySource.typingEnv.loops ≠ 0 := by
    rw [typing]
    exact Nat.ne_of_gt (Nat.zero_lt_succ _)
  have loopDepth : depth = env.scopes.length := by
    obtain ⟨_, _, _, related⟩ := invariant
    rw [depthEq, related.stack]
    simp
  have loopCounter : LoopCounterAt (some loop) input frame :=
    ⟨counterBound, runtimeType, current, invariant.2.1⟩
  exact eachBlock_typed_sim bodySource
    (blocks fuel smaller loop [(x, counter, origin)] [(x, .int runtimeType current)])
    bodyMetadata lexical input output result bodyPoint cx frame lowered point extension
    invariant.2.2.2 pre module returned loopDepth targets loopCounter generated frames

theorem execRange_success_flow (fuel : Nat) (cfg : Cfg) (env : Env) (x : VarId)
    (ty : IntTy) (current upper : Int) (body : Core.Block) :
    ∀ state after flow, execRange fuel cfg env x ty current upper body state = .ok flow after →
      flow = .normal .unit ∨ ∃ value, flow = .ret value := by
  induction fuel generalizing current with
  | zero =>
    intro state after flow done
    simp [execRange, Core.timeout, M.stop] at done
  | succ fuel induction =>
    intro state after flow done
    simp only [execRange] at done
    by_cases inside : current < upper
    · simp only [inside, ↓reduceIte, bind_apply] at done
      cases bodyResult : execBlock fuel cfg env [(x, .int ty current)] body state with
      | stop reason middle => simp [bodyResult] at done
      | ok bodyFlow middle =>
        simp only [bodyResult] at done
        cases bodyFlow with
        | normal value => exact induction (current + 1) middle after flow done
        | cont => exact induction (current + 1) middle after flow done
        | brk => exact Or.inl (Res.ok.inj done).1.symm
        | ret value => exact Or.inr ⟨value, (Res.ok.inj done).1.symm⟩
    · simp only [inside, ↓reduceIte, pure_apply, Res.ok.injEq] at done
      exact Or.inl done.1.symm

theorem prepareLoopFlow_execRange (n : Nat) (cfg : Cfg) (env : Env) (x : VarId)
    (ty : IntTy) (current upper : Int) (body : Core.Block) (loop : Option LoopCtx) :
    (execRange n cfg env x ty current upper body >>= prepareLoopFlow env loop) =
      (execRange n cfg env x ty current upper body >>= prepareReturn env) := by
  funext state
  simp only [bind_apply]
  cases done : execRange n cfg env x ty current upper body state with
  | stop reason after => rfl
  | ok flow after =>
    rcases execRange_success_flow n cfg env x ty current upper body state after flow done with
      normal | ⟨value, returned⟩
    · subst flow
      cases loop <;> simp [prepareLoopFlow, prepareLoopExit, prepareReturn]
    · subst flow
      cases loop <;> simp [prepareLoopFlow, prepareLoopExit, prepareReturn]

private theorem execBlock_raw_normal_of_prepared {fuel : Nat} {cfg : Cfg} {env : Env}
    {pre : List (VarId × Val)} {body : Core.Block} {state after : St} {value : Val}
    (success : (execBlock fuel cfg env pre body >>= prepareReturn env) state =
      .ok (.normal value) after) :
    execBlock fuel cfg env pre body state = .ok (.normal value) after := by
  rw [bind_apply] at success
  cases run : execBlock fuel cfg env pre body state with
  | stop reason middle => simp [run] at success
  | ok flow middle =>
    cases flow with
    | normal actual =>
      simp only [run, prepareReturn, pure_apply] at success
      obtain ⟨flowEq, stateEq⟩ := Res.ok.inj success
      cases flowEq
      cases stateEq
      rfl
    | brk =>
      simp only [run, prepareReturn, pure_apply] at success
      obtain ⟨flowEq, _⟩ := Res.ok.inj success
      cases flowEq
    | cont =>
      simp only [run, prepareReturn, pure_apply] at success
      obtain ⟨flowEq, _⟩ := Res.ok.inj success
      cases flowEq
    | ret actual =>
      cases released : releaseScopes env env.scopes middle with
      | stop reason afterRelease => simp [run, released, prepareReturn, bind_apply] at success
      | ok result afterRelease =>
        simp only [run, released, prepareReturn, bind_apply, pure_apply] at success
        obtain ⟨flowEq, _⟩ := Res.ok.inj success
        cases flowEq

private theorem execBlock_raw_cont_of_prepared {fuel : Nat} {cfg : Cfg} {env : Env}
    {pre : List (VarId × Val)} {body : Core.Block} {state after : St}
    (success : (execBlock fuel cfg env pre body >>= prepareReturn env) state =
      .ok .cont after) :
    execBlock fuel cfg env pre body state = .ok .cont after := by
  rw [bind_apply] at success
  cases run : execBlock fuel cfg env pre body state with
  | stop reason middle => simp [run] at success
  | ok flow middle =>
    cases flow with
    | normal actual =>
      simp only [run, prepareReturn, pure_apply] at success
      obtain ⟨flowEq, _⟩ := Res.ok.inj success
      cases flowEq
    | brk =>
      simp only [run, prepareReturn, pure_apply] at success
      obtain ⟨flowEq, _⟩ := Res.ok.inj success
      cases flowEq
    | cont =>
      simp only [run, prepareReturn, pure_apply] at success
      obtain ⟨flowEq, stateEq⟩ := Res.ok.inj success
      cases flowEq
      cases stateEq
      rfl
    | ret actual =>
      cases released : releaseScopes env env.scopes middle with
      | stop reason afterRelease => simp [run, released, prepareReturn, bind_apply] at success
      | ok result afterRelease =>
        simp only [run, released, prepareReturn, bind_apply, pure_apply] at success
        obtain ⟨flowEq, _⟩ := Res.ok.inj success
        cases flowEq

theorem stmt_range_checked_flow_sim_at {n : Nat} {cfg : Cfg} {env : Env} {initial : St}
    {x : VarId} {lo hi : Expr} {body : Core.Block} {origin : OriginId}
    (source : StmtSource cfg env (.forRange x lo hi body origin) initial)
    (results : List Ty) (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (lowerSimulation : TypedExprClaim n cfg results lo)
    (upperSimulation : TypedExprClaim n cfg results hi)
    (blocks : ∀ fuel, fuel < n + 1 → ∀ loop pre pre',
      TypedBlockLoopSimulation fuel cfg results (some loop) pre pre' false body)
    (cx : FnCtx) (module : cx.cfg.mod = lower cfg.mod) (returned : cx.fn.results = results)
    (loop : Option LoopCtx) (input output : LS) (frame : Frame) (point : Pt)
    (lowered : lowerStmt loop (.forRange x lo hi body origin)
      (lowerEnv cfg.mod env.vars results) input = ((), output))
    (atPoint : input.pp = some point) (extension : ExtT output cx.fn.blocks)
    (related : Rel cfg env cx frame input) (generated : GeneratedBuilderState input) :
    SimEAt cx point frame
      (execStmt (n + 1) cfg env (.forRange x lo hi body origin) >>= prepareReturn env)
      (StmtFlowPost cfg env cx input frame output) initial := by
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
  simp only [execStmt, bind_assoc]
  refine SimEAt.bind
    (lowerSimulation env initial lowerSource lowerMetadata input afterLowerBuilder lowerId
      point cx frame lowerBuilder atPoint extensionLower related module returned generated)
    fun lowerValue lowerState lowerPoint lowerFrame lowerDone lowerPost => ?_
  have lowerTyped := (lowerSource.result n lowerValue lowerDone).typed
  rw [lowerType] at lowerTyped
  obtain ⟨start, rfl⟩ := Core.Sound.hasTy_int lowerTyped
  simp only [Core.expectInt, pure_bind]
  have lowerResult := lowerSource.result n (.int plan.intTy start) lowerDone
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
  refine SimEAt.bind
    (upperSimulation env lowerState upperSource upperMetadata afterLowerBuilder
      afterUpperBuilder upperId lowerPoint cx lowerFrame upperBuilder lowerPost.pp
      extensionUpper lowerPost.rel module returned (generated.lowerExpr lo lowerBuilder))
    fun upperValue upperState upperPoint upperFrame upperDone upperPost => ?_
  have upperTyped := (upperSource.result n upperValue upperDone).typed
  rw [upperType] at upperTyped
  obtain ⟨upper, rfl⟩ := Core.Sound.hasTy_int upperTyped
  have upperResult := upperSource.result n (.int plan.intTy upper) upperDone
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
  have generatedUpper := (generated.lowerExpr lo lowerBuilder).lowerExpr hi upperBuilder
  have generatedNew := generatedUpper.newBlock [.data (.int hint)] newBlock
  have generatedTerm := generatedNew.emitTerm (.br hb [lowerId])
    (by
      intro target member
      simp only [Term.successors, List.mem_singleton] at member
      subst target
      exact (Array.getElem?_eq_some_iff.mp headerBlockOld).1) term
  have generatedHeader := generatedTerm.setCur (some hb)
    (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp headerBlockPreserved).1) setHeader

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
  have bodyCallback := plan.blockCallback results metadata
    (fun fuel smaller loop pre pre' => blocks fuel
      (Nat.lt_trans smaller (Nat.lt_succ_self n)) loop pre pre')
    cx module returned header upperFrame counter upperId hb hint plan.intTy upper rfl
  have retained : ∀ fuel, fuel < n → ∀ current state flow after,
      RangeLoopState plan state →
      (execBlock fuel cfg env [(x, .int plan.intTy current)] body >>= prepareReturn env)
        state = .ok flow after →
      (match flow with | .normal _ | .cont => RangeLoopState plan after | _ => True) := by
    intro fuel smaller current state flow after allowed success
    cases flow with
    | normal value =>
      have raw := execBlock_raw_normal_of_prepared success
      obtain ⟨child, typing, roots, world, observation, _, _, future,
        childRetained, may, _⟩ := allowed.bodyChild rfl current
      exact allowed.afterBody rfl child typing roots world observation future childRetained
        may fuel (.normal value) raw (Or.inr ⟨value, rfl⟩)
    | cont =>
      have raw := execBlock_raw_cont_of_prepared success
      obtain ⟨child, typing, roots, world, observation, _, _, future,
        childRetained, may, _⟩ := allowed.bodyChild rfl current
      exact allowed.afterBody rfl child typing roots world observation future childRetained
        may fuel .cont raw (Or.inl rfl)
    | brk | ret _ => trivial
  have rangeSimulation := lowerRange_flow_sim_at n cfg env cx
    (lowerEnv cfg.mod env.vars results) header output counter upperId hb hint plan.intTy
    upper upperFrame x origin body (fun _ state => RangeLoopState plan state)
    (fun _ state => RangeLoopState plan state) lowerRangeBuilder headerPoint extension
    ⟨headerTarget, headerTargetLive, headerParams⟩ boundBeforeCounter counterInHeader
    generatedHeader bodyCallback (fun _ _ allowed => allowed) retained
  have hiTerm : instAt cx.fn upperPoint = some (.term (.br hb [lowerId])) :=
    compareFacts.2.2.2
  have startGoes := goes_br1 hiTerm headerTargetLive headerParams lowerCell
  have combinedPost := lowerPost.comp upperPost
  have valuePrefix : input.vals.size ≤ counter := by rw [counterId]; exact combinedPost.mono
  have postConversion : ∀ flow after point' frame',
      (execRange n cfg env x plan.intTy start upper body >>= prepareReturn env) upperState =
        .ok flow after →
      RangeFlowPost cfg env cx output counter upperFrame flow point' frame' →
      StmtFlowPost cfg env cx input frame output flow point' frame' := by
    intro flow after point' frame' _ result
    rcases result with ⟨normal, pointEq, same, relatedFinal⟩ | returnedAt
    · exact Or.inl ⟨normal, Post.nil pointEq allAdvances.vals
        (combinedPost.same.trans (same.mono valuePrefix) (Nat.le_refl _)) relatedFinal⟩
    · exact Or.inr returnedAt
  have rangeStatement := (rangeSimulation start counterFrame upperState initialInvariant runtimeState).mono
    postConversion
  exact SimEAt.goes startGoes rangeStatement

end Goose.Lower
