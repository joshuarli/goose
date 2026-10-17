import Goose.Lower.Validation.SourceGlobalControlLeaves
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsWhile

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

namespace ReplayBuilder

private theorem typedGlobalWhileNative {typingEnv output : TEnv} {env : PEnv} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {scope start finish : Nat} {before after : RState}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov} (loop : Option LoopCtx)
    (inside : typingEnv.inExpr = true)
    (source : tyStmt typingEnv scope (.while condition body origin) start = .ok (output, finish))
    (replayed : rpStmt env (.while condition body origin) before = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body))
    (stackBounds : typingEnv.inExpr = false → ∀ entered ∈ ls.stack, entered < scopeCount)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerStmt loop (.while condition body origin)
      (lowerEnv env.mod env.impl.vars returnTypes) ls).2)
    (conditionChild : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount condition
      (nativeWhileHeader (lowerEnv env.mod env.impl.vars returnTypes) ls) upper)
    (bodyChild : ∀ provenance, GlobalBlockReplayAt {typingEnv with loops := typingEnv.loops + 1} env results vt func returnTypes slots target scopeCount
      (some (nativeWhileContext condition (lowerEnv env.mod env.impl.vars returnTypes) ls)) [] false body
      (nativeWhileBody condition (lowerEnv env.mod env.impl.vars returnTypes) ls) provenance) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved [] ls upper
        (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next := by
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let expected : List RootRef := []
  obtain ⟨conditionFinish, bodyType, conditionTyped, bodyTyped, _⟩ := tyStmt_while_children source
  obtain ⟨conditionRoots, conditionState, bodyRoots, bodyRange, conditionReplay, bodyReplay⟩ := native_while_replay replayed
  have conditionEffect := native_loop_source_body_effect bodyReplay wholeEffect
  let allocated := newBlock [] le ls
  have headerEq : allocated.1.1 = ls.blocks.size := by simp [allocated, newBlock0_run]
  have allocatedReady := ready.loopEmptyBlock
  have headerBound : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock0_run]
  let bridged := Goose.Lower.emitTerm (.br allocated.1.1 []) le allocated.2
  have bridgeReady := allocatedReady.loopBranch allocated.1.1 [] headerBound (by simp) (by simp)
  have bridgeAdv := advB_emitTerm (.br allocated.1.1 []) le allocated.2 bridged.1 bridged.2 rfl
  have headerStill := Nat.lt_of_lt_of_le headerBound bridgeAdv.ext.1
  let started := nativeWhileHeader le ls
  have startedReady := bridgeReady.setCur (some allocated.1.1) (by intro b row; cases row; exact headerStill)
  have allocatedGenerated := generated.newBlock [] (rfl : newBlock [] le ls = allocated)
  have bridgeGenerated := allocatedGenerated.emitTerm (.br allocated.1.1 [])
    (by simpa [Term.successors, allocated, newBlock0_run] using headerBound) (rfl : Goose.Lower.emitTerm (.br allocated.1.1 []) le allocated.2 = bridged)
  have startedGenerated := bridgeGenerated.setCur (some allocated.1.1)
    (by intro b row; cases row; exact headerStill) (rfl : Goose.Lower.setCur (some allocated.1.1) le bridged.2 = ((), started))
  let tested := lowerExpr condition le started
  let bodyAction := fun depth exit => lowerBlock (some ⟨depth, exit, .jump allocated.1.1⟩) [] false body
  have whole : lowerStmt loop (.while condition body origin) le ls =
      lowerWhile allocated.1.1 (lowerExpr condition) bodyAction le started := by
    simp only [lowerStmt, bind_run]
    rfl
  have testedNative : NativeRows vt tested.2 := by
    apply native.of_prefix
    rw [whole]
    change TypePrefix tested.2 (whenLive () _ le tested.2).2
    cases current : tested.2.cur with
    | none => rw [whenLive_none _ _ _ current]; exact .refl _
    | some block =>
      rw [whenLive_some _ _ _ current]
      exact types_loopBody tested.1 (fun _ _ => types_lowerBlock _ _ _ _) (types_emitTerm _) le tested.2 _ _ rfl
  obtain ⟨conditionProv, conditionReady, conditionValue, conditionGrowth⟩ := conditionChild .bool start conditionFinish
    before conditionState conditionRoots conditionTyped conditionReplay conditionEffect startedReady startedGenerated testedNative
  have testedGenerated := startedGenerated.lowerExpr condition (rfl : lowerExpr condition le started = tested)
  have testedAdv := advB_lowerExpr condition le started tested.1 tested.2 rfl
  have startValues : started.vals = ls.vals := by
    change bridged.2.vals = ls.vals
    cases active : allocated.2.cur with
    | none => simp [bridged, emitTerm_none _ _ active, allocated, newBlock0_run]
    | some b => simp [bridged, emitTerm_run _ _ active, allocated, newBlock0_run]
  have startStack : started.stack = ls.stack := by
    change bridged.2.stack = ls.stack
    exact bridgeAdv.stack.trans (advB_newBlock0 le ls allocated.1 allocated.2 rfl).stack
  have entryReturns : ReturnMembershipFrame ls started := by
    apply ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_header0 (fun _ => ReturnFrames.returnAbsent_pure ()))
      le ls () started
    simp only [bind_run, pure_run]
    rfl
  have entryTransfer : ReturnBoundsPreserved expected ls upper started upper :=
    .frame ready.symbols ready.roots.valueSize (fun _ _ => rfl) entryReturns
  have conditionTransfer : ReturnBoundsPreserved expected started upper tested.2 conditionProv :=
    .frame startedReady.symbols startedReady.roots.valueSize conditionGrowth
      (source_expression_return_frame conditionTyped le started tested.1 tested.2 rfl)
  cases current : tested.2.cur with
  | none =>
    have stopped : lowerStmt loop (.while condition body origin) le ls = ((), tested.2) := by
      rw [whole]
      change whenLive () _ le tested.2 = ((), tested.2)
      exact whenLive_none _ _ _ current
    exact ⟨conditionProv, by rw [stopped]; exact conditionReady, conditionGrowth,
      by rw [stopped]; exact entryTransfer.trans conditionTransfer⟩
  | some block =>
    have live : tested.2.cur.isSome = true := by simp [current]
    have nativeLoop : NativeRows vt (Goose.Lower.loopBody tested.1 bodyAction (Goose.Lower.emitTerm (.br allocated.1.1 [])) le tested.2).2 := by
      rw [whole] at native
      change NativeRows vt (whenLive () _ le tested.2).2 at native
      rw [whenLive_some _ _ _ current] at native
      exact native
    have backReturns : ReturnFrameRun (Goose.Lower.emitTerm (.br allocated.1.1 [])) :=
      .of_absence (fun _ => ReturnFrames.returnAbsent_emitTerm _ (by intro _ _ same; cases same))
    obtain ⟨next, nextReady, growth, transfer⟩ := conditionReady.loopBodyNative expected tested.1
      (conditionValue live).bound live bodyAction (Goose.Lower.emitTerm (.br allocated.1.1 [])) testedGenerated nativeLoop
      (fun _ _ => advB_lowerBlock _ _ _ _) (advB_emitTerm _) (types_emitTerm _) backReturns
      (by
        dsimp only
        intro stateReady stateGenerated stateNative exitBound blocks values
        have header : allocated.1.1 < (loopBodyEntry tested.1 le tested.2).blocks.size :=
          Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le headerStill testedAdv.ext.1) blocks
        have bounds : LoopBuilderTargets (some ⟨tested.2.stack.length, (fork tested.1 le tested.2).1.2, .jump allocated.1.1⟩)
            (loopBodyEntry tested.1 le tested.2) := ⟨exitBound, header⟩
        have replayBounds : LoopReplayBounds (some ⟨tested.2.stack.length, (fork tested.1 le tested.2).1.2, .jump allocated.1.1⟩)
            scopeCount (loopBodyEntry tested.1 le tested.2) := by
          constructor
          · trivial
          · rw [native_loopBody_entry_stack]
            simp
        obtain ⟨next, nextReady, _, retained⟩ := bodyChild conditionProv bodyType conditionFinish finish
          conditionState after bodyRoots bodyRange bodyTyped bodyReplay wholeEffect scopes (by simp) (by simp) (by simp)
          (by
            intro plain entered member
            apply stackBounds plain entered
            change entered ∈ (nativeWhileBody condition le ls).stack at member
            change entered ∈ (loopBodyEntry tested.1 le tested.2).stack at member
            rw [native_loopBody_entry_stack, testedAdv.stack, startStack] at member
            exact member)
          stateReady stateGenerated (by simpa only [nativeWhileContext, nativeWhileBody, headerEq] using bounds)
          (by simpa only [nativeWhileContext, nativeWhileBody, headerEq] using replayBounds) stateNative
        have transfer : ReturnBoundsPreserved expected
            (nativeWhileBody condition le ls) conditionProv
            (lowerBlock (some (nativeWhileContext condition le ls)) [] false body le
              (nativeWhileBody condition le ls)).2 next :=
          .frame stateReady.symbols stateReady.roots.valueSize retained
            (returnFrame_lowerBlock _ [] false body (tyBlock_returnFree body [] bodyTyped inside) _ _ _ _ rfl)
        exact ⟨next, nextReady, retained, transfer⟩)
      (by
        intro state provenance stateReady blocks values priorRoots
        exact ⟨provenance, stateReady.loopBranch allocated.1.1 []
          (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le headerStill testedAdv.ext.1) blocks) (by simp) (by simp), fun _ _ => rfl⟩)
    have same : lowerStmt loop (.while condition body origin) le ls =
        Goose.Lower.loopBody tested.1 bodyAction (Goose.Lower.emitTerm (.br allocated.1.1 [])) le tested.2 := by
      rw [whole]
      change whenLive () _ le tested.2 = _
      rw [whenLive_some _ _ _ current]
    refine ⟨next, by rw [same]; exact nextReady, ?_, ?_⟩
    · intro old bound
      have conditionBound : old < conditionProv.vals.size := by
        rw [conditionReady.roots.valueSize]
        apply Nat.lt_of_lt_of_le _ testedAdv.vals
        rw [startValues]
        simpa only [ready.roots.valueSize] using bound
      rw [growth old conditionBound, conditionGrowth old bound]
    · rw [same]
      exact entryTransfer.trans (conditionTransfer.trans transfer)

end ReplayBuilder

theorem globalStatementReplay_while {typingEnv : TEnv} {env : PEnv}
    {condition : Expr} {body : Core.Block} {origin : OriginId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func}
    {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff}
    {scopeCount : Nat} {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    (inside : typingEnv.inExpr = true)
    (conditionChild : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount condition
      (nativeWhileHeader (lowerEnv env.mod env.impl.vars returnTypes) initial) upper)
    (bodyChild : ∀ provenance, GlobalBlockReplayAt {typingEnv with loops := typingEnv.loops + 1}
      env results vt func returnTypes slots target scopeCount
      (some (nativeWhileContext condition (lowerEnv env.mod env.impl.vars returnTypes) initial)) [] false body
      (nativeWhileBody condition (lowerEnv env.mod env.impl.vars returnTypes) initial) provenance) :
    GlobalStatementReplayAt typingEnv env results vt func returnTypes slots target scopeCount loop scope
      (.while condition body origin) initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated targets loopReplay native
  have bodyScopes : SourceScopesWithin scopeCount (Core.blockScopes none body) := by
    apply scopes.of_subset
    intro entry member
    exact List.mem_append_right _ member
  obtain ⟨next, completed, retained, _⟩ := ready.typedGlobalWhileNative loop inside typed replay ceiling bodyScopes
    stack generated native conditionChild bodyChild
  exact ⟨next, completed, retained, fun expected => global_statement_transfer expected loop inside typed ready retained⟩

#print axioms globalStatementReplay_while

end Goose.Lower.Validation.SummaryPreservation
