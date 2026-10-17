import Goose.Lower.Validation.SummaryPreservationSourceControlKernels

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem returnBounds_frame_action {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {before after : LS} {upper : Prov}
    {expected : List RootRef} {action : B α} {result : α}
    (ready : ReplayBuilder module results vt func target le scopeCount slots before upper)
    (absent : ∀ avoid, ReturnFrames.ReturnAbsentRun (avoid := avoid) action)
    (run : action le before = (result, after)) :
    ReturnBoundsPreserved expected before upper after upper :=
  ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize (fun _ _ => rfl)
    (ReturnFrameRun.of_absence absent le before result after run)

theorem statementReplay_if {typingEnv : TEnv} {env : PEnv}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    {condition : Expr} {yes : Core.Block} {no : Option Core.Block} {origin : OriginId}
    (conditionChild : ExpressionReplayAt typingEnv env results vt target scopeCount condition initial upper)
    (blockChild : ∀ body, body = yes ∨ no = some body → ∀ state provenance,
      BlockReplayAt typingEnv env results vt target scopeCount loop [] false body state provenance) :
    StatementReplayAt typingEnv env results vt target scopeCount loop scope (.ifS condition yes no origin)
      initial upper := by
  intro output start finish before after typed replay ceiling scopes stack ready generated loopTargets loopReplay native
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerExpr condition le initial
  obtain ⟨conditionCounter, yesType, yesCounter, typedCondition, typedYes, typedNo, _⟩ := tyStmt_if_children typed
  obtain ⟨conditionRoots, conditionState, yesRoots, yesRange, yesState, replayedCondition, replayedYes, replayedNo⟩ := rpStmt_if_children replay
  have yesEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) yesState.eff target := by
    cases no with
    | none => simpa only [replayedNo] using ceiling
    | some body =>
      obtain ⟨roots, range, checked⟩ := replayedNo
      exact effectRefinement_before_of_replay (rp_mono_all.2.2.2.2.1 env [] body)
        (rp_rebinds_mono_all.2.2.2.2.1 env [] body) (rp_flags_mono_all.2.2.2.2.1 env [] body) checked ceiling
  have conditionEffect := effectRefinement_before_of_replay (rp_mono_all.2.2.2.2.1 env [] yes)
    (rp_rebinds_mono_all.2.2.2.2.1 env [] yes) (rp_flags_mono_all.2.2.2.2.1 env [] yes) replayedYes yesEffect
  have conditionNative : NativeRows vt lowered.2 := by
    cases no with
    | none => exact native.of_prefix (types_ifS_none_core lowered.1 (types_lowerBlock loop [] false yes) le lowered.2 _ _ rfl)
    | some body => exact native.of_prefix (types_ifS_some_core lowered.1 (types_lowerBlock loop [] false yes)
        (types_lowerBlock loop [] false body) le lowered.2 _ _ rfl)
  obtain ⟨conditionUpper, conditionReady, conditionValue, conditionPrefix⟩ := conditionChild .bool start conditionCounter
    before conditionState conditionRoots typedCondition replayedCondition conditionEffect ready generated conditionNative
  have conditionTransfer : ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) initial upper lowered.2 conditionUpper :=
    ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize conditionPrefix
      (source_expression_return_frame typedCondition le initial lowered.1 lowered.2 rfl)
  have conditionAdvance := advB_lowerExpr condition le initial lowered.1 lowered.2 rfl
  have conditionGenerated := generated.lowerExpr condition (rfl : lowerExpr condition le initial = lowered)
  have conditionTargets := loopTargets.mono conditionAdvance.ext.1
  have conditionLoops := loopReplay.mono conditionAdvance
  have conditionStack : typingEnv.inExpr = false → ∀ entered ∈ lowered.2.stack, entered < scopeCount := by
    simpa only [conditionAdvance.stack] using stack
  have yesScopes : SourceScopesWithin scopeCount (Core.blockScopes none yes) := by
    apply scopes.of_subset
    intro entry member
    cases no <;> simp only [stmtScopes, List.mem_append] <;> exact Or.inl (Or.inr member)
  cases current : lowered.2.cur with
  | none =>
    have whole : lowerStmt loop (.ifS condition yes no origin) le initial = ((), lowered.2) := by
      cases no <;> simp only [lowerStmt, bind_run, show lowerExpr condition le initial = lowered from rfl,
        whenLive_none _ _ _ current]
    rw [whole]
    exact ⟨conditionUpper, conditionReady, conditionPrefix, conditionTransfer⟩
  | some block =>
    let forked := (fork lowered.1 le lowered.2).2
    let yesStart := { forked with cur := some lowered.2.blocks.size }
    let yesResult := lowerBlock loop [] false yes le yesStart
    have forkReady := conditionReady.loopFork lowered.1 ((conditionValue (by change lowered.2.cur.isSome = true; rw [current]; rfl)).1)
    have forkSize : forked.blocks.size = lowered.2.blocks.size + 2 := by simp [forked, fork_run _ _ current]
    have yesReady : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target le scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl) yesStart conditionUpper := by
      have selected := forkReady.setCur (some lowered.2.blocks.size) (by
        intro candidate row; cases row
        change lowered.2.blocks.size < forked.blocks.size
        rw [forkSize]; omega)
      simpa only [setCur_run] using selected
    have forkGenerated := conditionGenerated.fork lowered.1 (rfl : fork lowered.1 le lowered.2 = ((fork lowered.1 le lowered.2).1, forked))
    have yesGenerated : GeneratedBuilderState yesStart := by
      apply forkGenerated.setCur (env := le) (some lowered.2.blocks.size) _ rfl
      intro candidate row; cases row
      change lowered.2.blocks.size < forked.blocks.size
      rw [forkSize]; omega
    have yesAdvance : lowered.2.Adv yesStart := by
      apply (advB_fork lowered.1 le lowered.2 _ _ rfl).setCur
      exact Or.inr ⟨Nat.le_refl _, by change lowered.2.blocks.size < forked.blocks.size; rw [forkSize]; omega⟩
    have yesTargets := conditionTargets.mono yesAdvance.ext.1
    have yesLoops := conditionLoops.mono yesAdvance
    have yesStack : typingEnv.inExpr = false → ∀ entered ∈ yesStart.stack, entered < scopeCount := by
      simpa only [yesAdvance.stack] using conditionStack
    have yesNative : NativeRows vt yesResult.2 := by
      cases other : no with
      | none =>
        have whole : lowerStmt loop (.ifS condition yes none origin) le initial =
            Goose.Lower.setCur (some (lowered.2.blocks.size + 1)) le
              (Goose.Lower.emitTerm (.br (lowered.2.blocks.size + 1) []) le yesResult.2).2 := by
          simp only [lowerStmt, bind_run, show lowerExpr condition le initial = lowered from rfl,
            whenLive_some _ _ _ current, fork_run _ _ current, setCur_run, yesResult, yesStart, forked]
        rw [other, whole] at native
        exact native.of_prefix ((types_emitTerm _ le yesResult.2 _ _ rfl).trans
          (types_setCur _ le _ _ _ rfl))
      | some body =>
        let noStart := { yesResult.2 with cur := some (lowered.2.blocks.size + 1) }
        let noResult := lowerBlock loop [] false body le noStart
        have whole : lowerStmt loop (.ifS condition yes (some body) origin) le initial =
            Goose.Lower.joinArms yesResult.2.cur noResult.2.cur le noResult.2 := by
          simp only [lowerStmt, bind_run, show lowerExpr condition le initial = lowered from rfl,
            whenLive_some _ _ _ current, fork_run _ _ current, setCur_run, curBlock_run,
            yesResult, noResult, yesStart, noStart, forked]
        rw [other, whole] at native
        exact native.of_prefix ((types_setCur _ le yesResult.2 _ _ rfl).trans
          ((types_lowerBlock loop [] false body le noStart _ _ rfl).trans
            (types_joinArms _ _ le noResult.2 _ _ rfl)))
    obtain ⟨middle, yesCompleted, _, yesPrefix, yesTransfer⟩ := blockChild yes (Or.inl rfl) yesStart conditionUpper
      yesType conditionCounter yesCounter conditionState yesState yesRoots yesRange typedYes replayedYes yesEffect yesScopes
      (by simp) (by simp) (by simp) yesStack yesReady yesGenerated yesTargets yesLoops yesNative
    have setupTransfer : ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) lowered.2 conditionUpper yesStart conditionUpper := by
      exact returnBounds_frame_action conditionReady
        (fun _ => ReturnFrames.ReturnAbsentRun.bind (ReturnFrames.returnAbsent_fork lowered.1)
          (fun _ => ReturnFrames.returnAbsent_setCur (some lowered.2.blocks.size)))
        (action := do let _ ← fork lowered.1; Goose.Lower.setCur (some lowered.2.blocks.size)) rfl
    have throughYes := (conditionTransfer.trans setupTransfer).trans yesTransfer
    have yesGrowth := advB_lowerBlock loop [] false yes le yesStart yesResult.1 yesResult.2 rfl
    have yesResultGenerated := yesGenerated.lowerBlock loop [] false yes yesTargets
      (rfl : lowerBlock loop [] false yes le yesStart = yesResult)
    have joinBound : lowered.2.blocks.size + 1 < yesResult.2.blocks.size := by
      apply Nat.lt_of_lt_of_le (m := yesStart.blocks.size) _ yesGrowth.ext.1
      change lowered.2.blocks.size + 1 < forked.blocks.size
      rw [forkSize]; omega
    have retainedYes : ∀ old, old < upper.vals.size → rootsAt middle.vals old = rootsAt upper.vals old := by
      intro old bound
      have growth : upper.vals.size ≤ conditionUpper.vals.size := by
        rw [ready.roots.valueSize, conditionReady.roots.valueSize]
        exact conditionAdvance.vals
      exact (yesPrefix old (Nat.lt_of_lt_of_le bound growth)).trans (conditionPrefix old bound)
    cases other : no with
    | none =>
      subst no
      have branched := yesCompleted.loopBranch (lowered.2.blocks.size + 1) [] joinBound (by simp) (by simp)
      have selected := branched.setCur (some (lowered.2.blocks.size + 1)) (by
        intro candidate row; cases row
        exact Nat.lt_of_lt_of_le joinBound (advB_emitTerm _ le yesResult.2 _ _ rfl).ext.1)
      have whole : lowerStmt loop (.ifS condition yes none origin) le initial =
          Goose.Lower.setCur (some (lowered.2.blocks.size + 1)) le
            (Goose.Lower.emitTerm (.br (lowered.2.blocks.size + 1) []) le yesResult.2).2 := by
        simp only [lowerStmt, bind_run, show lowerExpr condition le initial = lowered from rfl,
          whenLive_some _ _ _ current, fork_run _ _ current, setCur_run, yesResult, yesStart, forked]
      rw [whole]
      refine ⟨middle, selected, retainedYes, throughYes.trans ?_⟩
      exact returnBounds_frame_action yesCompleted
        (fun _ => ReturnFrames.ReturnAbsentRun.bind (ReturnFrames.returnAbsent_emitTerm _ (by intro values origin same; cases same))
          (fun _ => ReturnFrames.returnAbsent_setCur _)) rfl
    | some body =>
      subst no
      let noStart := { yesResult.2 with cur := some (lowered.2.blocks.size + 1) }
      let noResult := lowerBlock loop [] false body le noStart
      have noReady : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target le scopeCount
          (typedContextSlotUpper env.mod env.ctx env.impl) noStart middle := by
        simpa only [setCur_run] using yesCompleted.setCur (some (lowered.2.blocks.size + 1))
          (by intro candidate row; cases row; exact joinBound)
      have noGenerated : GeneratedBuilderState noStart := by
        apply yesResultGenerated.setCur (env := le) (some (lowered.2.blocks.size + 1)) _ rfl
        intro candidate row; cases row; exact joinBound
      have noTargets : LoopBuilderTargets loop noStart := yesTargets.mono yesGrowth.ext.1
      have noLoops : LoopReplayBounds loop scopeCount noStart := by
        have preserved := yesLoops.mono yesGrowth
        cases loop <;> exact preserved
      have noStack : typingEnv.inExpr = false → ∀ entered ∈ noStart.stack, entered < scopeCount := by
        simpa only [show noStart.stack = yesResult.2.stack from rfl, yesGrowth.stack] using yesStack
      have whole : lowerStmt loop (.ifS condition yes (some body) origin) le initial =
          Goose.Lower.joinArms yesResult.2.cur noResult.2.cur le noResult.2 := by
        simp only [lowerStmt, bind_run, show lowerExpr condition le initial = lowered from rfl,
          whenLive_some _ _ _ current, fork_run _ _ current, setCur_run, curBlock_run,
          yesResult, noResult, yesStart, noStart, forked]
      have noNative : NativeRows vt noResult.2 := by
        rw [whole] at native
        exact native.of_prefix (types_joinArms _ _ le noResult.2 _ _ rfl)
      obtain ⟨noType, typedNo⟩ := typedNo
      obtain ⟨noRoots, noRange, replayedNo⟩ := replayedNo
      have noScopes : SourceScopesWithin scopeCount (Core.blockScopes none body) := by
        apply scopes.of_subset
        intro entry member
        simp only [stmtScopes, List.mem_append]
        exact Or.inr member
      obtain ⟨next, noCompleted, _, noPrefix, noTransfer⟩ := blockChild body (Or.inr rfl) noStart middle
        noType yesCounter finish yesState after noRoots noRange typedNo replayedNo ceiling noScopes
        (by simp) (by simp) (by simp) noStack noReady noGenerated noTargets noLoops noNative
      have noGrowth := advB_lowerBlock loop [] false body le noStart noResult.1 noResult.2 rfl
      have joined := noCompleted.joinArms yesResult.2.cur noResult.2.cur
        (fun last row => Nat.lt_of_lt_of_le (yesCompleted.current last row) noGrowth.ext.1) noCompleted.current
      rw [whole]
      refine ⟨next, joined, ?_, ?_⟩
      · intro old bound
        have growth : upper.vals.size ≤ middle.vals.size := by
          rw [ready.roots.valueSize, yesCompleted.roots.valueSize]
          exact Nat.le_trans conditionAdvance.vals (Nat.le_trans yesAdvance.vals yesGrowth.vals)
        exact (noPrefix old (Nat.lt_of_lt_of_le bound growth)).trans (retainedYes old bound)
      · have selectedTransfer : ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx)
            yesResult.2 middle noStart middle := by
          exact returnBounds_frame_action yesCompleted (fun _ => ReturnFrames.returnAbsent_setCur _) rfl
        exact ((throughYes.trans selectedTransfer).trans noTransfer).trans
          (returnBounds_frame_action noCompleted (fun _ => ReturnFrames.returnAbsent_joinArms _ _) rfl)

#print axioms statementReplay_if

end Goose.Lower.Validation.SummaryPreservation
