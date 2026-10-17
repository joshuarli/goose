import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeSteps
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SummaryPreservationSourceBlockContracts
import Goose.Lower.Validation.SummaryPreservationReplayTerm
import Goose.Lower.Validation.SummaryPreservationReturnLedgerSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem noteAborts_flag {before after : RState}
    (run : noteAborts before = .ok ((), after)) : after.eff.aborts = true := by
  change Except.ok ((), { before with eff := { before.eff with aborts := true } }) = .ok ((), after) at run
  have same := (Prod.mk.inj (Except.ok.inj run)).2
  rw [← same]

private theorem noteAborts_before {func : Func} {before after : RState} {target : Core.Eff}
    (run : noteAborts before = .ok ((), after))
    (ceiling : EffectRefinement func after.eff target) : EffectRefinement func before.eff target := by
  change Except.ok ((), { before with eff := { before.eff with aborts := true } }) = .ok ((), after) at run
  have same := (Prod.mk.inj (Except.ok.inj run)).2
  rw [← same] at ceiling
  exact (⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
    fun _ h => h, fun _ => rfl, fun h => h, fun h => h⟩ :
    EffectRefinement func before.eff { before.eff with aborts := true }).trans ceiling

private theorem abortingTerm_delta (module : GIR.Module) (vt : Array (Option VTy)) (func : Func)
    (upper : Prov) (target : Core.Eff) (term : Term)
    (aborting : (∃ code origin, term = .abort code origin) ∨ (∃ value origin, term = .exit value origin))
    (aborts : target.aborts = true) :
    EffectRefinement func (func.effectStep module vt upper {} (.term term)) target := by
  rcases aborting with ⟨code, origin, rfl⟩ | ⟨value, origin, rfl⟩
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => aborts, ?_, ?_⟩
    all_goals simp [Func.effectStep, Func.storageTargets]

private theorem assertCore {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
    {slots : Array (List RootRef)} {state : LS} {upper : Prov} (condition : ValueId) (origin : OriginId)
    (ready : ReplayBuilder module results vt func target le scopeCount slots state upper)
    (conditionBound : state.cur.isSome = true → condition < state.vals.size)
    (originBound : origin < le.mod.origins.size) (aborts : target.aborts = true) :
    ReplayBuilder module results vt func target le scopeCount slots
      ((whenLive () fun _ => do
        let (success, failure) ← fork condition
        Goose.Lower.setCur (some failure)
        Goose.Lower.emitTerm (.abort .assert (some origin))
        Goose.Lower.setCur (some success)) le state).2 upper := by
  cases current : state.cur with
  | none => rw [whenLive_none _ _ _ current]; exact ready
  | some block =>
    rw [whenLive_some _ _ _ current]
    let forked := fork condition le state
    have forkReady := ready.loopFork condition (conditionBound (by simp [current]))
    have successBound : forked.1.1 < forked.2.blocks.size := by simp [forked, fork_run condition le current] <;> nat_omega
    have failureBound : forked.1.2 < forked.2.blocks.size := by simp [forked, fork_run condition le current] <;> nat_omega
    let failed := Goose.Lower.setCur (some forked.1.2) le forked.2
    have failedReady := forkReady.setCur (some forked.1.2) (by
      intro found same
      cases Option.some.inj same
      exact failureBound)
    have abortedReady := failedReady.emitTerm (.abort .assert (some origin))
      (fun _ => by
        apply Inst.SymbolsWithin.term
        · simp [Term.uses]
        · simpa [Term.origin] using originBound
        · simp [Term.successors])
      (fun _ => by trivial)
      (fun _ => abortingTerm_delta _ _ _ _ target _ (Or.inl ⟨_, _, rfl⟩) aborts)
    have completed := abortedReady.setCur (some forked.1.1) (by
      intro found same
      cases Option.some.inj same
      apply Nat.lt_of_lt_of_le _ (advB_emitTerm (.abort .assert (some origin)) le failed.2 _ _ rfl).ext.1
      simpa only [failed, setCur_run] using successBound)
    simpa only [bind_run, forked, failed] using completed

private theorem assert_emissions {property : Inst → Prop} (terms : ∀ term, property (.term term))
    (condition : ValueId) (origin : OriginId) :
    EmitsOnlyRun property (whenLive () fun _ => do
      let (success, failure) ← fork condition
      Goose.Lower.setCur (some failure)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some success)) := by
  apply EmitsOnlyRun.whenLive ()
  intro block
  apply EmitsOnlyRun.bind (emitsOnly_fork _ terms condition)
  rintro ⟨success, failure⟩
  apply EmitsOnlyRun.bind (emitsOnly_setCur _ (some failure))
  intro _
  apply EmitsOnlyRun.bind (emitsOnly_emitTerm (.abort .assert (some origin)) (terms _))
  intro _
  exact emitsOnly_setCur _ (some success)

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId} {loop : Option LoopCtx} {scope : ScopeId}

theorem statementOccurrence_abort (message : String) (origin : OriginId)
    (tables : SourceRootTables typingEnv env) :
    StatementOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop scope (.abort message origin) initial upper := by
  intro source output start finish before after typed replay ceiling _sourceScopes _stack ready sites targetBounds generated loopTargets loopReplay counterTyped included native projects continuation
  have originBound : origin < (lowerEnv env.mod env.impl.vars env.impl.results.toList).mod.origins.size := by
    simpa only [stmtSourceOrigin, lowerEnv, ← tables.moduleEq] using Core.tyStmt_success_origin_bound typed
  have completed := ready.emitTerm (.abort .userAbort (some origin))
    (fun _ => by
      apply Inst.SymbolsWithin.term
      · simp [Term.uses]
      · simpa [Term.origin] using originBound
      · simp [Term.successors])
    (fun _ => by trivial)
    (fun _ => abortingTerm_delta _ _ _ _ target _ (Or.inl ⟨_, _, rfl⟩)
      (ceiling.aborts (noteAborts_flag replay)))
  refine ⟨upper, completed, (fun _ _ => rfl), ?_, ?_, ?_⟩
  · exact ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize (fun _ _ => rfl)
      (returnFrame_lowerStmt loop (.abort message origin) trivial _ _ _ _ rfl)
  · exact emitsOnly_emitTerm _ (occurrenceInstructionTerm _) _ _ _ _ rfl
  · exact sites.emitTerm (by simp [Term.successors]) rfl

theorem statementOccurrence_exit {expression : Expr} (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper) :
    StatementOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop scope (.exit expression origin) initial upper := by
  intro source output start finish before after typed replay ceiling _sourceScopes _stack ready sites targetBounds generated loopTargets loopReplay counterTyped included native projects continuation
  obtain ⟨ignored, expressionStart, originTyped, expressionTail⟩ := (st_bind_ok _ _ _ _).mp typed
  have startEq := congrArg Prod.snd ((checkOrg_ok _ _ _ _).mp originTyped).2
  dsimp only at startEq
  subst expressionStart
  obtain ⟨actual, expressionFinish, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp expressionTail
  obtain ⟨roots, middle, expressionReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerExpr expression le initial
  have whole : lowerStmt loop (.exit expression origin) le initial =
      Goose.Lower.emitTerm (.exit lowered.1 (some origin)) le lowered.2 := by
    simp only [lowerStmt, bind_run, lowered]
  have childNative := native.of_prefix (by rw [whole]; exact types_emitTerm _ le lowered.2 _ _ rfl)
  have childProjects := projects
  rw [whole] at childProjects
  have expressionProjects := childProjects.of_advance
    (advB_emitTerm (.exit lowered.1 (some origin)) le lowered.2 _ _ rfl)
  have finalContinuation := continuation
  rw [whole] at finalContinuation
  have expressionContinuation := finalContinuation.of_advance
    (advB_emitTerm (.exit lowered.1 (some origin)) le lowered.2 _ _ rfl)
  have expressionAt : DemandNodeAt (.statement (.exit expression origin)) [0] (.expression expression) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have expressionSource : ∃ path, DemandNodeAt siteRoot path (.expression expression) := by
    obtain ⟨path, location⟩ := source
    exact ⟨path ++ [0], sourcePath_append location expressionAt⟩
  obtain ⟨next, expressionReady, value, retained, ledger, finalSites⟩ :=
    child expressionSource actual start expressionFinish before middle roots expressionTyped expressionReplay
      (noteAborts_before tail ceiling) ready sites targetBounds generated childNative expressionProjects expressionContinuation
  have originBound : origin < le.mod.origins.size := by
    simpa only [le, stmtSourceOrigin, lowerEnv, ← tables.moduleEq] using Core.tyStmt_success_origin_bound typed
  have completed := expressionReady.emitTerm (.exit lowered.1 (some origin))
    (fun live => by
      apply Inst.SymbolsWithin.term
      · simpa [Term.uses] using (value live).bound
      · simpa [Term.origin] using originBound
      · simp [Term.successors])
    (fun _ => by trivial)
    (fun _ => abortingTerm_delta _ _ _ _ target _ (Or.inr ⟨_, _, rfl⟩)
      (ceiling.aborts (noteAborts_flag tail)))
  refine ⟨next, by rw [whole]; exact completed, retained, ?_, ?_, ?_⟩
  · exact ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
      (returnFrame_lowerStmt loop (.exit expression origin) (tyExpr_returnFree expression expressionTyped) _ _ _ _ rfl)
  · rw [whole]
    exact (ledger.underRoot expressionAt).trans (emitsOnly_emitTerm _ (occurrenceInstructionTerm _) _ _ _ _ rfl)
  · rw [whole]
    exact finalSites.emitTerm (by simp [Term.successors]) rfl

theorem statementOccurrence_assert {expression : Expr} (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper) :
    StatementOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop scope (.assertS expression origin) initial upper := by
  intro source output start finish before after typed replay ceiling _sourceScopes _stack ready sites targetBounds generated loopTargets loopReplay counterTyped included native projects continuation
  obtain ⟨ignored, expressionStart, originTyped, expressionTail⟩ := (st_bind_ok _ _ _ _).mp typed
  have startEq := congrArg Prod.snd ((checkOrg_ok _ _ _ _).mp originTyped).2
  dsimp only at startEq
  subst expressionStart
  obtain ⟨actual, expressionFinish, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp expressionTail
  obtain ⟨roots, middle, expressionReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerExpr expression le initial
  have whole : lowerStmt loop (.assertS expression origin) le initial =
      (whenLive () fun _ => do
        let (success, failure) ← fork lowered.1
        Goose.Lower.setCur (some failure)
        Goose.Lower.emitTerm (.abort .assert (some origin))
        Goose.Lower.setCur (some success)) le lowered.2 := by
    simp only [lowerStmt, bind_run, lowered]
  have childNative := native.of_prefix (by rw [whole]; exact types_assert_core lowered.1 origin le lowered.2 _ _ rfl)
  have expressionProjects := projects.restrict (by
    intro recipe member
    rw [whole, recipesUnchangedB_assertCore lowered.1 origin le lowered.2]
    exact member)
  have expressionContinuation := continuation.of_advance (by
    rw [whole]
    exact advB_assert_core lowered.1 origin le lowered.2 _ _ rfl)
  have expressionAt : DemandNodeAt (.statement (.assertS expression origin)) [0] (.expression expression) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have expressionSource : ∃ path, DemandNodeAt siteRoot path (.expression expression) := by
    obtain ⟨path, location⟩ := source
    exact ⟨path ++ [0], sourcePath_append location expressionAt⟩
  obtain ⟨next, expressionReady, value, retained, ledger, finalSites⟩ :=
    child expressionSource actual start expressionFinish before middle roots expressionTyped expressionReplay
      (noteAborts_before tail ceiling) ready sites targetBounds generated childNative expressionProjects expressionContinuation
  have originBound : origin < le.mod.origins.size := by
    simpa only [le, stmtSourceOrigin, lowerEnv, ← tables.moduleEq] using Core.tyStmt_success_origin_bound typed
  have completed := assertCore lowered.1 origin expressionReady (fun live => (value live).bound) originBound
    (ceiling.aborts (noteAborts_flag tail))
  refine ⟨next, by rw [whole]; exact completed, retained, ?_, ?_, ?_⟩
  · exact ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
      (returnFrame_lowerStmt loop (.assertS expression origin) (tyExpr_returnFree expression expressionTyped) _ _ _ _ rfl)
  · rw [whole]
    exact (ledger.underRoot expressionAt).trans
      (assert_emissions occurrenceInstructionTerm lowered.1 origin le lowered.2 _ _ rfl)
  · rw [whole]
    exact finalSites.of_action (assert_emissions (fun _ => trivial) lowered.1 origin)
      (types_assert_core lowered.1 origin) (generatedTargetFrame_assert_core none lowered.1 origin)
      rfl (Nat.le_refl _) (fun _ _ => rfl)

#print axioms statementOccurrence_assert
#print axioms statementOccurrence_abort
#print axioms statementOccurrence_exit

end Goose.Lower.Validation.ReplacementContentFlowSource
