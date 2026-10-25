import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorageCoercions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorageReturnUnit
import Goose.Lower.Validation.SummaryPreservationSourceReturnKernels

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem returnCoerce_dead (type : Ty) (value : ValueId) (origin : OriginId)
    (le : LEnv) (state : LS) (dead : state.cur = none) :
    (coerceTo type value origin le state).2 = state := by
  rcases coerceTo_cases (r' := (coerceTo type value origin le state).1) rfl with same | frozen | sliced
  · exact same.2
  · obtain ⟨_, _, run⟩ := frozen
    rw [emitDef_none _ _ dead] at run
    exact (congrArg Prod.snd run).symm
  · obtain ⟨_, view, middle, _, first, second⟩ := sliced
    rw [emitDef_none _ _ dead] at first
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj first
    rw [emitDef_none _ _ dead] at second
    exact (congrArg Prod.snd second).symm

private theorem returnLeave_current (scopes : List ScopeId) (le : LEnv) (state : LS) :
    (Goose.Lower.leaveAll scopes le state).2.cur = state.cur := by
  induction scopes generalizing state with
  | nil => rfl
  | cons scope rest ih =>
    simp only [Goose.Lower.leaveAll, bind_run]
    rw [ih]
    cases current : state.cur with
    | none => rw [emitEffect_none _ _ current]; exact current
    | some block => rw [emitEffect_run _ _ current]; exact current

private theorem returnLeaveTo_current (le : LEnv) (state : LS) :
    (Goose.Lower.leaveTo 0 le state).2.cur = state.cur := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using returnLeave_current _ le state

theorem statementOccurrence_return {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov} {origin : OriginId} {expression : Expr}
    (tables : SourceRootTables typingEnv env)
    (implementation : typingEnv.impl = some env.impl)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (checked : CtxOk env.mod env.impl env.ctx)
    (child : ExpressionOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper) :
    StatementOccurrenceReplayAt typingEnv env results vt target scopeCount siteRoot siteTargets loop scope (.ret (some expression) origin) initial upper := by
  intro occurrence output start finish before after typed replay ceiling _scopes stack ready sites targets generated _loops _loopReplay _counter _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨expected, actual, impl, outside, implAt, resultTypes, expressionTyped, passable, _⟩ := tyStmt_return_children typed
  obtain ⟨roots, middleState, expressionReplay, checking⟩ := (st_bind_ok _ _ _ _).mp replay
  have resultCheck := (liftV_ok _ _ _).mp checking
  have same : after = middleState := resultCheck.2
  subst middleState
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let value := lowerExpr expression le initial
  let coerced := coerceResult value.1 origin le value.2
  let left := Goose.Lower.leaveTo 0 le coerced.2
  have whole : lowerStmt loop (.ret (some expression) origin) le initial =
      emitTerm (.ret [coerced.1] (some origin)) le left.2 := by
    simp only [lowerStmt, bind_run, value, coerced, left]
    rfl
  have childNative : NativeRows vt value.2 := by
    rw [whole] at native
    exact ((native.of_prefix (types_emitTerm _ le left.2 _ _ rfl)).of_prefix
      (types_leaveTo 0 le coerced.2 _ _ rfl)).of_prefix (types_coerceResult value.1 origin le value.2 _ _ rfl)
  have childMetadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl) value.2 := by
    rw [whole] at metadata
    exact ((metadata.of_advance (advB_emitTerm _ le left.2 _ _ rfl)).of_advance
      (advB_leaveTo 0 le coerced.2 _ _ rfl)).of_advance (advB_coerceResult value.1 origin le value.2 _ _ rfl)
  have childContinuation : NativeBuilderContinuation
      (lowerContextAt env.mod env.ctx env.impl) value.2 := by
    rw [whole] at continuation
    exact ((continuation.of_advance (advB_emitTerm _ le left.2 _ _ rfl)).of_advance
      (advB_leaveTo 0 le coerced.2 _ _ rfl)).of_advance (advB_coerceResult value.1 origin le value.2 _ _ rfl)
  obtain ⟨middle, childReady, childValue, childPrefix, childLedger, childSites⟩ :=
    child ⟨path ++ [0], globalPath.snoc 0 rfl⟩ actual start finish before after roots
      expressionTyped expressionReplay ceiling ready sites targets generated childNative childMetadata childContinuation
  have originBound : origin < le.mod.origins.size := tables.mutation_origin_bound typed
  have localPath : DemandNodeAt (.statement (.ret (some expression) origin)) [0] (.expression expression) := .child rfl (.here _)
  have coercePackage : ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target le scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) coerced.2 next ∧
      (coerced.2.cur.isSome = true → coerced.1 < coerced.2.vals.size ∧ GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt next.vals coerced.1) roots) ∧
      (∀ old, old < middle.vals.size → rootsAt next.vals old = rootsAt middle.vals old) ∧
      OccurrenceLedger env (.statement (.ret (some expression) origin)) (lowerContextAt env.mod env.ctx env.impl) vt next value.2 coerced.2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets le coerced.2 (lowerContextAt env.mod env.ctx env.impl) vt next := by
    cases current : value.2.cur with
    | none =>
      have stateEq : coerced.2 = value.2 := by
        simp only [coerced, coerceResult, bind_run, read_apply]
        cases destination : le.results.head? with
        | none => rfl
        | some type => exact returnCoerce_dead type value.1 origin le value.2 current
      rw [stateEq]
      exact ⟨middle, childReady, by simp [current], fun _ _ => rfl, .refl _ _, childSites⟩
    | some block =>
      have live : value.2.cur.isSome = true := by simp [current]
      obtain ⟨next, nextReady, refined, selected, bound, retained, ledger, nextSites⟩ :=
        ReplayBuilder.occurrenceCoerceResult origin childReady childSites localPath
          (.expression rfl expressionReplay) current (childValue live).bound (childValue live).refined originBound
          (by
            rw [whole] at native
            exact (native.of_prefix (types_emitTerm _ le left.2 _ _ rfl)).of_prefix
              (types_leaveTo 0 le coerced.2 _ _ rfl))
      exact ⟨next, nextReady, fun _ => ⟨bound, refined⟩, retained, ledger, nextSites⟩
  obtain ⟨next, coercedReady, returned, coercePrefix, coerceLedger, coerceSites⟩ := coercePackage
  have childGrowth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, childReady.roots.valueSize]
    exact (advB_lowerExpr expression le initial _ _ rfl).vals
  have coerceGrowth : middle.vals.size ≤ next.vals.size := by
    rw [childReady.roots.valueSize, coercedReady.roots.valueSize]
    exact (advB_coerceResult value.1 origin le value.2 _ _ rfl).vals
  have retained (old : Nat) (bound : old < upper.vals.size) : rootsAt next.vals old = rootsAt upper.vals old :=
    (coercePrefix old (Nat.lt_of_lt_of_le bound childGrowth)).trans (childPrefix old bound)
  have leftReady := coercedReady.leaveTo 0 (by
    have coerceStack : coerced.2.stack = value.2.stack := (advB_coerceResult value.1 origin le value.2 _ _ rfl).stack
    have childStack : value.2.stack = initial.stack := (advB_lowerExpr expression le initial _ _ rfl).stack
    change ∀ entered ∈ coerced.2.stack, entered < scopeCount
    rw [coerceStack, childStack]
    exact stack outside)
  have leftGrowth := advB_leaveTo 0 le coerced.2 _ _ rfl
  have completed := leftReady.emitTerm (.ret [coerced.1] (some origin))
    (by
      intro live
      have returnedLive : coerced.2.cur.isSome = true := by simpa only [left, returnLeaveTo_current] using live
      apply Inst.SymbolsWithin.term
      · intro operand member
        have identity := List.mem_singleton.mp member
        subst operand
        exact Nat.lt_of_lt_of_le (returned returnedLive).1 leftGrowth.vals
      · simpa [Term.origin] using originBound
      · simp [Term.successors])
    (by intros; trivial) (by intros; exact effectRefinement_empty _ _)
  have leaveLedger : OccurrenceLedger env (.statement (.ret (some expression) origin)) (lowerContextAt env.mod env.ctx env.impl) vt next coerced.2 left.2 :=
    occurrenceLedger_leaveAll _ le coerced.2 _ _ rfl
  have leftSites : OccurrenceSitesBuilder env siteRoot siteTargets le left.2 (lowerContextAt env.mod env.ctx env.impl) vt next :=
    occurrenceSites_leaveAll _ coerceSites
  have finalSites := leftSites.emitTerm (by simp [Term.successors]) (rfl : emitTerm (.ret [coerced.1] (some origin)) le left.2 = _)
  have ledger := (((childLedger.retained coerceGrowth coercePrefix).underRoot localPath).trans coerceLedger).trans
    (leaveLedger.trans (emitsOnly_emitTerm (.ret [coerced.1] (some origin))
      (InstructionOccurrences.term _ _ _ _ _ _) le left.2 _ _ rfl))
  refine ⟨next, ?_, retained, ?_, ?_, ?_⟩
  · rw [whole]; exact completed
  · intro declared declaredBounds prior
    apply prior.returned_expression loop ready.symbols ready.roots.valueSize generated expressionTyped rfl (rfl : coerceResult value.1 origin le value.2 = coerced) retained
    intro live root member
    by_cases reference : (env.impl.results[0]?).any Ty.isRefLike = true
    · apply declaredBounds root
      have candidate := checkedResult_refinedResultUpper checked (returned live).2 resultCheck.1
      simpa only [contextTypedResultUpper, implementationRow, reference, ite_true, contextRefinedResultUpper] using candidate root member
    · have nonref : (env.impl.results[0]?).any Ty.isRefLike = false := Bool.eq_false_iff.mpr reference
      have scalar := source_return_scalar_roots typed implementation nonref rfl expressionTyped childValue childReady.roots.valueSize
        (rfl : coerceResult value.1 origin le value.2 = coerced) coercePrefix live
      rw [scalar] at member
      cases member
  · rw [whole]; exact ledger
  · rw [whole]; exact finalSites

#print axioms statementOccurrence_return

end Goose.Lower.Validation.ReplacementContentFlowSource
