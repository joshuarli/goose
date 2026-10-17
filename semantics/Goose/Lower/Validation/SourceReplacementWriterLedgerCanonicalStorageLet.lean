import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalFinish
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorageCoercions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlSteps
import Goose.Lower.Validation.SummaryPreservationSourceControlKernels
import Goose.Lower.Validation.SummaryPreservationLowerScalarLet
import Goose.Lower.Validation.SourceRootShape

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

private theorem storable_not_refSlice (type : Ty) (stored : type.storable = true) :
    type.isRefSlice = false := by
  cases type <;> simp_all [Ty.storable, Ty.isRefSlice]
  rename_i mu target
  cases target <;> simp_all [Ty.storable, Ty.isRefSlice, Ty.refTarget]

theorem canonical_statementOccurrence_let {ownerRoot : Fragment} {ownerInitial baseline : LS} {typingEnv : TEnv} {env : PEnv}
    {siteRoot : DemandNode} {siteTargets : List BlockId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {loop : Option LoopCtx} {scope : ScopeId} {initial : LS} {upper : Prov}
    {slotId : VarId} {expression : Expr} {origin : OriginId}
    (tables : SourceRootTables typingEnv env) (checked : CtxOk env.mod env.impl env.ctx)
    (child : CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression initial upper) :
    CanonicalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop scope (.letS slotId expression origin)
      initial upper := by
  intro occurrence cursor output start finish before after typed replay ceiling scopes stack ready sites targets generated loopBounds loopReplay _counterTyped _included native metadata continuation
  obtain ⟨path, globalPath⟩ := occurrence
  obtain ⟨actualPath,located⟩ := cursor
  have childPath : DemandNodeAt (.statement (.letS slotId expression origin)) [0] (.expression expression) := .child rfl (.here _)
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerExpr expression le initial
  obtain ⟨localVar, childType, childStart, declared, childTyped, passable, _⟩ := tyStmt_let_children typed
  have declaration := declare_ok _ _ _ _ _ declared
  have variableRow : env.impl.vars[slotId]? = some localVar := by rw [tables.variablesEq]; exact declaration.2.1
  have ordinary : localVar.ty.isRefSlice = false := storable_not_refSlice _ declaration.2.2.2.1
  have originBound : origin < le.mod.origins.size := tables.mutation_origin_bound typed
  have slotBound : slotId < le.slots.size := by
    simpa only [le, lowerEnv, Array.size_mapIdx] using (Array.getElem?_eq_some_iff.mp variableRow).1
  obtain ⟨roots, sourceAfter, childReplay, tail⟩ :
      ∃ roots sourceAfter, rpExpr env expression {before with nextVar := before.nextVar + 1} = .ok (roots, sourceAfter) ∧
        (match env.impl.vars[slotId]? with
        | some found => if found.ty.isRefLike then bindRoots env env.scopes slotId roots else pure ()
        | none => rejP .root s!"variable {slotId} outside the variable table") sourceAfter = .ok ((), after) := by
    simp only [rpStmt] at replay
    inv at replay
    exact replay.2
  have same : after = sourceAfter := by
    simp only [variableRow] at tail
    split at tail
    · exact ((liftV_ok _ _ _).mp tail).2
    · exact congrArg Prod.snd ((st_pure_ok _ _ _).mp tail)
  subst sourceAfter
  have childNative : NativeRows vt lowered.2 := native.of_prefix
    ((types_coerceSlot slotId lowered.1 origin le lowered.2 _ _ rfl).trans
      (types_emitEffect _ le _ _ _ rfl))
  have childMetadata := metadata.of_advance
    ((advB_coerceSlot slotId lowered.1 origin le lowered.2 _ _ rfl).trans
      (advB_emitEffect _ le _ _ _ rfl))
  have childContinuation := continuation.of_advance
    ((advB_coerceSlot slotId lowered.1 origin le lowered.2 _ _ rfl).trans
      (advB_emitEffect _ le _ _ _ rfl))
  obtain ⟨middle, childReady, valueInfo, childPrefix, childLedger, childSites⟩ := child ⟨path ++ [0], globalPath.snoc 0 rfl⟩ ⟨actualPath ++ [0],located.child rfl⟩ childType childStart finish
    {before with nextVar := before.nextVar + 1} after roots childTyped childReplay ceiling ready sites targets generated childNative childMetadata childContinuation
  have suffix : ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      le scopeCount (typedContextSlotUpper env.mod env.ctx env.impl)
      (lowerStmt loop (.letS slotId expression origin) le initial).2 next ∧
      (∀ old, old < middle.vals.size → rootsAt next.vals old = rootsAt middle.vals old) ∧
      OccurrenceLedger env (.statement (.letS slotId expression origin)) (lowerContextAt env.mod env.ctx env.impl) vt next
        lowered.2 (lowerStmt loop (.letS slotId expression origin) le initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le (lowerStmt loop (.letS slotId expression origin) le initial).2
        (lowerContextAt env.mod env.ctx env.impl) vt next := by
    cases current : lowered.2.cur with
    | none =>
      let action : B Unit := do
        let value ← coerceSlot slotId lowered.1 origin
        Goose.Lower.emitEffect (.slotInit slotId value (some origin))
      have stopped := childReady.stopped
        (StoppedGraph.bind (stopped_coerceSlot slotId lowered.1 origin) (fun _ => stopped_emitEffect _)) current
        (rfl : action le lowered.2 = ((), (action le lowered.2).2))
      have stable : StoppedGraph action := StoppedGraph.bind (stopped_coerceSlot slotId lowered.1 origin) (fun _ => stopped_emitEffect _)
      obtain ⟨_, blocks, values, _recipes⟩ := stable le lowered.2 () (action le lowered.2).2 rfl current
      exact ⟨middle, stopped, (fun _ _ => rfl), .of_blocks blocks, childSites.of_blocks blocks values⟩
    | some block =>
      have live : lowered.2.cur.isSome = true := by rw [current]; rfl
      obtain ⟨next, coercedReady, nextValue, nextCurrent, nextBound, retained, coerceLedger, coerceSites⟩ :=
        ReplayBuilder.occurrenceCoerceSlot_canonicalSites slotId (origin := origin) childReady childSites childPath (.expression rfl childReplay)
          current (valueInfo live).bound (valueInfo live).refined originBound
          (native.of_prefix (types_emitEffect (.slotInit slotId (coerceSlot slotId lowered.1 origin le lowered.2).1 (some origin)) le _ _ _ rfl))
      let coerced := coerceSlot slotId lowered.1 origin le lowered.2
      have rootBound : ∀ root ∈ rootsAt next.vals coerced.1,
          root ∈ rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) slotId := by
        by_cases reference : localVar.ty.isRefLike = true
        · have binding := (rpStmt_reference_let_contract variableRow reference childReplay replay).1
          exact bindRootsV_typed_slot_bound checked.annotationShape variableRow ordinary binding nextValue
        · have nonref : localVar.ty.isRefLike = false := Bool.eq_false_iff.mpr reference
          have childNonref : childType.isRefLike = false := (source_passable_refLike_eq passable).trans nonref
          have empty := source_expression_nonref_roots_empty expression tables childTyped childNonref childReplay
          rw [empty] at nextValue
          exact rootsRefine_empty_typed_slot_bound checked.annotationShape variableRow ordinary nextValue
      have completed := coercedReady.emitEffect_live (.slotInit slotId coerced.1 (some origin))
        (by intro _; apply Inst.SymbolsWithin.eff
            · simpa [Effect.uses] using nextBound
            · simpa [Effect.origin] using originBound
            · simpa [Effect.SymbolRefsValid] using slotBound)
        (by intro _; simpa only [InstructionRootsClosed, coercedReady.slotsEq] using rootBound)
        (by intro _; exact effectRefinement_empty _ _)
      have step := occurrence_emitEffect_live (env := env) (root := .statement (.letS slotId expression origin))
        (func := lowerContextAt env.mod env.ctx env.impl) (types := vt) (upper := next)
        (rfl : emitEffect (.slotInit slotId coerced.1 (some origin)) le coerced.2 = _) (by
          intro _
          apply InstructionOccurrences.effect (ordinary := by intro address value origin same; cases same)
            (consumed := by intro value member; simp [GIR.ReplacementContentFlow.Model.accessOperands] at member)
          intro value member
          simp [GIR.ReplacementContentFlow.Model.accessOperands] at member)
      exact ⟨next, completed, retained, coerceLedger.trans step,
        coerceSites.mutationEffect (effect := .slotInit slotId coerced.1 (some origin)) trivial rfl (Nat.le_refl _) (fun _ _ => rfl)⟩
  obtain ⟨next, completed, retained, suffixLedger, finalSites⟩ := suffix
  have retainedAll : ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
    intro old bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, childReady.roots.valueSize]
      exact (advB_lowerExpr expression le initial _ _ rfl).vals
    exact (retained old (Nat.lt_of_lt_of_le bound growth)).trans (childPrefix old bound)
  have growth : middle.vals.size ≤ next.vals.size := by
    rw [childReady.roots.valueSize, completed.roots.valueSize]
    exact ((advB_coerceSlot slotId lowered.1 origin le lowered.2 _ _ rfl).trans
      (advB_emitEffect _ le _ _ _ rfl)).vals
  exact ⟨next, completed, retainedAll, mutation_statement_transfer loop typed rfl ready retainedAll,
    ((childLedger.retained growth retained).underRoot childPath).trans suffixLedger, finalSites⟩

#print axioms canonical_statementOccurrence_let

end Goose.Lower.Validation.SourceReplacementWriterLedger
