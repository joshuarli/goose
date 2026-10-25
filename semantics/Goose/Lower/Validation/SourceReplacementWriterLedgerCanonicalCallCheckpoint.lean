import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallsActions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

theorem canonical_callOccurrenceCheckpoint {env : PEnv} {calleeId : ContextId} {ctx : Context} {callee : Impl}
    {func : Func} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {target : Core.Eff} {returnTypes : List Ty} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {initial state : LS} {upper : Prov} {arguments : List ValueId} {syntaxArgs : List Arg}
    {sourceArgs : List (List RootRef)} {sourceRoots : List RootRef}
    {before addressed after : RState} {origin : OriginId}
    {root siteRoot : DemandNode} {siteTargets : List BlockId} {path : List Nat}
    (ready : ReplayBuilder (lower env.mod) results vt func target le scopeCount slots state upper)
    (ledger : OccurrenceLedger env root func vt upper initial state)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le state func vt upper)
    (callAtSite : ∃ sitePath, DemandNodeAt siteRoot sitePath (.expression (.call calleeId syntaxArgs origin)))
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (metadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func state)
    (sourceTyping : ∃ typingEnv start finish type, typingEnv.mod = env.mod ∧
      typingEnv.vars = env.impl.vars ∧
      Core.tyExpr typingEnv (.call calleeId syntaxArgs origin) start = .ok (type, finish))
    (sourcePath : DemandNodeAt root path (.expression (.call calleeId syntaxArgs origin)))
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (closed : ParameterRootsClosed func)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (argumentCount : state.cur.isSome = true → arguments.length = callee.params.size)
    (operandBounds : state.cur.isSome = true → ∀ value ∈ arguments, value < state.vals.size)
    (argumentRoots : state.cur.isSome = true → ∀ (index : Nat) (value : ValueId),
      arguments[index]? = some value → ∃ roots, sourceArgs[index]? = some roots ∧
        GIR.RootsRefine func (rootsAt upper.vals value) roots)
    (argumentOccurrences : state.cur.isSome = true → ∀ value ∈ arguments,
      OperandOccurrence env root func upper value)
    (argumentConsumed : state.cur.isSome = true → ∀ value ∈ arguments, ∀ mutability payload,
      vt[value]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func vt upper value)
    (argumentPhysical : state.cur.isSome = true → CallArgumentsPhysical env upper syntaxArgs arguments)
    (originBound : origin < le.mod.origins.size) (calleeBound : calleeId < le.sigs.size)
    (environment : le = lowerEnv env.mod env.impl.vars returnTypes)
    (generated : GeneratedBuilderState initial)
    (continuation : NativeBuilderContinuation func
      (lowerExpr (.call calleeId syntaxArgs origin) le initial).2)
    (argumentsRun : lowerArgs syntaxArgs le initial = (arguments, state))
    (argumentsReplay : rpArgs env syntaxArgs before = .ok (sourceArgs, addressed))
    (contents : checkContents env calleeId syntaxArgs sourceArgs = .ok ())
    (callReplay : rpCall env calleeId sourceArgs addressed = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target le scopeCount slots
        (lowerExpr (.call calleeId syntaxArgs origin) le initial).2 next ∧
      ((lowerExpr (.call calleeId syntaxArgs origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.call calleeId syntaxArgs origin) le initial).2
          (lowerExpr (.call calleeId syntaxArgs origin) le initial).1 sourceRoots
          (.data ((callee.results[0]?).getD Ty.unit))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func vt next initial
        (lowerExpr (.call calleeId syntaxArgs origin) le initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le
        (lowerExpr (.call calleeId syntaxArgs origin) le initial).2 func vt next := by
  obtain ⟨next, completed, returned, retained, origins, emittedResult⟩ :=
    ready.callWithArgumentOrigins accepted contextLookup implLookup closed bounded argumentCount
      operandBounds argumentRoots originBound calleeBound argumentsRun callReplay wholeEffect
  have tailRun : occurrenceCallTail calleeId arguments origin le state =
      lowerExpr (.call calleeId syntaxArgs origin) le initial := by
    rw [occurrenceCallTail_run, lowerExpr_call_after_args argumentsRun]
  have valGrowth : state.vals.size ≤
      (lowerExpr (.call calleeId syntaxArgs origin) le initial).2.vals.size := by
    rw [← tailRun]
    exact occurrenceCallTail_values _ _ _ _ _
  have ghostGrowth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize, completed.roots.valueSize]
    exact valGrowth
  have callLedger : OccurrenceLedger env root func vt next state
      (lowerExpr (.call calleeId syntaxArgs origin) le initial).2 := by
    rw [← tailRun]
    apply occurrenceCallTail_ledger
    intro live
    have result := emittedResult live
    have resultId : (lowerExpr (.call calleeId syntaxArgs origin) le initial).1 = state.vals.size := by
      rw [← tailRun]
      exact occurrenceCallTail_result _ _ _ _ _ live
    refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store ?_, ?_⟩
    · intro value member _
      have argumentMember : value ∈ arguments := by
        simpa only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
      exact (argumentOccurrences live value argumentMember).retained ghostGrowth retained
    · intro value address same _
      cases same
    · intro value fn args callOrigin same
      cases same
      refine ⟨env, path, syntaxArgs, origin, before, sourceArgs, addressed, sourceRoots, after,
        rfl, rfl, sourcePath, argumentsReplay, contents, callReplay, ?_, ?_, ?_, ?_⟩
      · rw [← resultId, completed.roots.valueSize]
        exact result.bound
      · rw [← resultId]
        exact result.refined
      · intro index argument row
        have bound := operandBounds live argument (List.mem_of_getElem? row)
        refine ⟨?_, (origins live index argument row).1⟩
        rw [completed.roots.valueSize]
        exact Nat.lt_of_lt_of_le bound valGrowth
      · refine ⟨(argumentPhysical live).retained
          (fun index argument row => by
            rw [ready.roots.valueSize]
            exact operandBounds live argument (List.mem_of_getElem? row)) retained, ?_⟩
        obtain ⟨sitePath, callAtSite⟩ := callAtSite
        refine ⟨returnTypes, initial, state, siteRoot, sitePath, ?_, generated, live, ?_,
          callAtSite, validity, metadata, sourceTyping⟩
        · simpa only [← environment] using argumentsRun
        · apply continuation.of_advance
          rw [← tailRun]
          exact occurrenceCallTail_advance calleeId arguments origin le state
    · intro address value storeOrigin same
      cases same
    · intro value member mutability payload row
      have argumentMember : value ∈ arguments := by
        simpa only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
      exact (argumentConsumed live value argumentMember mutability payload row).retained ghostGrowth retained
  have finalLedger := (ledger.retained ghostGrowth retained).trans callLedger
  have finalSites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le
      (lowerExpr (.call calleeId syntaxArgs origin) le initial).2 func vt next := by
    apply sites.of_emits
    · rw [← tailRun]
      exact occurrenceCallTail_notReplacement _ _ _ _ _
    · exact occurrenceCallTail_types calleeId arguments origin le state _ _ tailRun
    · exact .of_run (occurrenceCallTail_frames calleeId arguments origin) tailRun
    · exact ghostGrowth
    · exact retained
  exact ⟨next, completed, returned, retained, finalLedger, finalSites⟩

#print axioms canonical_callOccurrenceCheckpoint

end Goose.Lower.Validation.SourceReplacementWriterLedger
