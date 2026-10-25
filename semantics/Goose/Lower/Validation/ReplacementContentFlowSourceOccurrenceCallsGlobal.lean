import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsGlobal
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsPhysicalLists
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallsCheckpoint
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallsConsumedReferences
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SummaryPreservationReplayTypedCallSource
import Goose.Lower.Validation.SummaryPreservationReplayCallSource
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId}

theorem call_argument_paths (callee : ContextId) (arguments : List Arg) (origin : OriginId)
    (argument : Arg) (member : argument ∈ arguments) :
    ∃ path, DemandNodeAt (.expression (.call callee arguments origin)) path (argumentDemandNode argument) := by
  obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
  refine ⟨[index], .child ?_ (.here _)⟩
  cases argument <;> simp [DemandNode.child?, DemandNode.children, argumentDemandNode, row]

theorem globalExpressionOccurrence_call {calleeId : ContextId} {arguments : List Arg} {origin : OriginId}
    (tables : SourceRootTables typingEnv env)
    (accepted : Core.validate env.mod = .ok ())
    (closed : ParameterRootsClosed func)
    (validity : SourceCanonicalRootFloors.SourceRootScopeValid siteRoot)
    (bounded : RootsBelow results (moduleTypedResultUpper env.mod))
    (argumentChild : ∀ argument ∈ arguments, ∀ state provenance,
      PhysicalArgumentOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        (.expression (.call calleeId arguments origin)) argument state provenance) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
      (.call calleeId arguments origin) initial upper := by
  intro present type start finish before after roots typed replay ceiling ready sites targets generated native metadata continuation
  have calleeBound : calleeId < env.mod.contexts.size := by
    simpa only [← tables.moduleEq] using Core.tyExpr_call_success_context_bound typed
  let ctx := env.mod.contexts[calleeId]'calleeBound
  have contextLookup : env.mod.contexts[calleeId]? = some ctx := Array.getElem?_eq_getElem calleeBound
  obtain ⟨callee, implLookup, _checked⟩ := (validate_modOk env.mod accepted).ctx calleeId ctx contextLookup
  have contextTyped : typingEnv.mod.contexts[calleeId]? = some ctx := by
    simpa only [← tables.moduleEq] using contextLookup
  have implTyped : typingEnv.mod.impls[ctx.impl]? = some callee := by
    simpa only [← tables.moduleEq] using implLookup
  obtain ⟨arity, argumentCounter, typedArguments, resultTyped⟩ := tyExpr_call_arguments contextTyped implTyped typed
  have resultType := callResultTy_default resultTyped
  obtain ⟨argumentRoots, argumentState, argumentReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨contents, callReplay⟩ := rpExpr_call_contract argumentReplay replay
  have argumentEffect := effectRefinement_before_of_replay
    (PMono.rpCall env calleeId argumentRoots) (PMonoRebinds.rpCall env calleeId argumentRoots)
    (PFlagsMono.rpCall env calleeId argumentRoots) callReplay ceiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerArgs arguments le initial
  have tailRun : occurrenceCallTail calleeId lowered.1 origin le lowered.2 =
      lowerExpr (.call calleeId arguments origin) le initial := by
    rw [occurrenceCallTail_run, lowerExpr_call_after_args (rfl : lowerArgs arguments le initial = lowered)]
  have argumentNative : NativeRows vt lowered.2 :=
    native.of_prefix (occurrenceCallTail_types calleeId lowered.1 origin le lowered.2 _ _ tailRun)
  obtain ⟨middle, argumentReady, argumentValues, argumentPrefix, argumentLedger, argumentSites, argumentPhysical⟩ :=
    typedPhysicalArgumentsOccurrence arguments argumentChild
      initial upper present (call_argument_paths calleeId arguments origin) callee callee.params.toList
      start argumentCounter before argumentState argumentRoots typedArguments
      (by simpa only [Array.length_toList] using arity.symm) argumentReplay argumentEffect
      ready sites targets generated argumentNative
      (metadata.of_advance (by
        rw [← tailRun]
        exact occurrenceCallTail_advance calleeId lowered.1 origin le lowered.2))
      (continuation.of_advance (by
        rw [← tailRun]
        exact occurrenceCallTail_advance calleeId lowered.1 origin le lowered.2))
  obtain ⟨next, completed, returned, retained, ledger, nextSites⟩ :=
    callOccurrenceCheckpoint argumentReady argumentLedger argumentSites present validity
      (metadata.of_advance (by
        rw [← tailRun]
        exact occurrenceCallTail_advance calleeId lowered.1 origin le lowered.2))
      ⟨typingEnv, start, finish, type, tables.moduleEq.symm, tables.variablesEq.symm, typed⟩ (.here _) accepted
      contextLookup implLookup closed bounded
      (fun live => (argumentValues live).1.trans arity)
      (fun live value member => by
        obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
        exact ((argumentValues live).2 index value row).1)
      (fun live index value row => ((argumentValues live).2 index value row).2.1)
      (fun live value member => by
        obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
        exact ((argumentValues live).2 index value row).2.2)
      (fun live value member mutability payload row => by
        obtain ⟨index, argumentAt⟩ := List.mem_iff_getElem?.mp member
        have checked := (Core.validate_declarativeTables typingEnv.mod
          (by simpa only [tables.moduleEq] using accepted)).implementations callee
            (List.mem_iff_getElem?.mpr ⟨ctx.impl, by
              simpa only [Array.getElem?_toList] using implTyped⟩)
        apply call_arguments_consumed_references checked (by simpa only [Array.length_toList] using arity.symm)
          typedArguments generated argumentNative
          (show lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars returnTypes) initial = lowered by
            change lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars returnTypes) initial =
              lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial
            rw [tables.moduleEq, tables.variablesEq]) live argumentReplay
        · intro selected argument atArgument
          rw [argumentReady.roots.valueSize]
          exact ((argumentValues live).2 selected argument atArgument).1
        · intro selected argument atArgument
          exact ((argumentValues live).2 selected argument atArgument).2.1
        · intro selected borrowed place sourceAt
          refine ⟨[selected], .child ?_ (.here _)⟩
          simp [DemandNode.child?, DemandNode.children, sourceAt]
        · exact argumentAt
        · exact row)
      argumentPhysical
      (by simpa only [le, lowerEnv, ← tables.moduleEq] using Core.tyExpr_call_success_origin_bound typed)
      (by simpa only [le, lowerEnv, Array.size_map] using calleeBound)
      (returnTypes := returnTypes) rfl generated continuation
      (rfl : lowerArgs arguments le initial = lowered) argumentReplay contents callReplay ceiling
  refine ⟨next, completed, ?_, ?_, ledger, nextSites⟩
  · simpa only [resultType] using returned
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, argumentReady.roots.valueSize]
      exact (advB_lowerArgs arguments le initial lowered.1 lowered.2 rfl).vals
    exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (argumentPrefix index bound)

end Goose.Lower.Validation.ReplacementContentFlowSource
