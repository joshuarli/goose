import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessBorrow
import Goose.Lower.Validation.SummaryPreservationReplayNativeReference
import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

theorem canonical_borrowReferenceOccurrence {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial : LS} {upper : Prov}
    {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}
    (mutability : Mutability) (targetType : Ty) (address : ValueId) (sourceRoots : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots initial upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le initial func vt upper)
    (input : initial.cur.isSome = true → address < initial.vals.size ∧
      GIR.RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (borrowTo mutability address le initial).2 next ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        ReplayValue func next (borrowTo mutability address le initial).2
          (borrowTo mutability address le initial).1 sourceRoots (.data (.ref mutability targetType))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func vt next initial (borrowTo mutability address le initial).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets le
        (borrowTo mutability address le initial).2 func vt next := by
  obtain ⟨next, completed, returned, retained⟩ :=
    ready.borrowReference mutability targetType address sourceRoots input
  have growth := accessRootsGrowth ready completed
    (advB_borrowTo mutability address le initial _ _ rfl).vals
  have emitted : OccurrenceLedger env root func vt next initial (borrowTo mutability address le initial).2 :=
    accessBorrowEmits rfl
      (fun _ => by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
      (fun _ => by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
  have withoutReplacement : EmitsOnly NotReplacement initial (borrowTo mutability address le initial).2 :=
    accessBorrowEmits rfl (fun _ => trivial) (fun _ => trivial)
  exact ⟨next, completed, returned, retained, emitted,
    sites.of_emits withoutReplacement (types_borrowTo mutability address le initial _ _ rfl)
      (.of_run (generatedTargetFrame_borrowTo none mutability address) rfl) growth retained⟩


theorem canonical_occurrenceReplay_reference {typingEnv : TEnv} {env : PEnv} {context : ContextId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {place : Place}
    (mutability : Mutability) (source : SourceContextEnvironment typingEnv env context)
    (child : ∀ initial upper, CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place initial upper) :
    ∀ initial upper, CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets (.ref mutability place) initial upper := by
  intro initial upper here cursor type start finish before after sourceRoots typed replayed ceiling ready sites targets generated native metadata continuation
  obtain ⟨info, childFinish, childTyped, shape, _⟩ := tyExpr_ref_place typed
  subst type
  have placeReplay : rpPlace env place before = .ok (sourceRoots, after) := replayed
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let lowered := lowerPlace place le initial
  have childNative := native.of_prefix (types_borrowTo mutability lowered.1 le lowered.2 _ _ rfl)
  have childMetadata := metadata.of_advance (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl)
  have childContinuation := continuation.of_advance (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl)
  obtain ⟨middle, middleReady, input, retained, ledger, childSites⟩ :=
    child initial upper (accessChildPresent here 0 rfl)
    (by obtain ⟨path,located⟩ := cursor; exact ⟨path ++ [0],located.child rfl⟩) info start childFinish before after sourceRoots
      childTyped placeReplay ceiling ready sites targets generated childNative childMetadata childContinuation
  obtain ⟨next, nextReady, value, nextRetained, tailLedger, finalSites⟩ :=
    canonical_borrowReferenceOccurrence (root := .expression (.ref mutability place)) mutability info.ty lowered.1 sourceRoots
      middleReady childSites input
  have growth := accessRootsGrowth middleReady nextReady (advB_borrowTo mutability lowered.1 le lowered.2 _ _ rfl).vals
  refine ⟨next, nextReady, value, ?_, ?_, finalSites⟩
  · intro old bound
    have middleBound := Nat.lt_of_lt_of_le bound (accessRootsGrowth ready middleReady
      (advB_lowerPlace place le initial _ _ rfl).vals)
    exact (nextRetained old middleBound).trans (retained old bound)
  · exact ((ledger.retained growth nextRetained).underRoot (accessChildNode 0 rfl)).trans tailLedger

#print axioms canonical_occurrenceReplay_reference

end Goose.Lower.Validation.SourceReplacementWriterLedger
