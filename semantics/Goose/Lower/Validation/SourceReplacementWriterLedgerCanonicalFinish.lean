import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceOccurrenceFinishActions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem canonical_occurrenceSites_leaveAll {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (scopes : List ScopeId)
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types upper) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.leaveAll scopes le before).2 func types upper := by
  induction scopes generalizing before with
  | nil => exact checked
  | cons scope rest ih => exact ih (checked.emitEffect (effect := .leave scope) trivial rfl)

theorem CanonicalOccurrenceSitesBuilder.finishFunction {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {env : PEnv} {root : DemandNode} {targets : List BlockId} {le : LEnv} {state : LS}
    {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le state func types upper)
    (impl : Impl) (value : ValueId) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le
      (Goose.Lower.finishFunction impl value le state).2 func types upper := by
  apply sites.of_emits
    (finishFunction_emitsOnly impl value (by intro term; trivial) le state _ _ rfl)
    (SummaryPreservation.ReplayBuilder.types_finishFunction impl value le state _ _ rfl)
    (ReplacementIntervalsPreserved.of_run (generatedTargetFrame_finishFunction impl value) rfl)
    (Nat.le_refl _) (fun _ _ => rfl)

#print axioms canonical_occurrenceSites_leaveAll
#print axioms CanonicalOccurrenceSitesBuilder.finishFunction

end Goose.Lower.Validation.SourceReplacementWriterLedger
