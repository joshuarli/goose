import Goose.Lower.Validation.SourceReplacementWriterLedgerAccepted
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalRebase

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

def contextReplayFragment (module : Core.Module) (impl : Impl) : Fragment :=
  .block none (contextEntryBindings impl (lowerEnv module impl.vars impl.results.toList)) impl.body.value.isSome impl.body

theorem SourceLoweringAt.blockWant {loop : Option LoopCtx} {bindings : List (SlotId × ValueId × OriginId)}
    {want otherWant : Bool} {body : Core.Block} {env : LEnv} {initial before : LS}
    {path : List Nat} {fragment : Fragment}
    (located : SourceLoweringAt (.block loop bindings want body) env initial path fragment before)
    (nonempty : path ≠ []) :
    SourceLoweringAt (.block loop bindings otherWant body) env initial path fragment before := by
  cases path with
  | nil => exact False.elim (nonempty rfl)
  | cons index rest =>
    cases body
    simpa only [SourceLoweringAt,Fragment.at?,Fragment.child?,Fragment.children] using located

theorem contextReplay_statement_cursor {module : Core.Module} {impl : Impl}
    {path : List Nat} {loop : Option LoopCtx} {statement : Stmt} {before : LS}
    (located : SourceLoweringAt (contextReplayFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) path (.statement loop statement) before) :
    SourceLoweringAt (contextFragment module impl) (lowerEnv module impl.vars impl.results.toList)
      (contextInitial module impl) path (.statement loop statement) before := by
  have nonempty : path ≠ [] := by
    intro same
    subst path
    simp [SourceLoweringAt,Fragment.at?,contextReplayFragment] at located
  exact located.blockWant nonempty

theorem contextInitial_instructions (module : Core.Module) (impl : Impl) :
    (contextInitial module impl).insts = [] :=
  entryReplayState_instructions _ _

#print axioms SourceLoweringAt.blockWant
#print axioms contextReplay_statement_cursor
#print axioms contextInitial_instructions

end Goose.Lower.Validation.SourceReplacementWriterLedger
