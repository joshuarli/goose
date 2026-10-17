import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessKernel
import Goose.Lower.Validation.SummaryPreservationCallOccurrences

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

def occurrenceCallTail (callee : FnId) (arguments : List ValueId) (origin : OriginId) : B ValueId := do
  let returned ← Goose.Lower.emitDef (.call callee arguments (some origin))
  if (← read).mod.noReturn callee then Goose.Lower.emitTerm .unreachable
  pure returned

theorem occurrenceCallTail_run (callee : FnId) (arguments : List ValueId) (origin : OriginId)
    (le : LEnv) (initial : LS) :
    occurrenceCallTail callee arguments origin le initial =
      let emitted := Goose.Lower.emitDef (.call callee arguments (some origin)) le initial
      if le.mod.noReturn callee then (emitted.1, (Goose.Lower.emitTerm .unreachable le emitted.2).2)
      else emitted := by
  by_cases diverges : le.mod.noReturn callee = true
  · simp only [occurrenceCallTail, bind_run, read_apply, diverges, ite_true, pure_run]
  · simp [occurrenceCallTail, bind_run, read_apply, diverges, pure_run]

theorem occurrenceCallTail_types (callee : FnId) (arguments : List ValueId) (origin : OriginId) :
    TypeRun (occurrenceCallTail callee arguments origin) := by
  exact TypeRun.bind (types_emitDef _) fun returned => TypeRun.bind types_read fun environment => by
    cases environment.mod.noReturn callee <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact TypeRun.pure _ | exact TypeRun.bind (types_emitTerm _) fun _ => TypeRun.pure _

theorem occurrenceCallTail_advance (callee : FnId) (arguments : List ValueId) (origin : OriginId)
    (le : LEnv) (initial : LS) :
    initial.Adv (occurrenceCallTail callee arguments origin le initial).2 := by
  rw [occurrenceCallTail_run]
  dsimp only
  split
  · exact (advB_emitDef _ le initial _ _ rfl).trans (advB_emitTerm _ le _ _ _ rfl)
  · exact advB_emitDef _ le initial _ _ rfl

theorem occurrenceCallTail_frames (callee : FnId) (arguments : List ValueId) (origin : OriginId) :
    GeneratedTargetFrameRun none (occurrenceCallTail callee arguments origin) := by
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef none _) fun returned =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_read none) fun environment => by
      cases environment.mod.noReturn callee <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact generatedTargetFrame_pure none _
              | exact GeneratedTargetFrameRun.bind
                  (generatedTargetFrame_emitTerm none .unreachable (by simp [Term.successors]))
                  fun _ => generatedTargetFrame_pure none _

theorem occurrenceCallTail_notReplacement (callee : FnId) (arguments : List ValueId) (origin : OriginId)
    (le : LEnv) (initial : LS) :
    EmitsOnly NotReplacement initial (occurrenceCallTail callee arguments origin le initial).2 := by
  rw [occurrenceCallTail_run]
  dsimp only
  split
  · exact (emitsOnly_emitDef rfl trivial).trans (emitsOnly_emitTerm .unreachable trivial _ _ _ _ rfl)
  · exact emitsOnly_emitDef rfl trivial

theorem occurrenceCallTail_values (callee : FnId) (arguments : List ValueId) (origin : OriginId)
    (le : LEnv) (initial : LS) :
    initial.vals.size ≤ (occurrenceCallTail callee arguments origin le initial).2.vals.size := by
  rw [occurrenceCallTail_run]
  dsimp only
  split
  · exact Nat.le_trans (advB_emitDef _ le initial _ _ rfl).vals (advB_emitTerm _ le _ _ _ rfl).vals
  · exact (advB_emitDef _ le initial _ _ rfl).vals

theorem occurrenceCallTail_result (callee : FnId) (arguments : List ValueId) (origin : OriginId)
    (le : LEnv) (initial : LS) (live : initial.cur.isSome = true) :
    (occurrenceCallTail callee arguments origin le initial).1 = initial.vals.size := by
  cases current : initial.cur with
  | none => simp [current] at live
  | some block =>
    rw [occurrenceCallTail_run, emitDef_run _ _ current]
    split <;> rfl

theorem occurrenceCallTail_ledger {env : PEnv} {root : DemandNode} {func : Func}
    {vt : Array (Option VTy)} {upper : Prov} {callee : FnId} {arguments : List ValueId}
    {origin : OriginId} {le : LEnv} {initial : LS}
    (valid : initial.cur.isSome = true → InstructionOccurrences env root func vt upper
      (.def initial.vals.size (.call callee arguments (some origin)))) :
    OccurrenceLedger env root func vt upper initial (occurrenceCallTail callee arguments origin le initial).2 := by
  have emitted : OccurrenceLedger env root func vt upper initial
      (Goose.Lower.emitDef (.call callee arguments (some origin)) le initial).2 := by
    apply accessEmitDefinition
      (rfl : Goose.Lower.emitDef (.call callee arguments (some origin)) le initial =
        ((Goose.Lower.emitDef (.call callee arguments (some origin)) le initial).1,
          (Goose.Lower.emitDef (.call callee arguments (some origin)) le initial).2))
    intro live
    have result : (Goose.Lower.emitDef (.call callee arguments (some origin)) le initial).1 =
        initial.vals.size := by
      cases current : initial.cur with
      | none => simp [current] at live
      | some block => rw [emitDef_run _ _ current]
    change InstructionOccurrences env root func vt upper
      (.def (Goose.Lower.emitDef (.call callee arguments (some origin)) le initial).1
        (.call callee arguments (some origin)))
    rw [result]
    exact valid live
  rw [occurrenceCallTail_run]
  dsimp only
  split
  · exact emitted.trans (emitsOnly_emitTerm .unreachable
      (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands]) _ _ _ _ rfl)
  · exact emitted

end Goose.Lower.Validation.ReplacementContentFlowSource
