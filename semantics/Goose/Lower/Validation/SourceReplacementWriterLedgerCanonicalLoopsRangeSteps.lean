import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsBody

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}


theorem canonical_scalarDef {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (result : ValueId) (op : Op)
    (scalar : ∀ operand ∈ GIR.ReplacementContentFlow.Model.accessOperands (.def result op),
      valRefLike types operand = false)
    (noLoad : ∀ address, op ≠ .load address)
    (noCall : ∀ callee arguments origin, op ≠ .call callee arguments origin) :
    InstructionOccurrences env root func types upper (.def result op) := by
  refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intro address value origin same; cases same), ?_⟩
  · intro operand member reference
    rw [scalar operand member] at reference
    cases reference
  · intro value address same reference
    exact False.elim (noLoad address (Inst.def.inj same).2)
  · intro value callee arguments origin same
    exact False.elim (noCall callee arguments origin (Inst.def.inj same).2)
  · intro operand member mutability payload row
    have reference : valRefLike types operand = true := by simp [valRefLike, row, VTy.refLike, Ty.isRefLike]
    rw [scalar operand member] at reference
    cases reference

theorem canonical_occurrenceLedger_rangeBack {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} (type : IntTy) (counter : ValueId) (header : BlockId)
    (scalar : valRefLike types counter = false) :
    EmitsOnlyRun (InstructionOccurrences env root func types upper) (rangeBack type counter header) := by
  unfold rangeBack
  apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
  intro live
  cases live with
  | false => exact .pure _ _
  | true =>
    simp only [ite_true]
    apply EmitsOnlyRun.bind (next := fun value => Goose.Lower.emitTerm (.br header [value]))
    · intro le before result after run
      exact emitsOnly_emitDef run (InstructionOccurrences.next _ _ _ scalar)
    · intro value
      exact emitsOnly_emitTerm _ (occurrenceInstructionTerm _)

theorem canonical_occurrenceSites_rangeBack {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (type : IntTy) (counter : ValueId) (header : BlockId) (included : header ∈ targets)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ value, value < old.vals.size → rootsAt next.vals value = rootsAt old.vals value) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le (rangeBack type counter header le before).2 func types next := by
  have initialSites := checked.ghost_retained growth retained
  cases current : before.cur with
  | none => simpa only [rangeBack, bind_run, isLive_none current, Bool.false_eq_true, ite_false, pure_run] using initialSites
  | some block =>
    have incremented := initialSites.emitDef (op := .next type counter) rfl (Nat.le_refl _) (fun _ _ => rfl)
    have branched := incremented.emitTerm (term := .br header [(emitDef (.next type counter) le before).1])
      (by
        intro destination member
        have same : destination = header := by simpa [Term.successors] using member
        exact Or.inl (same.symm ▸ included)) rfl
    simp only [rangeBack, bind_run, isLive_run current, ite_true]
    exact branched

#print axioms canonical_occurrenceLedger_rangeBack
#print axioms canonical_occurrenceSites_rangeBack

end Goose.Lower.Validation.SourceReplacementWriterLedger
