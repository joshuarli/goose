import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverage
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlFrames

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

def NeutralInstruction (instruction : Inst) : Prop := ¬ WriterInstruction instruction

theorem neutral_emitDef (op : Op) (neutral : ∀ value, NeutralInstruction (.def value op)) :
    EmitsOnlyRun NeutralInstruction (Goose.Lower.emitDef op) := by
  intro env before result after run
  exact emitsOnly_emitDef run (neutral _)

theorem neutral_freezeTo (mutability : Mutability) (value : ValueId) :
    EmitsOnlyRun NeutralInstruction (freezeTo mutability value) := by
  intro env before result after run
  rcases freezeTo_cases run with same | frozen
  · exact same.2.symm ▸ .refl _ _
  · exact emitsOnly_emitDef frozen (by simp [NeutralInstruction,WriterInstruction])

theorem neutral_borrowTo (mutability : Mutability) (value : ValueId) :
    EmitsOnlyRun NeutralInstruction (borrowTo mutability value) := by
  intro env before result after run
  rcases borrowTo_cases run with frozen | borrowed
  · exact neutral_freezeTo mutability value _ _ _ _ frozen
  · exact emitsOnly_emitDef borrowed (by simp [NeutralInstruction,WriterInstruction])

theorem neutral_valTy (value : ValueId) : EmitsOnlyRun NeutralInstruction (valTy value) :=
  .unchanged (fun env before => congrArg LS.blocks (valTy_run value env before))

theorem neutral_intTyOf (value : ValueId) : EmitsOnlyRun NeutralInstruction (intTyOf value) := by
  unfold intTyOf
  apply EmitsOnlyRun.bind (neutral_valTy value)
  intro type
  split <;> exact .pure _ _

theorem neutral_coerceTo (type : Ty) (value : ValueId) (origin : OriginId) :
    EmitsOnlyRun NeutralInstruction (coerceTo type value origin) := by
  unfold coerceTo
  apply EmitsOnlyRun.bind (neutral_valTy value)
  intro source
  split
  · exact neutral_emitDef _ (by intro; simp [NeutralInstruction,WriterInstruction])
  · exact (neutral_emitDef _ (by intro; simp [NeutralInstruction,WriterInstruction])).bind fun _ =>
      neutral_emitDef _ (by intro; simp [NeutralInstruction,WriterInstruction])
  · exact .pure _ _

theorem neutral_coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    EmitsOnlyRun NeutralInstruction (coerceSlot slot value origin) := by
  unfold coerceSlot
  apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
  intro env
  cases env.slots[slot]? with
  | none => exact .pure _ _
  | some destination => exact neutral_coerceTo _ _ _

theorem neutral_coerceResult (value : ValueId) (origin : OriginId) :
    EmitsOnlyRun NeutralInstruction (coerceResult value origin) := by
  unfold coerceResult
  apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
  intro env
  cases env.results.head? with
  | none => exact .pure _ _
  | some destination => exact neutral_coerceTo _ _ _

theorem At.neutral {property : Inst → Prop} {env : LEnv} {before : LS} {action : B α}
    (allowed : ∀ instruction, NeutralInstruction instruction → property instruction)
    (emitted : EmitsOnlyRun NeutralInstruction action) : At property env before action :=
  (emitted env before _ _ rfl).map (fun instruction _ proof => allowed instruction proof)

theorem At.neutralDef {property : Inst → Prop} {env : LEnv} {before : LS} {op : Op}
    (allowed : ∀ instruction, NeutralInstruction instruction → property instruction)
    (neutral : ∀ value, NeutralInstruction (.def value op)) : At property env before (Goose.Lower.emitDef op) :=
  .neutral allowed (neutral_emitDef op neutral)

theorem At.neutralEffect {property : Inst → Prop} {env : LEnv} {before : LS} {effect : Effect}
    (allowed : ∀ instruction, NeutralInstruction instruction → property instruction)
    (neutral : NeutralInstruction (.eff effect)) : At property env before (Goose.Lower.emitEffect effect) :=
  .of_run (emitsOnly_emitEffect effect (allowed _ neutral))

theorem At.term {property : Inst → Prop} {env : LEnv} {before : LS} (term : Term)
    (allowed : ∀ instruction, NeutralInstruction instruction → property instruction) :
    At property env before (emitTerm term) := .of_run (emitsOnly_emitTerm term (allowed _ (by simp [NeutralInstruction,WriterInstruction])))

theorem At.whenLive {property : Inst → Prop} {env : LEnv} {before : LS} {default : α}
    {next : BlockId → B α}
    (branches : ∀ block, before.cur = some block → At property env before (next block)) :
    At property env before (whenLive default next) := by
  cases current : before.cur with
  | none => rw [At,whenLive_none _ _ _ current]; exact .refl _ _
  | some block => simpa only [At,whenLive_some _ _ _ current] using branches block current

#print axioms neutral_coerceSlot
#print axioms At.whenLive

end Goose.Lower.Validation.SourceReplacementWriterLedger
