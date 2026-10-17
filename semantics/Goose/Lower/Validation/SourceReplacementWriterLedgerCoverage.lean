import Goose.Lower.Validation.SourceReplacementWriterLedgerEmissions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

def ChildrenCovered (property : Inst → Prop) (fragment : Fragment) (env : LEnv) (before : LS) : Prop :=
  ∀ index child start, fragment.child? env before index = some (child,start) →
    EmitsOnly property start (child.finish env start)

def EmissionsCovered (property : Inst → Prop) (fragment : Fragment) (env : LEnv) (before : LS) : Prop :=
  ∀ emission ∈ fragment.emissions env before, property emission.instruction

def OrdinaryFragment : Fragment → Prop
  | .expression (.ifE ..) | .expression (.and ..) | .expression (.or ..)
    | .expression (.blockE ..) => False
  | .expression _ | .place _ | .view _ | .bound _ => True
  | _ => False

def EmissionCoverage (property : Inst → Prop) (fragment : Fragment) (env : LEnv) (before : LS) : Prop :=
  (∀ instruction, ¬ WriterInstruction instruction → property instruction) →
    ChildrenCovered property fragment env before →
      EmissionsCovered property fragment env before →
        EmitsOnly property before (fragment.finish env before)

def At (property : Inst → Prop) (env : LEnv) (before : LS) (action : B α) : Prop :=
  EmitsOnly property before (action env before).2

theorem At.bind {property : Inst → Prop} {env : LEnv} {before : LS}
    {first : B α} {next : α → B β}
    (head : At property env before first)
    (tail : At property env (first env before).2 (next (first env before).1)) :
    At property env before (first >>= next) := head.trans tail

theorem At.pure (property : Inst → Prop) (env : LEnv) (before : LS) (value : α) :
    At property env before (pure value) := .refl _ _

theorem At.of_blocks {property : Inst → Prop} {env : LEnv} {before : LS} {action : B α}
    (same : (action env before).2.blocks = before.blocks) : At property env before action :=
  EmitsOnly.of_blocks same

theorem At.of_run {property : Inst → Prop} {env : LEnv} {before : LS} {action : B α}
    (emitted : EmitsOnlyRun property action) : At property env before action :=
  emitted env before _ _ rfl

theorem At.emitEffect {property : Inst → Prop} {env : LEnv} {before : LS} {effect : Effect}
    (allowed : before.cur.isSome = true → property (.eff effect)) :
    At property env before (emitEffect effect) := by
  cases current : before.cur with
  | none => rw [At,emitEffect_none effect env current]; exact .refl _ _
  | some block => exact emitsOnly_emitEffect effect (allowed (by simp [current])) _ _ _ _ rfl

theorem At.emitDef {property : Inst → Prop} {env : LEnv} {before : LS} {op : Op}
    (allowed : before.cur.isSome = true → property (.def before.vals.size op)) :
    At property env before (emitDef op) := by
  cases current : before.cur with
  | none => rw [At,emitDef_none op env current]; exact .refl _ _
  | some block => exact emitsOnly_emitDef rfl (allowed (by simp [current]))

theorem ChildrenCovered.at_index {property : Inst → Prop} {fragment child : Fragment}
    {env : LEnv} {before start : LS} (children : ChildrenCovered property fragment env before)
    (index : Nat) (row : fragment.child? env before index = some (child,start)) :
    EmitsOnly property start (child.finish env start) := children index child start row

theorem EmissionsCovered.effect {property : Inst → Prop} {fragment : Fragment}
    {env : LEnv} {before current : LS} {effect : Effect}
    (events : EmissionsCovered property fragment env before)
    (member : ∀ live : current.cur.isSome = true,
      (⟨current,(emitEffect effect env current).2,.eff effect⟩ : Emission) ∈ fragment.emissions env before) :
    At property env current (emitEffect effect) := by
  apply At.emitEffect
  intro live
  exact events _ (member live)

theorem EmissionsCovered.definition {property : Inst → Prop} {fragment : Fragment}
    {env : LEnv} {before current : LS} {op : Op}
    (events : EmissionsCovered property fragment env before)
    (member : ∀ live : current.cur.isSome = true,
      (⟨current,(emitDef op env current).2,.def current.vals.size op⟩ : Emission) ∈ fragment.emissions env before) :
    At property env current (emitDef op) := by
  apply At.emitDef
  intro live
  exact events _ (member live)

#print axioms At.bind
#print axioms At.emitEffect
#print axioms At.emitDef

end Goose.Lower.Validation.SourceReplacementWriterLedger
