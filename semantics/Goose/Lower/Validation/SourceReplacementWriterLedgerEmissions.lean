import Goose.Lower.Validation.SourceReplacementWriterLedger

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

structure Emission where
  before : LS
  after : LS
  instruction : Inst

def effectEmission (env : LEnv) (before : LS) (effect : Effect) : List Emission :=
  if before.cur.isSome then [⟨before,(emitEffect effect env before).2,.eff effect⟩] else []

def definitionEmission (env : LEnv) (before : LS) (op : Op) : List Emission :=
  if before.cur.isSome then [⟨before,(emitDef op env before).2,.def before.vals.size op⟩] else []

def initializationEmissions (env : LEnv) : List (SlotId × ValueId × OriginId) → LS → List Emission
  | [], _ => []
  | (slot,value,origin) :: rest, before =>
      effectEmission env before (.slotInit slot value (some origin)) ++
        initializationEmissions env rest (emitEffect (.slotInit slot value (some origin)) env before).2

def Fragment.emissions (fragment : Fragment) (env : LEnv) (before : LS) : List Emission :=
  match fragment with
  | .expression (.call callee arguments origin) =>
    let lowered := lowerArgs arguments env before
    definitionEmission env lowered.2 (.call callee lowered.1 (some origin))
  | .statement _ (.letS slot syntaxExpr origin) =>
    let lowered := lowerExpr syntaxExpr env before
    let coerced := coerceSlot slot lowered.1 origin env lowered.2
    effectEmission env coerced.2 (.slotInit slot coerced.1 (some origin))
  | .statement _ (.assign sourcePlace syntaxExpr origin) =>
    let addressed := lowerPlace sourcePlace env before
    let lowered := lowerExpr syntaxExpr env addressed.2
    effectEmission env lowered.2 (.store addressed.1 lowered.1 (some origin))
  | .statement _ (.assignOp op sourcePlace syntaxExpr origin) =>
    let addressed := lowerPlace sourcePlace env before
    let loaded := emitDef (.load addressed.1) env addressed.2
    let lowered := lowerExpr syntaxExpr env loaded.2
    let integer := intTyOf loaded.1 env lowered.2
    let combined := emitDef (.bin op integer.1 loaded.1 lowered.1 (some origin)) env integer.2
    effectEmission env combined.2 (.store addressed.1 combined.1 (some origin))
  | .statement _ (.rebind slot syntaxExpr origin) =>
    let lowered := lowerExpr syntaxExpr env before
    let coerced := coerceSlot slot lowered.1 origin env lowered.2
    let addressed := emitDef (.slotAddr slot) env coerced.2
    effectEmission env addressed.2 (.store addressed.1 coerced.1 (some origin))
  | .statement _ (.assignWhole sourcePlace syntaxExpr origin) =>
    let addressed := lowerPlace sourcePlace env before
    let cleared := emitEffect (.clear addressed.1 (some origin)) env addressed.2
    let lowered := lowerExpr syntaxExpr env cleared.2
    effectEmission env lowered.2 (.replace addressed.1 lowered.1 (some origin))
  | .block _ bindings _ (.mk scope _ _) =>
    let entered := emitEffect (.enter scope) env before
    let inside := pushScope scope env entered.2
    initializationEmissions env bindings inside.2
  | _ => []

def WriterInstruction : Inst → Prop
  | .def _ (.call ..) => True
  | .eff (.slotInit ..) | .eff (.store ..) | .eff (.replace ..) => True
  | _ => False

def InstructionSource (root : Fragment) (env : LEnv) (initial : LS) (instruction : Inst) : Prop :=
  WriterInstruction instruction →
    ∃ path fragment before emission,
      SourceLoweringAt root env initial path fragment before ∧
      emission ∈ fragment.emissions env before ∧ emission.instruction = instruction

def Emission.Run (env : LEnv) (emission : Emission) : Prop :=
  emission.before.cur.isSome = true ∧
    match emission.instruction with
    | .eff effect => emitEffect effect env emission.before = ((),emission.after)
    | .def result op => emitDef op env emission.before = (result,emission.after)
    | .term _ => False

theorem effectEmission_run {env : LEnv} {before : LS} {effect : Effect} {emission : Emission}
    (member : emission ∈ effectEmission env before effect) : emission.Run env := by
  unfold effectEmission at member
  split at member
  · have same := List.mem_singleton.mp member
    subst emission
    exact ⟨by assumption,rfl⟩
  · contradiction

theorem definitionEmission_run {env : LEnv} {before : LS} {op : Op} {emission : Emission}
    (member : emission ∈ definitionEmission env before op) : emission.Run env := by
  unfold definitionEmission at member
  split at member
  · have same := List.mem_singleton.mp member
    subst emission
    refine ⟨by assumption,?_⟩
    change emitDef op env before = (before.vals.size,(emitDef op env before).2)
    cases current : before.cur with
    | none => simp [current] at *
    | some sourceBlock => rw [emitDef_run _ _ current]
  · contradiction

theorem initializationEmissions_run {env : LEnv} {bindings : List (SlotId × ValueId × OriginId)}
    {before : LS} {emission : Emission}
    (member : emission ∈ initializationEmissions env bindings before) : emission.Run env := by
  induction bindings generalizing before with
  | nil => contradiction
  | cons binding rest ih =>
    rcases List.mem_append.mp member with head | tail
    · exact effectEmission_run head
    · exact ih tail

theorem Fragment.emission_run {fragment : Fragment} {env : LEnv} {before : LS} {emission : Emission}
    (member : emission ∈ fragment.emissions env before) : emission.Run env := by
  cases fragment with
  | expression syntaxExpr =>
    cases syntaxExpr <;> simp only [Fragment.emissions] at member
    all_goals first | exact definitionEmission_run member | contradiction
  | statement loop sourceStatement =>
    cases sourceStatement <;> simp only [Fragment.emissions] at member
    all_goals first | exact effectEmission_run member | contradiction
  | block loop bindings want sourceBlock =>
    cases sourceBlock
    exact initializationEmissions_run member
  | _ => simp [Fragment.emissions] at member

theorem InstructionSource.underParent {root child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} {instruction : Inst}
    (row : root.child? env before index = some (child,start))
    (source : InstructionSource child env start instruction) :
    InstructionSource root env before instruction := by
  intro writer
  obtain ⟨path,fragment,initial,emission,located,member,same⟩ := source writer
  refine ⟨index :: path,fragment,initial,emission,?_,member,same⟩
  simp only [SourceLoweringAt,Fragment.at?,row,Option.bind_some]
  exact located

#print axioms Fragment.emission_run
#print axioms InstructionSource.underParent

end Goose.Lower.Validation.SourceReplacementWriterLedger
