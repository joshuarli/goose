import Goose.Lower.Validation.SummaryPreservationReturnLedger

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

structure ReturnCheckpoint (head : B β) (child : β → B α) (env : LEnv) (initial : LS)
    (values : List ValueId) (origin : Option OriginId) where
  argument : β
  before : LS
  value : α
  after : LS
  prefixRun : head env initial = (argument, before)
  childRun : child argument env before = (value, after)
  member : .term (.ret values origin) ∈ after.insts

namespace ReturnCheckpoint

theorem of_suffix {head : B β} {child : β → B α} {suffix : β → α → B γ}
    {env : LEnv} {initial final : LS} {result : γ} {values : List ValueId} {origin : Option OriginId}
    (frames : ∀ argument value, ReturnFrameRun (suffix argument value))
    (run : (do let argument ← head; let value ← child argument; suffix argument value) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    Nonempty (ReturnCheckpoint head child env initial values origin) := by
  obtain ⟨argument, before, prefixRun, tail⟩ := bind_eq.mp run
  obtain ⟨value, after, childRun, suffixRun⟩ := bind_eq.mp tail
  exact ⟨⟨argument, before, value, after, prefixRun, childRun,
    frames argument value env after result final suffixRun values origin member⟩⟩

def prepend {head : B β} {child : β → B α} {leading : B γ}
    {env : LEnv} {initial middle : LS} {headValue : γ} {values : List ValueId} {origin : Option OriginId}
    (run : leading env initial = (headValue, middle))
    (checkpoint : ReturnCheckpoint head child env middle values origin) :
    ReturnCheckpoint (leading >>= fun _ => head) child env initial values origin :=
  { checkpoint with prefixRun := by simpa only [bind_run, run] using checkpoint.prefixRun }

theorem roots_bounded {head : B β} {child : β → B α} {env : LEnv} {initial : LS}
    {value : ValueId} {origin : Option OriginId} {target : List RootRef} {upper finalUpper : Prov}
    {scopeCount : Nat} (checkpoint : ReturnCheckpoint head child env initial [value] origin)
    (ledger : BuilderReturnsBound upper target checkpoint.after)
    (symbols : checkpoint.after.SymbolWF env scopeCount)
    (size : upper.vals.size = checkpoint.after.vals.size)
    (retained : ∀ index, index < upper.vals.size → rootsAt finalUpper.vals index = rootsAt upper.vals index) :
    ∀ root ∈ rootsAt finalUpper.vals value, root ∈ target := by
  have bound := (symbols.instructions _ checkpoint.member).uses value (by simp [Inst.uses, Term.uses])
  intro root member
  rw [retained value (by simpa only [size] using bound)] at member
  exact ledger value origin checkpoint.member root member

end ReturnCheckpoint

namespace ReturnLedgerControl

theorem frame (action : B α) (absent : ∀ avoid, ReturnFrames.ReturnAbsentRun (avoid := avoid) action) :
    ReturnFrameRun action := ReturnFrameRun.of_absence absent

theorem frame_bind {first : B α} {next : α → B β}
    (head : ReturnFrameRun first) (tail : ∀ value, ReturnFrameRun (next value)) : ReturnFrameRun (first >>= next) := by
  intro env before result after run
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  exact (head env before value middle firstRun).trans (tail value env middle result after nextRun)

def loopPrefix (condition : ValueId) : B (Nat × BlockId) := do
  let state ← get
  let (body, exit) ← fork condition
  setCur (some body)
  pure (state.stack.length, exit)

theorem loopBody_origin {condition : ValueId} {body : Nat → BlockId → B ValueId} {back : B Unit}
    {env : LEnv} {initial final : LS} {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (backFrame : ReturnFrameRun back)
    (run : loopBody condition body back env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    Nonempty (ReturnCheckpoint (loopPrefix condition) (fun pair => body pair.1 pair.2) env initial values origin) := by
  exact ReturnCheckpoint.of_suffix (head := loopPrefix condition)
    (child := fun pair => body pair.1 pair.2)
    (suffix := fun pair _ => do back; setCur (some pair.2))
    (fun pair _ => frame_bind backFrame (fun _ => frame _ (fun _ => ReturnFrames.returnAbsent_setCur _)))
    (by simpa only [loopBody, loopPrefix, bind_run, pure_run] using run) member

end ReturnLedgerControl
end Goose.Lower.Validation.SummaryPreservation
