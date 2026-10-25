import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlActions

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

structure ActiveReturnCheckpoint (setup : B (Option β)) (child : β → B α)
    (env : LEnv) (initial : LS) (values : List ValueId) (origin : Option OriginId) where
  argument : β
  before : LS
  value : α
  after : LS
  setupRun : setup env initial = (some argument, before)
  childRun : child argument env before = (value, after)
  member : .term (.ret values origin) ∈ after.insts

theorem ActiveReturnCheckpoint.roots_bounded {setup : B (Option β)} {child : β → B α}
    {env : LEnv} {initial : LS} {value : ValueId} {origin : Option OriginId}
    {target : List RootRef} {upper finalUpper : Prov} {scopeCount : Nat}
    (checkpoint : ActiveReturnCheckpoint setup child env initial [value] origin)
    (ledger : BuilderReturnsBound upper target checkpoint.after)
    (symbols : checkpoint.after.SymbolWF env scopeCount)
    (size : upper.vals.size = checkpoint.after.vals.size)
    (retained : ∀ index, index < upper.vals.size → rootsAt finalUpper.vals index = rootsAt upper.vals index) :
    ∀ root ∈ rootsAt finalUpper.vals value, root ∈ target := by
  have bound := (symbols.instructions _ checkpoint.member).uses value (by simp [Inst.uses, Term.uses])
  intro root member
  rw [retained value (by simpa only [size] using bound)] at member
  exact ledger value origin checkpoint.member root member

namespace ReturnLedgerControl

theorem optional_origin {setup : B (Option β)} {child : β → B α} {suffix : β → α → B Unit}
    {env : LEnv} {initial final : LS} {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (setupFrame : ReturnFrameRun setup) (suffixFrame : ∀ argument value, ReturnFrameRun (suffix argument value))
    (run : (do let selected ← setup; match selected with
      | none => pure ()
      | some argument => do let value ← child argument; suffix argument value) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨
      Nonempty (ActiveReturnCheckpoint setup child env initial values origin) := by
  obtain ⟨selected, before, setupRun, tail⟩ := bind_eq.mp run
  cases selected with
  | none =>
    obtain ⟨rfl, rfl⟩ := pure_eq.mp tail
    exact Or.inl (setupFrame env initial none before setupRun values origin member)
  | some argument =>
    obtain ⟨value, after, childRun, suffixRun⟩ := bind_eq.mp tail
    exact Or.inr ⟨⟨argument, before, value, after, setupRun, childRun,
      suffixFrame argument value env after result final suffixRun values origin member⟩⟩

theorem optional_origin_none {setup : B (Option β)} {child : β → B α} {suffix : β → α → B Unit}
    {env : LEnv} {initial final : LS} {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (noneFrame : ∀ before, setup env initial = (none, before) → ReturnMembershipFrame initial before)
    (suffixFrame : ∀ argument value, ReturnFrameRun (suffix argument value))
    (run : (do let selected ← setup; match selected with
      | none => pure ()
      | some argument => do let value ← child argument; suffix argument value) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨
      Nonempty (ActiveReturnCheckpoint setup child env initial values origin) := by
  obtain ⟨selected, before, setupRun, tail⟩ := bind_eq.mp run
  cases selected with
  | none =>
    obtain ⟨rfl, rfl⟩ := pure_eq.mp tail
    exact Or.inl (noneFrame before setupRun values origin member)
  | some argument =>
    obtain ⟨value, after, childRun, suffixRun⟩ := bind_eq.mp tail
    exact Or.inr ⟨⟨argument, before, value, after, setupRun, childRun,
      suffixFrame argument value env after result final suffixRun values origin member⟩⟩

end ReturnLedgerControl
end Goose.Lower.Validation.SummaryPreservation
