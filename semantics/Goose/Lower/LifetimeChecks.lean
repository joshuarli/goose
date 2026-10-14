import Goose.Lower.Lifetime

namespace Goose.Lower.LifetimeChecks

open Goose.Core Goose.GIR

def physicalSlots : Array Val := #[.int .i64 9]

def clearedOwner : Store :=
  Store.empty.introduce (.global 0) (.limited (.int .i64) 1 physicalSlots 0)

def sampledView : ViewVal := ⟨⟨.global 0, []⟩, 0, 1, false⟩

def sampledFrame : GIR.Frame :=
  (⟨0, [], {}, 0⟩ : GIR.Frame).set 0 (.view sampledView)

def ownerAlias : RetainedAlias :=
  ⟨.ref .mutable (.limited (.int .i64) 1), [.global 0], .operand []⟩

theorem retained_limited_sample (m : Core.Module) (world : Core.Sound.World) (env : Env) :
    LimitedRunAliasAt m world env clearedOwner sampledFrame 0 ownerAlias := by
  have hread : clearedOwner.read sampledView.loc =
      .ok (.limited (.int .i64) 1 physicalSlots 0) := by
    simp [clearedOwner, sampledView, Store.read, Store.introduce, Store.empty, Val.get?]
  have hflat : Goose.Proofs.Memory.FlatTy (.limited (.int .i64) 1)
      (.limited (.int .i64) 1 physicalSlots 0) := by
    simp only [Goose.Proofs.Memory.FlatTy, Nat.zero_le, true_and]
    intro i v hv
    cases i with
    | zero => simp [physicalSlots] at hv; subst v; rfl
    | succ i => simp [physicalSlots] at hv
  refine ⟨sampledView, .mutable, .int .i64, 1, Frame.set_get _ _ _, rfl, ?_, ?_⟩
  · constructor
    · refine ⟨sampledView.loc, rfl, Or.inl ⟨rfl, Or.inl ⟨_, hread, hflat⟩, ?_⟩⟩
      intro _
      rfl
    · intro root htarget
      change sampledView.loc.root = root at htarget
      exact ⟨.global 0, by simp [ownerAlias], htarget.symm⟩
  · exact ⟨.limited (.int .i64) 1 physicalSlots 0, physicalSlots, hread, rfl,
      by decide, Or.inr (Or.inr (Or.inr ⟨1, hflat⟩))⟩

theorem cleared_sample_read (m : Core.Module) (world : Core.Sound.World) (env : Env) :
    ∃ values, (getView sampledFrame 0 >>= readRun)
      ⟨clearedOwner, "", 0, 0⟩ = .ok values ⟨clearedOwner, "", 0, 0⟩ :=
  (retained_limited_sample m world env).read_safe

#guard match (getView sampledFrame 0 >>= readRun) ⟨clearedOwner, "", 0, 0⟩ with
  | .ok values _ => values.size == 1 && (match values[0]? with
    | some (Val.int IntTy.i64 9) => true
    | _ => false)
  | .stop _ _ => false

def removedSample : St :=
  ⟨Store.empty.introduce (.global 0) (.resizable (.int .i64) #[]), "", 0, 0⟩

theorem removed_sample_faults :
    (getView sampledFrame 0 >>= readRun) removedSample =
      .stop (.fault .pathRange) removedSample := by
  simp [sampledFrame, sampledView, getView, getCell, Frame.set, getVal,
    readRun, removedSample, readLoc, Store.introduce, Store.empty, Store.read,
    Val.get?, bind_apply, pure_apply, fault, M.stop]

theorem removed_sample_not_retained (m : Core.Module) (world : Core.Sound.World) (env : Env)
    (alias : RetainedAlias) :
    ¬ RunAliasAt m world env removedSample.store sampledFrame 0 alias := by
  intro h
  obtain ⟨values, hread⟩ := h.read_safe
  rw [removed_sample_faults] at hread
  cases hread

end Goose.Lower.LifetimeChecks
