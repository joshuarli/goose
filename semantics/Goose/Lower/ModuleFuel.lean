import Goose.Lower.Eventual

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem initGlobals_fuel_mono (n k : Nat) (enough : n ≤ k) (cfg : GCfg) :
    ∀ globals, MonoM (GIR.initGlobals n cfg globals) (GIR.initGlobals k cfg globals) := by
  intro globals
  induction globals with
  | nil => exact MonoM.refl _
  | cons global rest previous =>
    simp only [GIR.initGlobals]
    refine MonoM.bind (MonoM.refl _) fun initializer => ?_
    refine MonoM.bind (enterFn_fuel_mono n k enough cfg 0 initializer []) fun value => ?_
    exact MonoM.bind (MonoM.refl _) fun _ => previous

theorem runModule_fuel_mono (n k : Nat) (enough : n ≤ k) (cfg : GCfg) :
    MonoM (GIR.runModule n cfg) (GIR.runModule k cfg) := by
  unfold GIR.runModule
  refine MonoM.bind (initGlobals_fuel_mono n k enough cfg _) fun _ => ?_
  exact MonoM.bind (callFn_fuel_mono n k enough cfg 0 cfg.mod.entry [])
    (fun _ => MonoM.refl _)

theorem EventualM.module_no_fault_of_ok {source : M Unit} {cfg : GCfg} {state : St}
    {value : Unit} {after : St}
    (h : EventualM source (fun fuel => GIR.runModule fuel cfg) state)
    (done : source state = .ok value after) :
    ∀ fuel reason failed, GIR.runModule fuel cfg state ≠ .stop (.fault reason) failed := by
  obtain ⟨K, completed⟩ := h.1 value after done
  dsimp only at completed
  intro fuel reason failed fault
  have monotone := runModule_fuel_mono fuel (max fuel K) (Nat.le_max_left _ _) cfg state
  have faultAtMax := (monotone.2 (.fault reason) failed fault).resolve_left (by simp [isTimeout])
  rw [completed (max fuel K) (Nat.le_max_right _ _)] at faultAtMax
  cases faultAtMax

theorem EventualM.module_no_fault_of_final {source : M Unit} {cfg : GCfg} {state : St}
    {reason : Stop} {after : St}
    (h : EventualM source (fun fuel => GIR.runModule fuel cfg) state)
    (done : source state = .stop reason after) (final : IsFinal reason) :
    ∀ fuel kind failed, GIR.runModule fuel cfg state ≠ .stop (.fault kind) failed := by
  obtain ⟨K, completed⟩ := h.2 reason after done final
  dsimp only at completed
  intro fuel kind failed fault
  have monotone := runModule_fuel_mono fuel (max fuel K) (Nat.le_max_left _ _) cfg state
  have faultAtMax := (monotone.2 (.fault kind) failed fault).resolve_left (by simp [isTimeout])
  rw [completed (max fuel K) (Nat.le_max_right _ _)] at faultAtMax
  obtain ⟨equal, _⟩ := Res.stop.inj faultAtMax
  subst reason
  exact final

end Goose.Lower
