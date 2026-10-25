import Goose.Lower.Validation.CfgSourceDominanceControl
import Goose.Lower.Validation.DenseDefinitions
import Goose.Lower.Validation.CfgOpenTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem BuilderImportedSSA.patchBrs {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (target : BlockId)
    (incoming : List (BlockId × ValueId)) (env : LEnv)
    (operands : ∀ pair ∈ incoming, BuilderAvailable state imports pair.1 pair.2)
    (transport : ∀ pair ∈ incoming, ∀ value ∈ imports target,
      BuilderAvailable state imports pair.1 value) :
    BuilderImportedSSA (patchBrs target incoming env state).2 imports := by
  induction incoming generalizing state with
  | nil => exact certificate
  | cons pair rest ih =>
    simp only [Goose.Lower.patchBrs, bind_run]
    have one := certificate.patchTerm pair.1 (.br target [pair.2]) env
      (by intro value member; have same : value = pair.2 := by simpa [Term.uses] using member
          exact same.symm ▸ operands pair (by simp))
      (by intro destination member; have same : destination = target := by simpa [Term.successors] using member
          subst destination; exact transport pair (by simp))
    have extension : state.Ext (Goose.Lower.patchTerm pair.1 (.br target [pair.2]) env state).2 := by
      rw [patchTerm_run]
      exact (LS.Ext.refl state).modify (appends_push _) pair.1
    apply ih one
    · intro next member
      exact (operands next (by simp [member])).of_ext extension (fun _ _ => rfl)
    · intro next member value imported
      exact (transport next (by simp [member]) value imported).of_ext extension (fun _ _ => rfl)

theorem BuilderImportedSSA.patchBrs0 {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (target : BlockId)
    (incoming : List BlockId) (env : LEnv)
    (transport : ∀ source ∈ incoming, ∀ value ∈ imports target,
      BuilderAvailable state imports source value) :
    BuilderImportedSSA (patchBrs0 target incoming env state).2 imports := by
  induction incoming generalizing state with
  | nil => exact certificate
  | cons block rest ih =>
    simp only [Goose.Lower.patchBrs0, bind_run]
    have one := certificate.patchTerm block (.br target []) env
      (by simp [Term.uses])
      (by intro destination member; have same : destination = target := by simpa [Term.successors] using member
          subst destination; exact transport block (by simp))
    have extension : state.Ext (Goose.Lower.patchTerm block (.br target []) env state).2 := by
      rw [patchTerm_run]
      exact (LS.Ext.refl state).modify (appends_push _) block
    apply ih one
    intro next member value imported
    exact (transport next (by simp [member]) value imported).of_ext extension (fun _ _ => rfl)

theorem targets_patchBrs (target : BlockId) (incoming : List (BlockId × ValueId))
    (env : LEnv) (state : LS) (bounded : TargetsBounded state) (targetBound : target < state.blocks.size) :
    TargetsBounded (patchBrs target incoming env state).2 := by
  induction incoming generalizing state with
  | nil => exact bounded
  | cons pair rest ih =>
    simp only [patchBrs, bind_run]
    apply ih
    · exact bounded.patchTerm pair.1 (.br target [pair.2])
        (by intro destination member
            have same : destination = target := by simpa [Term.successors] using member
            exact same.symm ▸ targetBound) env
    · simpa only [patchTerm_run, Array.size_modify] using targetBound

theorem targets_patchBrs0 (target : BlockId) (incoming : List BlockId)
    (env : LEnv) (state : LS) (bounded : TargetsBounded state) (targetBound : target < state.blocks.size) :
    TargetsBounded (patchBrs0 target incoming env state).2 := by
  induction incoming generalizing state with
  | nil => exact bounded
  | cons block rest ih =>
    simp only [patchBrs0, bind_run]
    apply ih
    · exact bounded.patchTerm block (.br target [])
        (by intro destination member
            have same : destination = target := by simpa [Term.successors] using member
            exact same.symm ▸ targetBound) env
    · simpa only [patchTerm_run, Array.size_modify] using targetBound

theorem ssa_patchBrs_values (target : BlockId) (incoming : List (BlockId × ValueId))
    (env : LEnv) (state : LS) : (patchBrs target incoming env state).2.vals = state.vals := by
  induction incoming generalizing state with
  | nil => rfl
  | cons pair rest ih => simpa only [patchBrs, bind_run, patchTerm_run] using (ih
      { state with blocks := state.blocks.modify pair.1 fun body =>
        { body with insts := body.insts.push (.term (.br target [pair.2])) } })

theorem ssa_patchBrs0_values (target : BlockId) (incoming : List BlockId)
    (env : LEnv) (state : LS) : (patchBrs0 target incoming env state).2.vals = state.vals := by
  induction incoming generalizing state with
  | nil => rfl
  | cons block rest ih => simpa only [patchBrs0, bind_run, patchTerm_run] using (ih
      { state with blocks := state.blocks.modify block fun body =>
        { body with insts := body.insts.push (.term (.br target [])) } })

end Goose.Lower.Validation
