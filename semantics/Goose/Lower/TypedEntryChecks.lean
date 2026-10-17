import Goose.Lower.TypedEntry
import Goose.Lower.ModuleFuel
import Goose.Lower.TypedGlobalChecks
import Goose.Lower.FinalStatements
import Goose.Lower.TypedLists
import Goose.Lower.TypedTransfers

namespace Goose.Lower.TypedEntryChecks

open Goose.Core Goose.GIR

private theorem readGlobal_simulation (fuel : Nat) (cfg : Cfg) (id : GlobalId) :
    TypedExprClaim fuel cfg [] (.read (.global id)) := by
  cases fuel with
  | zero => exact typedExprClaim_zero _ _ _
  | succ fuel => exact typedExprClaim_read (typedPlaceClaim_global fuel cfg [] id)

theorem body_simulation (fuel : Nat) (cfg : Cfg) :
    TypedBlockLoopSimulation fuel cfg [] none [] [] false TypedGlobalChecks.implementation.body := by
  cases fuel with
  | zero => exact typedBlockLoopSimulation_zero _ _ _ _ _ _ _
  | succ fuel =>
    apply typedBlockLoopSimulation_succ
    · cases fuel with
      | zero => exact typedStatementsLoopSimulation_zero _ _ _ _
      | succ fuel =>
        apply typedStatementsLoopSimulation_cons
        · cases fuel with
          | zero => exact typedStatementLoopSimulation_zero _ _ _ _
          | succ fuel => exact typedStatementLoopSimulation_assert (readGlobal_simulation fuel cfg 1)
        · exact typedStatementsLoopSimulation_nil fuel cfg [] none
    · trivial

theorem module_simulation (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (TypedGlobalChecks.module artifact) = .ok ()) :
    EventualM (Core.runModule 8 ⟨profile, TypedGlobalChecks.module artifact⟩)
      (fun fuel => GIR.runModule fuel ⟨profile, lower (TypedGlobalChecks.module artifact)⟩) St.initial := by
  apply typedModule_simulation_succ 7 accepted
  · intro id found present
    cases id with
    | zero =>
      have foundEq : found = TypedGlobalChecks.global := by
        simpa [TypedGlobalChecks.module] using present.symm
      subst found
      exact typedExprClaim_bool 8 _ _ true
    | succ id =>
      cases id with
      | zero =>
        have foundEq : found = TypedGlobalChecks.dependent := by
          simpa [TypedGlobalChecks.module] using present.symm
        subst found
        exact typedExprClaim_read (typedPlaceClaim_global 7 _ _ 0)
      | succ id => simp [TypedGlobalChecks.module] at present
  · intro context impl contextAt implAt
    have contextEq : context = ⟨0, "main", [], [], []⟩ := by
      simpa [TypedGlobalChecks.module] using contextAt.symm
    subst context
    have implEq : impl = TypedGlobalChecks.implementation := by
      simpa [TypedGlobalChecks.module] using implAt.symm
    subst impl
    exact body_simulation 7 _

theorem completed_module_no_fault (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (TypedGlobalChecks.module artifact) = .ok ()) (after : St)
    (completed : Core.runModule 8 ⟨profile, TypedGlobalChecks.module artifact⟩ St.initial = .ok () after) :
    ∀ fuel kind failed, GIR.runModule fuel ⟨profile, lower (TypedGlobalChecks.module artifact)⟩
      St.initial ≠ .stop (.fault kind) failed :=
  (module_simulation artifact profile accepted).module_no_fault_of_ok completed

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 8 profile (TypedGlobalChecks.module artifact),
        GIR.run 60 profile (lower (TypedGlobalChecks.module artifact)) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

end Goose.Lower.TypedEntryChecks
