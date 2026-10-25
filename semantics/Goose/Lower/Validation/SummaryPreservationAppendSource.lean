import Goose.Lower.Validation.SummaryPreservationMutationOwnerEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_append_effect {env : PEnv} {owner : Place} {view : View} {org : OriginId}
    {roots viewRoots : List RootRef} {initial ownerState before after : RState} {limited : Bool}
    (ownerReplay : rpPlace env owner initial = .ok (roots, ownerState))
    (viewReplay : rpView env view ownerState = .ok (viewRoots, before))
    (limitedRun : env.limitedOwner owner = .ok limited)
    (source : rpStmt env (.append owner view org) initial = .ok ((), after)) :
    after.eff = if env.mod.profile == .shrink then
      { before.eff with
        reads := addTargets before.eff.reads (rootsTargets viewRoots)
        grows := addTargets before.eff.grows (rootsTargets roots)
        writes := addTargets before.eff.writes (rootsTargets roots)
        aborts := before.eff.aborts || limited }
      else { before.eff with
        reads := addTargets before.eff.reads (rootsTargets viewRoots)
        grows := addTargets before.eff.grows (rootsTargets roots) } := by
  simp only [rpStmt] at source
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [ownerReplay] at run
  cases run
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  rw [viewReplay] at run
  cases run
  obtain ⟨_, readState, reading, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have readEq : readState = { before with eff := { before.eff with
      reads := addTargets before.eff.reads (rootsTargets viewRoots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp reading)
  obtain ⟨_, growState, growing, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have growEq : growState = { readState with eff := { readState.eff with
      grows := addTargets readState.eff.grows (rootsTargets roots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp growing)
  by_cases shrink : (env.mod.profile == .shrink) = true
  · simp only [shrink, ite_true] at tail ⊢
    obtain ⟨_, writeState, writing, tail⟩ := (st_bind_ok _ _ _ _).mp tail
    have writeEq : writeState = { growState with eff := { growState.eff with
        writes := addTargets growState.eff.writes (rootsTargets roots) } } :=
      congrArg Prod.snd ((st_modify_ok _ _ _).mp writing)
    obtain ⟨returned, checkedState, checking, finish⟩ := (st_bind_ok _ _ _ _).mp tail
    obtain ⟨checked, stateEq⟩ := (liftV_ok _ _ _).mp checking
    rw [limitedRun] at checked
    cases checked
    have sameState : checkedState = writeState := stateEq
    subst checkedState
    cases returned with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at finish
      have effEq := congrArg (fun pair => pair.2.eff) ((st_pure_ok _ _ _).mp finish)
      simpa only [writeEq, growEq, readEq, Bool.or_false] using effEq
    | true =>
      simp only [ite_true] at finish
      have effEq := congrArg (fun pair => pair.2.eff) ((st_modify_ok _ _ _).mp finish)
      simpa only [writeEq, growEq, readEq, Bool.or_true] using effEq
  · simp only [shrink, Bool.false_eq_true, ite_false] at tail ⊢
    have effEq := congrArg (fun pair => pair.2.eff) ((st_pure_ok _ _ _).mp tail)
    simpa only [growEq, readEq] using effEq

end Goose.Lower.Validation.SummaryPreservation
