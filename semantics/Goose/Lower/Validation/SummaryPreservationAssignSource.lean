import Goose.Lower.Validation.SummaryPreservationStores

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_assign_contract {env : PEnv} {place : Place} {expression : Expr} {org : OriginId}
    {placeRoots storedRoots : List RootRef} {initial placeState before after : RState}
    (placeReplay : rpPlace env place initial = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (storedRoots, before))
    (source : rpStmt env (.assign place expression org) initial = .ok ((), after)) :
    checkStore env place storedRoots = .ok () ∧
      after.eff = { before.eff with
        writes := addTargets before.eff.writes (rootsTargets placeRoots)
        rebinds := addTargets before.eff.rebinds (storeRebinds env place) } := by
  simp only [rpStmt] at source
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [placeReplay] at run
  cases run
  obtain ⟨_, _, run, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  rw [valueReplay] at run
  cases run
  obtain ⟨_, checkedState, checking, tail⟩ := (st_bind_ok _ _ _ _).mp tail
  obtain ⟨checked, stateEq⟩ := (liftV_ok _ _ _).mp checking
  have sameState : checkedState = before := stateEq
  subst checkedState
  obtain ⟨_, writeState, writing, rebinding⟩ := (st_bind_ok _ _ _ _).mp tail
  have writeEq : writeState = { before with eff := { before.eff with
      writes := addTargets before.eff.writes (rootsTargets placeRoots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp writing)
  have rebindEq : after.eff = { writeState.eff with
      rebinds := addTargets writeState.eff.rebinds (storeRebinds env place) } :=
    congrArg (fun pair => pair.2.eff) ((st_modify_ok _ _ _).mp rebinding)
  exact ⟨checked, by simpa only [writeEq] using rebindEq⟩

end Goose.Lower.Validation.SummaryPreservation
