import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpExpr_read_contract {env : PEnv} {place : Place} {initial before after : RState}
    {placeRoots sourceRoots : List RootRef}
    (placeReplay : rpPlace env place initial = .ok (placeRoots, before))
    (source : rpExpr env (.read place) initial = .ok (sourceRoots, after)) :
    readRoots env place { before with eff := {
        before.eff with reads := addTargets before.eff.reads (rootsTargets placeRoots) } } =
        .ok (sourceRoots, after) ∧
      after.eff = { before.eff with reads := addTargets before.eff.reads (rootsTargets placeRoots) } := by
  simp only [rpExpr] at source
  obtain ⟨_, _, first, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [placeReplay] at first
  cases first
  obtain ⟨_, readState, reading, rootReplay⟩ := (st_bind_ok _ _ _ _).mp tail
  unfold addReads addRoots at reading
  have readEq : readState = { before with eff := {
      before.eff with reads := addTargets before.eff.reads (rootsTargets placeRoots) } } :=
    congrArg Prod.snd ((st_modify_ok _ _ _).mp reading)
  subst readState
  exact ⟨rootReplay, congrArg RState.eff (readRoots_ok env place _ _ rootReplay).1⟩

end Goose.Lower.Validation.SummaryPreservation
