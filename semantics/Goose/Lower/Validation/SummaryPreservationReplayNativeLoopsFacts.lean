import Goose.Lower.Validation.SummaryPreservationReplayLoopsRangeSource
import Goose.Lower.Validation.SummaryPreservationSourceBlockContracts
import Goose.Lower.Validation.SummaryPreservationEffectMonotonicity

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem native_loop_source_body_effect {env : PEnv} {body : Core.Block} {before after : RState}
    {roots : List RootRef} {range : Nat × Nat} {func : Func} {target : Core.Eff}
    (replayed : rpBlockValue env [] body before = .ok ((roots, range), after))
    (wholeEffect : EffectRefinement func after.eff target) : EffectRefinement func before.eff target :=
  (EffectTargetsBelow.refines ⟨(rpBlockValue_mono replayed).2,
    rpBlockValue_rebinds_mono replayed, rpBlockValue_flags_mono replayed⟩).trans wholeEffect

theorem native_while_replay {env : PEnv} {condition : Expr} {body : Core.Block} {origin : OriginId}
    {before after : RState}
    (source : rpStmt env (.while condition body origin) before = .ok ((), after)) :
    ∃ conditionRoots conditionState bodyRoots bodyRange,
      rpExpr env condition before = .ok (conditionRoots, conditionState) ∧
      rpBlockValue env [] body conditionState = .ok ((bodyRoots, bodyRange), after) := by
  simp only [rpStmt] at source
  obtain ⟨conditionRoots, conditionState, conditionReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨result, bodyState, bodyReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  have same := congrArg Prod.snd ((st_pure_ok _ _ _).mp source)
  dsimp only at same
  subst after
  exact ⟨conditionRoots, conditionState, result.1, result.2, conditionReplay, bodyReplay⟩

theorem native_range_replay {env : PEnv} {variableId : VarId} {low high : Expr} {body : Core.Block} {origin : OriginId}
    {before after : RState}
    (source : rpStmt env (.forRange variableId low high body origin) before = .ok ((), after)) :
    ∃ lowStart lowRoots lowState highRoots highState bodyRoots bodyRange,
      rpExpr env low lowStart = .ok (lowRoots, lowState) ∧
      rpExpr env high lowState = .ok (highRoots, highState) ∧
      rpBlockValue env [] body highState = .ok ((bodyRoots, bodyRange), after) := by
  simp only [rpStmt] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, lowStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨lowRoots, lowState, lowReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨highRoots, highState, highReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨result, bodyState, bodyReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  have same := ((liftV_ok _ _ _).mp source).2
  dsimp only at same
  subst after
  exact ⟨lowStart, lowRoots, lowState, highRoots, highState, result.1, result.2, lowReplay, highReplay, bodyReplay⟩

end Goose.Lower.Validation.SummaryPreservation
