import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpExpr_call_contract {env : PEnv} {callee : ContextId} {args : List Arg}
    {origin : OriginId} {initial before after : RState}
    {argumentRoots : List (List RootRef)} {sourceRoots : List RootRef}
    (arguments : rpArgs env args initial = .ok (argumentRoots, before))
    (source : rpExpr env (.call callee args origin) initial = .ok (sourceRoots, after)) :
    checkContents env callee args argumentRoots = .ok () ∧
      rpCall env callee argumentRoots before = .ok (sourceRoots, after) := by
  simp only [rpExpr] at source
  obtain ⟨_, _, first, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [arguments] at first
  cases first
  obtain ⟨value, intermediate, checking, called⟩ := (st_bind_ok _ _ _ _).mp tail
  have checked := (liftV_ok _ _ _).mp checking
  obtain ⟨contents, stateEq⟩ := checked
  cases value
  change intermediate = before at stateEq
  subst intermediate
  exact ⟨contents, called⟩

end Goose.Lower.Validation.SummaryPreservation
