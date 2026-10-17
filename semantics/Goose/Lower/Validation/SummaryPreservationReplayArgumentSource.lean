import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound

def ArgumentTyping (env : TEnv) (argument : Arg) (start finish : Nat) : Prop :=
  match argument with
  | .byVal expression => ∃ type, tyExpr env expression start = .ok (type, finish)
  | .byRef _ place => ∃ info, tyPlace env place start = .ok (info, finish)

theorem tyArgs_cons_children {env : TEnv} {callee : Impl} {parameter : Param}
    {parameters : List Param} {argument : Arg} {arguments : List Arg} {start finish : Nat}
    (source : tyArgs env callee (parameter :: parameters) (argument :: arguments) start = .ok ((), finish)) :
    ∃ middle, ArgumentTyping env argument start middle ∧
      tyArgs env callee parameters arguments middle = .ok ((), finish) := by
  cases row : callee.vars[parameter.var]? with
  | none =>
    cases argument <;> simp only [tyArgs, row] at source
    all_goals inv at source
  | some localVar =>
    cases argument with
    | byVal expression =>
      simp only [tyArgs, row] at source
      inv at source
      obtain ⟨_mode, type, middle, typed, _passable, remaining⟩ := source
      exact ⟨middle, ⟨type, typed⟩, remaining⟩
    | byRef mutability place =>
      simp only [tyArgs, row] at source
      inv at source
      obtain ⟨_mode, type, binding, contents, middle, typed, _reference, _target, branches⟩ := source
      rcases branches with ⟨_mutable, _writable, _passable, remaining⟩ | ⟨_readonly, _passable, remaining⟩
      all_goals exact ⟨middle, ⟨⟨type, binding, contents⟩, typed⟩, remaining⟩

end Goose.Lower.Validation.SummaryPreservation
