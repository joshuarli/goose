import Goose.Lower.Validation.SummaryPreservationReplayControlActions

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def LoopReplayBounds (loop : Option LoopCtx) (scopeCount : Nat) (state : LS) : Prop :=
  match loop with
  | none => True
  | some context =>
    (match context.cont with
      | .jump _ => True
      | .next _ _ counter => counter < state.vals.size) ∧
    ∀ scope ∈ state.stack.take (state.stack.length - context.depth), scope < scopeCount

namespace LoopReplayBounds

theorem mono {loop : Option LoopCtx} {scopeCount : Nat} {before after : LS}
    (bounded : LoopReplayBounds loop scopeCount before) (advance : before.Adv after) :
    LoopReplayBounds loop scopeCount after := by
  cases loop with
  | none => trivial
  | some context =>
    obtain ⟨counter, scopes⟩ := bounded
    refine ⟨?_, ?_⟩
    · cases continuation : context.cont with
      | jump header => trivial
      | next header type value =>
        simp only [continuation] at counter ⊢
        exact Nat.lt_of_lt_of_le counter advance.vals
    · simpa only [advance.stack] using scopes

theorem pushScope {loop : Option LoopCtx} {scopeCount scope : Nat} {state : LS}
    (bounded : LoopReplayBounds loop scopeCount state) (scopeBound : scope < scopeCount) :
    LoopReplayBounds loop scopeCount { state with stack := scope :: state.stack } := by
  cases loop with
  | none => trivial
  | some context =>
    obtain ⟨counter, scopes⟩ := bounded
    refine ⟨counter, ?_⟩
    by_cases depth : context.depth ≤ state.stack.length
    · have length : (scope :: state.stack).length - context.depth =
          state.stack.length - context.depth + 1 := by simp only [List.length_cons]; omega
      simp only [length, List.take_succ_cons, List.mem_cons]
      intro entered member
      rcases member with rfl | old
      · exact scopeBound
      · exact scopes entered old
    · have length : (scope :: state.stack).length - context.depth = 0 := by
        simp only [List.length_cons]; omega
      simp only [length, List.take_zero, List.not_mem_nil, false_implies, implies_true]

end LoopReplayBounds

namespace ReplayBuilder

theorem leaveToScopes {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {state : LS} {upper : Prov}
    (ready : ReplayBuilder module results vt func target le scopeCount slots state upper)
    (depth : Nat)
    (bounds : ∀ scope ∈ state.stack.take (state.stack.length - depth), scope < scopeCount) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.leaveTo depth le state).2 upper := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using
    ready.leaveAll (state.stack.take (state.stack.length - depth)) bounds

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
