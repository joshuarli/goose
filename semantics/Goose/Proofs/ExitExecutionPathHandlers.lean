import Goose.Proofs.ExitExecutionPathContext

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private def handlerEntered (rootFuel : Nat) (config : EvalConfig) : ExitLexicalFrame → Prop
  | .handler activation resultTypes origin =>
      ∃ fuel pre body initial implementation,
        ExitReached rootFuel config (.activation (fuel + 1) activation pre body origin) initial ∧
        config.module.impls[activation.implementation]? = some implementation ∧
        resultTypes = implementation.results.toList.map (·.ty)
  | _ => True

private theorem contextReached_forget {rootFuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {α : Type} {invocation : ExitInvocation α} {state : ExecutionState}
    (reached : ExitContextReached rootFuel config context invocation state) :
    ExitReached rootFuel config invocation state := by
  induction reached with
  | initial => exact .initial
  | call callerReached site frames previous => exact .call previous site

private def activationPositive (invocation : ExitInvocation α) : Prop :=
  match invocation with | .activation fuel .. => 0 < fuel | _ => True

private theorem activationSite_positive {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {callee : ExitInvocation β} {initial middle : ExecutionState}
    (site : ExitCallSite config caller initial callee middle) : activationPositive caller := by
  cases site
  all_goals try trivial
  case activationBody => exact Nat.zero_lt_succ _
  case values edge => cases edge <;> trivial
  case producer edge => cases edge <;> trivial
  case statements edge => cases edge <;> trivial

private theorem frames_handlers_entered {rootFuel : Nat} {config : EvalConfig} {α : Type}
    {caller : ExitInvocation α} {β : Type} {callee : ExitInvocation β} {initial middle : ExecutionState} {outer inner : List ExitLexicalFrame}
    (reached : ExitReached rootFuel config caller initial)
    (site : ExitCallSite config caller initial callee middle)
    (frames : caller.frames config initial middle outer inner)
    (previous : ∀ frame ∈ outer, handlerEntered rootFuel config frame) :
    ∀ frame ∈ inner, handlerEntered rootFuel config frame := by
  cases caller
  all_goals dsimp only [ExitInvocation.frames] at frames
  all_goals first | (subst inner; exact previous) | skip
  case activation fuel environment pre body origin =>
    obtain ⟨implementation, lookup, rfl⟩ := frames
    intro frame member
    rcases List.mem_cons.mp member with same | member
    · subst frame
      have positive := activationSite_positive site
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ positive)
      | succ fuel => exact ⟨fuel, pre, body, initial, implementation, reached, lookup, rfl⟩
    · exact previous frame member
  case activationScope fuel environment pre body =>
    cases body
    dsimp only at frames
    subst inner
    simpa only [List.forall_mem_cons, handlerEntered, true_and] using previous
  case resultScope fuel environment pre channels body =>
    cases body
    dsimp only at frames
    subst inner
    simpa only [List.forall_mem_cons, handlerEntered, true_and] using previous
  case block fuel environment pre channels body =>
    cases body
    dsimp only at frames
    subst inner
    simpa only [List.forall_mem_cons, handlerEntered, true_and] using previous
  case produce fuel environment incoming expression =>
    cases expression <;> try dsimp only at frames
    all_goals first
      | (subst inner; exact previous)
      | (rcases frames with ⟨_, _, _, _, rfl⟩
         simpa only [List.forall_mem_cons, handlerEntered, true_and] using previous)
  case build fuel environment incoming expression =>
    rcases frames with ⟨_, _, _, rfl⟩
    cases expression <;> simpa only [List.nil_append, List.cons_append, List.forall_mem_cons, handlerEntered, true_and] using previous
  case loop fuel environment pre body =>
    subst inner
    simpa only [List.forall_mem_cons, handlerEntered, true_and] using previous
  case completionTail fuel environment channels expression =>
    rcases frames with ⟨_, _, rfl⟩
    simpa only [List.forall_mem_cons, handlerEntered, true_and] using previous
  case statement fuel environment statement =>
    cases statement <;> try dsimp only at frames
    all_goals first
      | (subst inner; exact previous)
      | (rcases frames with ⟨_, _, rfl⟩
         simpa only [List.forall_mem_cons, handlerEntered, true_and] using previous)
      | skip
    case ret expression origin =>
      cases expression <;> try dsimp only at frames
      all_goals first
        | (subst inner; exact previous)
        | (rcases frames with ⟨_, _, rfl⟩
           simpa only [List.forall_mem_cons, handlerEntered, true_and] using previous)

theorem ExitContextReached.handler_entered {rootFuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {α : Type} {invocation : ExitInvocation α} {state : ExecutionState}
    (reached : ExitContextReached rootFuel config context invocation state)
    (activation : RuntimeActivation) (resultTypes : List Ty) (origin : Goose.Core.OriginId)
    (member : ExitLexicalFrame.handler activation resultTypes origin ∈ context) :
    ∃ fuel pre body initial implementation,
      ExitReached rootFuel config (.activation (fuel + 1) activation pre body origin) initial ∧
      config.module.impls[activation.implementation]? = some implementation ∧
      resultTypes = implementation.results.toList.map (·.ty) := by
  have all : ∀ frame ∈ context, handlerEntered rootFuel config frame := by
    clear member activation resultTypes origin
    induction reached with
    | initial => simp only [List.not_mem_nil, false_implies, implies_true]
    | call callerReached site frames previous =>
        exact frames_handlers_entered (contextReached_forget callerReached) site frames previous
  exact all _ member

#print axioms ExitContextReached.handler_entered
end Goose.Proofs.ExitExecution
