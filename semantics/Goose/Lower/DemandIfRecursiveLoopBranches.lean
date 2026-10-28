import Goose.Lower.DemandIfRecursiveLoopCursor
import Goose.Lower.DemandIfInvariantNoneFamilies
import Goose.Lower.DemandIfInvariantSomeFamilies
import Goose.Lower.DemandIfThenProgress
import Goose.Lower.DemandIfElseProgress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_recursive_loop_if_some_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (yesFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
    (yesFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes)
    (noFamily : RecursiveLoopIfBranchFamily cx results selected loop depth no)
    (yesNoValue : yes.value = none) (noNoValue : no.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected loop condition (@GeneratedControlProgressCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected loop (.ifS condition yes (some no) origin)
      (@RecursiveLoopIfCursor cfg cx results root owner loop (depth + 1) env selected) := by
  let inner := fun {innerEnv : Env} (innerSelected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod innerEnv.vars results) root owner) =>
    @RecursiveLoopIfCursor cfg cx results root owner loop depth innerEnv innerSelected
  have invariantYes : ∀ (state : St) (before : LS),
      InvariantSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (@inner { env with scopes := (yes.scope, state.nextScope) :: env.scopes } selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (fun _ => True) := by
    intro state before
    constructor
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
      exact (yesFamily state before).1 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
      exact (yesFamily state before).2 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  have invariantNo : ∀ (state : St) (before : LS),
      InvariantSequencePrefixFamily (env := { env with scopes := (no.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false no no.stmts (@inner { env with scopes := (no.scope, state.nextScope) :: env.scopes } selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily (env := { env with scopes := (no.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false no no.stmts (fun _ => True) := by
    intro state before
    constructor
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
      exact (noFamily state before).1 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
      exact (noFamily state before).2 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  have yesNormal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (yesFragment middle).recursive.normal done
  have noNormal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (no.scope, middle.nextScope) :: env.scopes } no.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (noFragment middle).recursive.normal done
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  exact accepted_generated_invariant_if_some_prefix_family loop selected condition yes no origin inner (fun _ => True) (fun _ _ => trivial)
    invariantYes invariantNo yesNormal noNormal yesNoValue noNoValue conditionFamily source owned occurrence rows coverage admitted bounded realized input extended trivial steps


theorem accepted_generated_recursive_loop_if_some_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (yesFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noFragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
    (yesFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes)
    (noFamily : RecursiveLoopIfBranchFamily cx results selected loop depth no)
    (yesNoValue : yes.value = none) (noNoValue : no.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop condition) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.ifS condition yes (some no) origin) := by
  let inner := fun {innerEnv : Env} (innerSelected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod innerEnv.vars results) root owner) =>
    @RecursiveLoopIfCursor cfg cx results root owner loop depth innerEnv innerSelected
  have invariantYes : ∀ (state : St) (before : LS),
      InvariantSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (@inner { env with scopes := (yes.scope, state.nextScope) :: env.scopes } selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (fun _ => True) := by
    intro state before
    constructor
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
      exact (yesFamily state before).1 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
      exact (yesFamily state before).2 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  have invariantNo : ∀ (state : St) (before : LS),
      InvariantSequencePrefixFamily (env := { env with scopes := (no.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false no no.stmts (@inner { env with scopes := (no.scope, state.nextScope) :: env.scopes } selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily (env := { env with scopes := (no.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false no no.stmts (fun _ => True) := by
    intro state before
    constructor
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
      exact (noFamily state before).1 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
      exact (noFamily state before).2 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  have yesNormal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (yesFragment middle).recursive.normal done
  have noNormal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (no.scope, middle.nextScope) :: env.scopes } no.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (noFragment middle).recursive.normal done
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps fuel stop after stopped nonTimeout
  exact accepted_generated_invariant_if_some_stopped_family loop selected condition yes no origin inner (fun _ => True) (fun _ _ => trivial)
    invariantYes invariantNo yesNormal noNormal yesNoValue noNoValue conditionFamily source owned occurrence rows coverage admitted bounded realized input extended trivial steps stopped nonTimeout


theorem accepted_generated_recursive_loop_if_none_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily cx results selected loop condition (@GeneratedControlProgressCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected loop (.ifS condition yes none origin)
      (@RecursiveLoopIfCursor cfg cx results root owner loop (depth + 1) env selected) := by
  let inner := fun {innerEnv : Env} (innerSelected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod innerEnv.vars results) root owner) =>
    @RecursiveLoopIfCursor cfg cx results root owner loop depth innerEnv innerSelected
  have invariantFamily : ∀ (state : St) (before : LS),
      InvariantSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (@inner { env with scopes := (yes.scope, state.nextScope) :: env.scopes } selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (fun _ => True) := by
    intro state before
    constructor
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
      exact (branchFamily state before).1 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
      exact (branchFamily state before).2 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  have normal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (fragment middle).recursive.normal done
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  exact accepted_generated_invariant_if_none_prefix_family loop selected condition yes origin inner (fun _ => True) (fun _ _ => trivial)
    invariantFamily normal noValue conditionFamily source owned occurrence rows coverage admitted bounded realized input extended trivial steps


theorem accepted_generated_recursive_loop_if_none_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedIfStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : RecursiveLoopIfBranchFamily cx results selected loop depth yes)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop condition) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.ifS condition yes none origin) := by
  let inner := fun {innerEnv : Env} (innerSelected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod innerEnv.vars results) root owner) =>
    @RecursiveLoopIfCursor cfg cx results root owner loop depth innerEnv innerSelected
  have invariantFamily : ∀ (state : St) (before : LS),
      InvariantSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (@inner { env with scopes := (yes.scope, state.nextScope) :: env.scopes } selected) (fun _ => True) ∧
      InvariantStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        cx results selected before loop [] false yes yes.stmts (fun _ => True) := by
    intro state before
    constructor
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps
      exact (branchFamily state before).1 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps
    · intro innerState source owned occurrence all scope value required map rows coverage admitted bounded initial start realized input extended _ taken reached steps fuel stop after stopped nonTimeout
      exact (branchFamily state before).2 source owned occurrence all scope value rows coverage admitted bounded realized input extended steps stopped nonTimeout
  have normal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (fragment middle).recursive.normal done
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps fuel stop after stopped nonTimeout
  exact accepted_generated_invariant_if_none_stopped_family loop selected condition yes origin inner (fun _ => True) (fun _ _ => trivial)
    invariantFamily normal noValue conditionFamily source owned occurrence rows coverage admitted bounded realized input extended trivial steps stopped nonTimeout


#print axioms accepted_generated_recursive_loop_if_some_prefix_family
#print axioms accepted_generated_recursive_loop_if_some_stopped_family
#print axioms accepted_generated_recursive_loop_if_none_prefix_family
#print axioms accepted_generated_recursive_loop_if_none_stopped_family
end Goose.Lower
