import Goose.Lower.DemandWhileCallStoppedFamily
import Goose.Lower.DemandIfRecursiveLoopBranches

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_nested_call_if_none_prefix_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : ∀ (state : St) (before : LS),
      ReachableSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (yes.scope, state.nextScope) :: env.scopes } loop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop condition (@GeneratedControlProgressCursor cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩)) :
    ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.ifS condition yes none origin)
      (@NestedCallLoopCursor cfg caller results root owner (depth + 1) env loop selected) := by
  let inner := fun {innerEnv : Env} (innerSelected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod innerEnv.vars results) root owner) =>
    @NestedCallLoopCursor cfg caller results root owner depth innerEnv loop innerSelected
  have normal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (fragment middle).recursive.normal_any_env done
  apply ReachableStatementPrefixFamily.mapCursor
    (cursor := @RecursiveLoopIfCursorStep cfg ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results root owner loop inner env selected)
    (accepted_generated_invariant_if_none_prefix_family loop selected condition yes origin inner
      (fun point => Evidence.RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
      (fun valid steps => steps.reachable valid) branchFamily normal noValue conditionFamily)
  intro statement state source before built initial start map required runtime cursor
  exact .conditional cursor


theorem accepted_generated_nested_call_if_none_stopped_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes : Core.Block) (origin : OriginId)
    (fragment : ∀ state : St, BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (branchFamily : ∀ (state : St) (before : LS),
      ReachableSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (yes.scope, state.nextScope) :: env.scopes } loop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts)
    (noValue : yes.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop condition) :
    ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.ifS condition yes none origin) := by
  let inner := fun {innerEnv : Env} (innerSelected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod innerEnv.vars results) root owner) =>
    @NestedCallLoopCursor cfg caller results root owner depth innerEnv loop innerSelected
  have normal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (fragment middle).recursive.normal_any_env done
  intro state
  exact accepted_generated_invariant_if_none_stopped_family loop selected condition yes origin inner
    (fun point => Evidence.RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
    (fun valid steps => steps.reachable valid) branchFamily normal noValue conditionFamily (state := state)


theorem accepted_generated_nested_call_if_some_prefix_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (yesFragment : ∀ state : St, BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noFragment : ∀ state : St, BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
    (yesFamily : ∀ (state : St) (before : LS),
      ReachableSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (yes.scope, state.nextScope) :: env.scopes } loop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts)
    (noFamily : ∀ (state : St) (before : LS),
      ReachableSequencePrefixFamily (env := { env with scopes := (no.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false no no.stmts
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (no.scope, state.nextScope) :: env.scopes } loop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (no.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false no no.stmts)
    (yesNoValue : yes.value = none) (noNoValue : no.value = none)
    (conditionFamily : GeneratedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop condition (@GeneratedControlProgressCursor cfg env ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩)) :
    ReachableStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.ifS condition yes (some no) origin)
      (@NestedCallLoopCursor cfg caller results root owner (depth + 1) env loop selected) := by
  let inner := fun {innerEnv : Env} (innerSelected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod innerEnv.vars results) root owner) =>
    @NestedCallLoopCursor cfg caller results root owner depth innerEnv loop innerSelected
  have yesNormal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (yesFragment middle).recursive.normal_any_env done
  have noNormal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (no.scope, middle.nextScope) :: env.scopes } no.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (noFragment middle).recursive.normal_any_env done
  apply ReachableStatementPrefixFamily.mapCursor
    (cursor := @RecursiveLoopIfCursorStep cfg ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results root owner loop inner env selected)
    (accepted_generated_invariant_if_some_prefix_family loop selected condition yes no origin inner
      (fun point => Evidence.RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
      (fun valid steps => steps.reachable valid) yesFamily noFamily yesNormal noNormal yesNoValue noNoValue conditionFamily)
  intro statement state source before built initial start map required runtime cursor
  exact .conditional cursor

#print axioms accepted_generated_nested_call_if_some_prefix_family

theorem accepted_generated_nested_call_if_some_stopped_family {cfg : Cfg} {env : Env} {caller : Func} {results : List Ty}
    {root : DemandNode} {owner : Nat} (loop : Option LoopCtx)
    (selected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod env.vars results) root owner)
    (depth : Nat) (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (yesFragment : ∀ state : St, BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (yes.scope, state.nextScope) :: env.scopes } yes.stmts)
    (noFragment : ∀ state : St, BoundedNestedCallLoopStatements cfg depth
      { env with scopes := (no.scope, state.nextScope) :: env.scopes } no.stmts)
    (yesFamily : ∀ (state : St) (before : LS),
      ReachableSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (yes.scope, state.nextScope) :: env.scopes } loop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (yes.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false yes yes.stmts)
    (noFamily : ∀ (state : St) (before : LS),
      ReachableSequencePrefixFamily (env := { env with scopes := (no.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false no no.stmts
        (@NestedCallLoopCursor cfg caller results root owner depth { env with scopes := (no.scope, state.nextScope) :: env.scopes } loop selected) ∧
      ReachableStoppedSequencePrefixFamily (env := { env with scopes := (no.scope, state.nextScope) :: env.scopes })
        ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected before loop [] false no no.stmts)
    (yesNoValue : yes.value = none) (noNoValue : no.value = none)
    (conditionFamily : GeneratedStoppedExpressionPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop condition) :
    ReachableStoppedStatementPrefixFamily ⟨⟨cfg.profile, lower cfg.mod⟩, caller⟩ results selected loop (.ifS condition yes (some no) origin) := by
  let inner := fun {innerEnv : Env} (innerSelected : GeneratedDemandRootSelection cfg.mod caller (lowerEnv cfg.mod innerEnv.vars results) root owner) =>
    @NestedCallLoopCursor cfg caller results root owner depth innerEnv loop innerSelected
  have yesNormal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (yes.scope, middle.nextScope) :: env.scopes } yes.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (yesFragment middle).recursive.normal_any_env done
  have noNormal : ∀ (middle : St) {fuel : Nat} {state after : St} {flow : Flow},
      execStmts fuel cfg { env with scopes := (no.scope, middle.nextScope) :: env.scopes } no.stmts state = .ok flow after → flow = .normal .unit := by
    intro middle fuel state after flow done
    exact (noFragment middle).recursive.normal_any_env done
  intro state
  exact accepted_generated_invariant_if_some_stopped_family loop selected condition yes no origin inner
    (fun point => Evidence.RuntimePoint ⟨cfg.profile, lower cfg.mod⟩ caller point.point point.frame point.state)
    (fun valid steps => steps.reachable valid) yesFamily noFamily yesNormal noNormal yesNoValue noNoValue conditionFamily (state := state)

#print axioms accepted_generated_nested_call_if_some_stopped_family

#print axioms accepted_generated_nested_call_if_none_prefix_family
#print axioms accepted_generated_nested_call_if_none_stopped_family
end Goose.Lower
