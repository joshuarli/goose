import Goose.Proofs.ConstructionAcceptedParameterizedCallEffects
import Goose.Proofs.ConstructionAcceptedParameterTargetMapping
import Goose.Proofs.ConstructionAcceptedParameterArgumentRoots
namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem rpExpr_singleByValue_accessUpper {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {expression : Expr} {before middle after : RState} {roots : List RootRef}
    {argumentRoots : List (List RootRef)} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter])
    (arguments : rpArgs env [.byVal expression] before = .ok (argumentRoots, middle))
    (checked : rpExpr env (.call target [.byVal expression] origin) before = .ok (roots, after)) :
    ∀ access ∈ after.eff.accessTargets, access ∈ middle.eff.accessTargets ∨ access ∈ (callEffects callee context argumentRoots {}).accessTargets := by
  unfold rpExpr at checked
  simp only [arguments, bind, StateT.bind, Except.bind, contextAt, calleeAt, parameters,
    List.zip, List.zipWith, List.forIn_cons, List.forIn_nil, pure, StateT.pure, Except.pure] at checked
  cases content : checkContents env target [.byVal expression] argumentRoots with
  | error failure => simp [content, liftV] at checked
  | ok result =>
    cases result
    simp only [content, liftV] at checked
    split at checked
    · simp only [bind, StateT.bind] at checked
      cases updated : noteResultConstruction env middle with
      | error failure => simp [updated, Except.bind] at checked
      | ok pair =>
        have call : rpCall env target argumentRoots pair.2 = .ok (roots, after) := by
          simpa [updated, Except.bind] using checked
        have same : pair.2.eff.accessTargets = middle.eff.accessTargets := by
          simp [noteResultConstruction, modify, Eff.accessTargets] at updated ⊢
          cases updated
          rfl
        intro access member
        simpa [same] using rpCall_accessUpper argumentRoots contextAt calleeAt call access member
    · exact rpCall_accessUpper argumentRoots contextAt calleeAt checked
theorem rpExpr_singleByValue_noParameter {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {expression : Expr} {before middle after : RState} {roots : List RootRef}
    {argumentRoots : List (List RootRef)} {origin : Nat} (summary : Summary)
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary)
    (clear : NoParameterAccess middle.eff)
    (argumentsClear : ∀ result, result ∈ argumentRoots → ∀ id, .param id ∉ rootsTargets result)
    (arguments : rpArgs env [.byVal expression] before = .ok (argumentRoots, middle))
    (checked : rpExpr env (.call target [.byVal expression] origin) before = .ok (roots, after)) :
    NoParameterAccess after.eff := by
  have mapped : NoParameterAccess (callEffects callee context argumentRoots {}) :=
    callEffects_noParameter callee context argumentRoots summary {} known (by simp [NoParameterAccess, Eff.accessTargets]) argumentsClear
  intro id member
  rcases rpExpr_singleByValue_accessUpper contextAt calleeAt parameters arguments checked (.param id) member with prior | call
  · exact clear id prior
  · exact mapped id call

theorem rpArgs_singleByValue_accessTargets {env : PEnv} {expression : Expr} {before middle after : RState}
    {roots : List RootRef} {argumentRoots : List (List RootRef)}
    (operand : rpExpr env expression before = .ok (roots, middle))
    (checked : rpArgs env [.byVal expression] before = .ok (argumentRoots, after)) : after.eff.accessTargets = middle.eff.accessTargets := by
  simp only [rpArgs, operand, bind, StateT.bind, Except.bind] at checked
  repeat' first
    | split at checked
    | simp_all
  rename_i captured capturedValue interior interiorValue retained retainedValue capturedEq interiorEq retainedEq
  change Except.ok (([], ({} : Eff)), _) = Except.ok capturedValue at capturedEq
  cases capturedEq
  simp [pure, StateT.pure, Except.pure] at checked
  cases checked.2
  unfold liftV at interiorEq
  split at interiorEq <;> simp_all
  change (if (interiorValue.fst.any fun root => ([] : List RootRef).any fun accessed => root == accessed || env.aliases.contains (root, accessed) || env.aliases.contains (accessed, root)) || false then rejP .shrink "shrink may invalidate a retained reference or slice" else pure ()) interiorValue.snd = Except.ok retainedValue at retainedEq
  split at retainedEq <;> simp_all [pure, StateT.pure, Except.pure]
  cases retainedEq
  cases interiorEq
  change addTargets middle.eff.reads [] ++ addTargets middle.eff.writes [] ++ addTargets middle.eff.grows [] ++ addTargets middle.eff.shrinks [] = middle.eff.accessTargets
  simp [Eff.accessTargets, addTargets]

theorem rpExpr_scalarLocalCall_noParameter {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {localId origin : Nat} {descriptor : LocalVar} {before after : RState} {roots : List RootRef}
    (summary : Summary) (contextAt : env.mod.contexts[target]? = some context)
    (calleeAt : env.mod.impls[context.impl]? = some callee) (parameters : callee.params = #[parameter])
    (known : callee.summary = .known summary) (declared : env.impl.vars[localId]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) (clear : NoParameterAccess before.eff)
    (checked : rpExpr env (.call target [.byVal (.read (.var localId))] origin) before = .ok (roots, after)) :
    NoParameterAccess after.eff := by
  obtain ⟨selected, actual, arguments, middle, selectedAt, actualAt, argumentChecked, contents⟩ :=
    rpExpr_call_argumentChecks checked
  have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans contextAt)
  subst selected
  have sameCallee : actual = callee := Option.some.inj (actualAt.symm.trans calleeAt)
  subst actual
  have argumentRoots := scalarLocal_singleArgument_roots env localId descriptor before middle arguments declared scalar argumentChecked
  have argumentsClear : ∀ result, result ∈ arguments → ∀ id, .param id ∉ rootsTargets result := by
    rw [argumentRoots]
    simp [rootsTargets]
  cases operand : rpExpr env (.read (.var localId)) before with
  | error error => simp [rpArgs, bind, StateT.bind, Except.bind, operand] at argumentChecked
  | ok pair =>
    obtain ⟨operandRoots, operandAfter⟩ := pair
    have same := rpArgs_singleByValue_accessTargets operand argumentChecked
    have localSame := localRead_accessTargets env localId before operandAfter operandRoots operand
    have middleClear : NoParameterAccess middle.eff := by
      intro id member
      exact clear id (by rw [← localSame, ← same]; exact member)
    exact rpExpr_singleByValue_noParameter summary contextAt calleeAt parameters known middleClear argumentsClear argumentChecked checked

theorem scalarLocalCallTail_noParameter (source : PEnv) (scope target origin localId : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar) (summary : Summary)
    (before after : RState) (result : List RootRef × (Nat × Nat))
    (contextAt : source.mod.contexts[target]? = some context) (calleeAt : source.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary)
    (declared : source.impl.vars[localId]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) (clear : NoParameterAccess before.eff)
    (rooted : rpBlockValue source [] ⟨scope, [], some (.call target [.byVal (.read (.var localId))] origin)⟩ before = .ok (result, after)) :
    NoParameterAccess after.eff := by
  obtain ⟨_, middle, roots, statements, tail, resultEq⟩ := rpBlockValue_body rooted
  simp only [List.length_nil, Nat.add_zero, rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statements
  cases statements.2
  exact rpExpr_scalarLocalCall_noParameter (env := { source with scopes := scope :: source.scopes }) summary contextAt calleeAt parameters known declared scalar clear (by simpa using tail)

#print axioms scalarLocalCallTail_noParameter
#print axioms rpExpr_scalarLocalCall_noParameter
#print axioms rpArgs_singleByValue_accessTargets
#print axioms rpExpr_singleByValue_noParameter
#print axioms rpExpr_singleByValue_accessUpper
end Goose.Proofs.ConstructionAcceptedExecution
