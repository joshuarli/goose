import Goose.Proofs.ConstructionAcceptedCallEffects
import Goose.Proofs.ConstructionRootCorrespondenceCursors

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem rpExpr_zeroArgument_access {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {before after : RState} {roots : List RootRef} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[])
    (checked : rpExpr env (.call target [] origin) before = .ok (roots, after)) :
    EffectTargetsIncluded (callEffects callee context [] {}) after.eff := by
  unfold rpExpr at checked
  simp only [rpArgs, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind, contextAt, calleeAt,
    parameters, Array.toList_empty, List.zip, List.zipWith, List.forIn_nil] at checked
  cases content : checkContents env target [] [] with
  | error failure => simp [content, liftV] at checked
  | ok result =>
    cases result
    simp only [content, liftV] at checked
    split at checked
    · simp only [bind, StateT.bind] at checked
      cases updated : noteResultConstruction env before with
      | error failure => simp [updated, Except.bind] at checked
      | ok pair =>
        have call : rpCall env target [] pair.2 = .ok (roots, after) := by
          simpa [updated, Except.bind] using checked
        exact rpCall_zeroArgument_access contextAt calleeAt call
    · exact rpCall_zeroArgument_access contextAt calleeAt checked
theorem checkedValue_zeroArgument_bodyAvailable (config : EvalConfig) (caller : ConstructionSourceFrame)
    (target : Goose.Core.ContextId) (context : Context) (callee : Impl) (origin : Nat)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (sourceModule : caller.source.mod = config.module) (parameters : callee.params = #[])
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt config.module context aliases calls escaping names)
    (summary : Summary) (known : callee.summary = .known summary) (activation : RuntimeActivation) :
    ∃ bodyContext actualEscapes value state,
      parameterBodyRootContext config.module callee context = .ok bodyContext ∧
      bodyTargets config.module = .ok actualEscapes ∧
      rpBlockValue { mod := config.module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) ∧
      GlobalEffectsAvailable (Goose.Proofs.ConstructionRootCorrespondence.CallInterpretation caller.interpretation activation []) caller.initialized state.eff := by
  have callerContext : caller.source.mod.contexts[target]? = some context := by rw [sourceModule]; exact contextAt
  have callerCallee : caller.source.mod.impls[context.impl]? = some callee := by rw [sourceModule]; exact calleeAt
  have included := rpExpr_zeroArgument_access callerContext callerCallee parameters checked.provenance
  have available : GlobalEffectsAvailable caller.interpretation caller.initialized (callEffects callee context [] {}) := by
    intro target member global instantiated
    exact checked.available target (included member) global instantiated
  exact contextRootFactsAt_zeroArgument_bodyAvailable config.module context callee aliases calls escaping names facts calleeAt
    summary known parameters {} caller.interpretation activation caller.initialized available

#print axioms checkedValue_zeroArgument_bodyAvailable
#print axioms rpExpr_zeroArgument_access
end Goose.Proofs.ConstructionAcceptedExecution
