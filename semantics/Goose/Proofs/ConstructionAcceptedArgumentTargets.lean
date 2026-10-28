import Goose.Proofs.ConstructionAcceptedSource
import Goose.Proofs.ConstructionAcceptedCallEffects
import Goose.Proofs.ConstructionRootCorrespondenceCalls

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem rootedGlobal_argumentTarget (interpretation : RootInterpretation) (roots : List RootRef) (global : Nat)
    (inBounds : global < interpretation.globalCount) (rooted : RootIn interpretation roots (.global global)) :
    ∃ target ∈ rootsTargets roots,
      match target with
      | .global id => global = id
      | .param id => interpretation.parameters id (.global global) ∧ global < interpretation.globalCount := by
  obtain ⟨symbolic, member, instantiated⟩ := rooted
  cases instantiated with
  | global declared =>
    exact ⟨.global global, List.mem_filterMap.mpr ⟨.global global, member, rfl⟩, rfl⟩
  | static id synthetic => exact False.elim ((Nat.not_lt_of_ge synthetic) inBounds)
  | parameter id root actual =>
    exact ⟨.param id, List.mem_filterMap.mpr ⟨.param id, member, rfl⟩, actual, inBounds⟩

theorem mapCallTargets_parameter_argument (callee : Impl) (context : Context) (arguments : List (List RootRef))
    (targets : List Target) (parameter : Nat) (roots : List RootRef) (target : Target)
    (parameterMember : .param parameter ∈ targets) (argumentAt : arguments[parameter]? = some roots)
    (targetMember : target ∈ rootsTargets roots) : target ∈ mapCallTargets callee context arguments targets := by
  induction targets with
  | nil => cases parameterMember
  | cons head tail ih =>
    simp only [List.mem_cons] at parameterMember
    rcases parameterMember with same | later
    · subst head
      simp [mapCallTargets, argumentAt, targetMember]
    · cases head with
      | global id => simp only [mapCallTargets, List.mem_cons]; exact Or.inr (ih later)
      | param id => simp only [mapCallTargets, List.mem_append]; exact Or.inr (ih later)

theorem argumentRoots_globalAvailable (interpretation : RootInterpretation) (initialized : Nat) (effects : Eff)
    (roots : List RootRef) (global : Nat) (available : GlobalEffectsAvailable interpretation initialized effects)
    (included : ∀ target, target ∈ rootsTargets roots → target ∈ effects.accessTargets)
    (inBounds : global < interpretation.globalCount) (rooted : RootIn interpretation roots (.global global)) :
    global < initialized := by
  obtain ⟨target, member, instantiated⟩ := rootedGlobal_argumentTarget interpretation roots global inBounds rooted
  cases target <;> exact available _ (included _ member) global instantiated

private theorem argumentTarget_added (before added : List Target) (target : Target) (member : target ∈ added) :
    target ∈ addTargets before added := (callEffects_addTargets_members before added target).2 (Or.inr member)

theorem callEffects_parameter_argument (callee : Impl) (context : Context) (arguments : List (List RootRef))
    (summary : Summary) (before : Eff) (parameter : Nat) (roots : List RootRef) (target : Target)
    (known : callee.summary = .known summary) (argumentAt : arguments[parameter]? = some roots)
    (parameterMember : .param parameter ∈ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks)
    (targetMember : target ∈ rootsTargets roots) : target ∈ (callEffects callee context arguments before).accessTargets := by
  simp only [List.mem_append] at parameterMember
  simp only [callEffects, known, Eff.accessTargets, List.mem_append]
  rcases parameterMember with ((read | write) | grow) | shrink
  · exact Or.inl (Or.inl (Or.inl (argumentTarget_added _ _ _ (mapCallTargets_parameter_argument callee context arguments summary.reads parameter roots target read argumentAt targetMember))))
  · exact Or.inl (Or.inl (Or.inr (argumentTarget_added _ _ _ (mapCallTargets_parameter_argument callee context arguments summary.writes parameter roots target write argumentAt targetMember))))
  · exact Or.inl (Or.inr (argumentTarget_added _ _ _ (mapCallTargets_parameter_argument callee context arguments summary.grows parameter roots target grow argumentAt targetMember)))
  · exact Or.inr (argumentTarget_added _ _ _ (mapCallTargets_parameter_argument callee context arguments summary.shrinks parameter roots target shrink argumentAt targetMember))

theorem callEffects_parameter_globalAvailable (caller : RootInterpretation) (activation : RuntimeActivation)
    (callee : Impl) (context : Context) (arguments : List (List RootRef)) (summary : Summary) (before : Eff)
    (initialized parameter global : Nat) (known : callee.summary = .known summary)
    (parameterMember : .param parameter ∈ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks)
    (available : GlobalEffectsAvailable caller initialized (callEffects callee context arguments before))
    (instantiated : (CallInterpretation caller activation arguments).parameters parameter (.global global))
    (inBounds : global < caller.globalCount) : global < initialized := by
  obtain ⟨roots, argumentAt, rooted⟩ := instantiated
  apply argumentRoots_globalAvailable caller initialized (callEffects callee context arguments before) roots global available
  · intro target member
    exact callEffects_parameter_argument callee context arguments summary before parameter roots target known argumentAt parameterMember member
  · exact inBounds
  · exact rooted

theorem expandTargets_global_maps (callee : Impl) (context : Context) (arguments : List (List RootRef))
    (targets : List Target) (global : Nat) (member : .global global ∈ expandTargets callee context targets) :
    .global global ∈ mapCallTargets callee context arguments targets := by
  induction targets with
  | nil => cases member
  | cons head rest ih =>
    cases head with
    | global id =>
      simp only [expandTargets, List.flatMap_cons, List.mem_append, List.not_mem_nil, or_false, mapCallTargets, List.mem_cons] at member ⊢
      rcases member with same | later
      · exact Or.inl same
      · exact Or.inr (ih later)
    | param id =>
      simp only [expandTargets, List.flatMap_cons, List.mem_append] at member
      simp only [mapCallTargets, List.mem_append]
      rcases member with here | later
      · cases variableAt : callee.vars[id]? with
        | none => simp [variableAt] at here
        | some descriptor =>
          cases annotation : context.varRoots.find? (·.1 == id) with
          | none => simp [variableAt, annotation] at here
          | some entry =>
            cases entry with
            | mk var roots =>
              by_cases reference : descriptor.ty.isRefLike
              · simp only [variableAt, annotation, reference, ↓reduceIte] at here
                have target : .global global ∈ paramGlobals callee context id := by
                  simp only [paramGlobals, variableAt, annotation, reference, ↓reduceIte]
                  simp only [rootsTargets, List.mem_filterMap] at here
                  obtain ⟨root, rootMember, targetEq⟩ := here
                  cases root with
                  | «local» id => simp [rootTarget] at targetEq
                  | «static» => simp [rootTarget] at targetEq
                  | param id => simp [rootTarget] at targetEq
                  | global id =>
                    simp only [rootTarget, Option.some.injEq, Target.global.injEq] at targetEq
                    subst id
                    exact List.mem_filterMap.mpr ⟨.global global, rootMember, rfl⟩
                exact Or.inl (Or.inr target)
              · simp [variableAt, annotation, reference] at here
      · exact Or.inr (ih later)

theorem checkSummary_global_callEffects (module : Module) (callee : Impl) (context : Context)
    (arguments : List (List RootRef)) (effects before : Eff) (summary : Summary) (global : Nat)
    (known : callee.summary = .known summary) (checked : checkSummary module callee context effects = .ok ())
    (member : .global global ∈ effects.accessTargets) :
    .global global ∈ (callEffects callee context arguments before).accessTargets := by
  have included := checkSummary_accessIncluded module callee context effects summary known checked member
  simp only [List.mem_append] at included
  simp only [callEffects, known, Eff.accessTargets, List.mem_append]
  rcases included with ((read | write) | grow) | shrink
  · exact Or.inl (Or.inl (Or.inl (argumentTarget_added _ _ _ (expandTargets_global_maps callee context arguments summary.reads global read))))
  · exact Or.inl (Or.inl (Or.inr (argumentTarget_added _ _ _ (expandTargets_global_maps callee context arguments summary.writes global write))))
  · exact Or.inl (Or.inr (argumentTarget_added _ _ _ (expandTargets_global_maps callee context arguments summary.grows global grow)))
  · exact Or.inr (argumentTarget_added _ _ _ (expandTargets_global_maps callee context arguments summary.shrinks global shrink))

theorem checkSummary_global_bodyAvailable (module : Module) (callee : Impl) (context : Context)
    (arguments : List (List RootRef)) (effects before : Eff) (summary : Summary) (global initialized : Nat)
    (caller : RootInterpretation) (known : callee.summary = .known summary)
    (checked : checkSummary module callee context effects = .ok ())
    (member : .global global ∈ effects.accessTargets)
    (available : GlobalEffectsAvailable caller initialized (callEffects callee context arguments before)) : global < initialized := by
  exact available (.global global) (checkSummary_global_callEffects module callee context arguments effects before summary global known checked member)
    global rfl

theorem contextRootFactsAt_parameterized_globalAvailable (module : Module) (context : Context) (callee : Impl)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt module context aliases calls escaping names)
    (present : module.impls[context.impl]? = some callee) (summary : Summary) (known : callee.summary = .known summary)
    (arguments : List (List RootRef)) (before : Eff) (caller : RootInterpretation) (initialized : Nat)
    (available : GlobalEffectsAvailable caller initialized (callEffects callee context arguments before)) :
    ∃ bodyContext actualEscapes value state,
      parameterBodyRootContext module callee context = .ok bodyContext ∧ bodyTargets module = .ok actualEscapes ∧
      rpBlockValue { mod := module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) ∧
      ∀ global, .global global ∈ state.eff.accessTargets → global < initialized := by
  obtain ⟨actual, bodyContext, actualEscapes, value, state, effects, present', closed, targets, rooted,
    callsIncluded, included, summaryChecked⟩ := contextRootFactsAt_bodyEffects module context aliases calls escaping names facts
  have same : actual = callee := Option.some.inj (present'.symm.trans present)
  subst actual
  refine ⟨bodyContext, actualEscapes, value, state, closed, targets, rooted, ?_⟩
  intro global member
  exact checkSummary_global_bodyAvailable module callee context arguments effects before summary global initialized caller known
    summaryChecked (included member) available

theorem contextRootFactsAt_parameterized_bodyAvailable (module : Module) (context : Context) (callee : Impl)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt module context aliases calls escaping names)
    (present : module.impls[context.impl]? = some callee) (summary : Summary) (known : callee.summary = .known summary)
    (arguments : List (List RootRef)) (before : Eff) (caller : RootInterpretation) (activation : RuntimeActivation) (initialized : Nat)
    (available : GlobalEffectsAvailable caller initialized (callEffects callee context arguments before))
    (noParameterEffects : ∀ bodyContext actualEscapes value state,
      parameterBodyRootContext module callee context = .ok bodyContext → bodyTargets module = .ok actualEscapes →
      rpBlockValue { mod := module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) →
      ∀ id, .param id ∉ state.eff.accessTargets) :
    ∃ bodyContext actualEscapes value state,
      parameterBodyRootContext module callee context = .ok bodyContext ∧ bodyTargets module = .ok actualEscapes ∧
      rpBlockValue { mod := module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) ∧
      GlobalEffectsAvailable (CallInterpretation caller activation arguments) initialized state.eff := by
  obtain ⟨bodyContext, actualEscapes, value, state, closed, targets, rooted, globals⟩ :=
    contextRootFactsAt_parameterized_globalAvailable module context callee aliases calls escaping names facts present summary known
      arguments before caller initialized available
  refine ⟨bodyContext, actualEscapes, value, state, closed, targets, rooted, ?_⟩
  intro target member global instantiated
  cases target with
  | global id =>
    change global = id at instantiated
    subst global
    exact globals id member
  | param id => exact False.elim ((noParameterEffects bodyContext actualEscapes value state closed targets rooted id) member)

theorem expandTargets_noParameterMember (callee : Impl) (context : Context) (targets : List Target)
    (noParameters : ∀ id, .param id ∉ targets) (id : Nat) : .param id ∉ expandTargets callee context targets := by
  induction targets with
  | nil => simp [expandTargets]
  | cons head tail ih =>
    have tailNo : ∀ id, .param id ∉ tail := by
      intro id member
      exact noParameters id (List.mem_cons_of_mem _ member)
    cases head with
    | global global => simpa [expandTargets] using ih tailNo
    | param parameter => exact False.elim (noParameters parameter (by simp))

theorem checkSummary_noParameter_bodyEffects (module : Module) (callee : Impl) (context : Context)
    (effects : Eff) (summary : Summary) (known : callee.summary = .known summary)
    (checked : checkSummary module callee context effects = .ok ())
    (noParameters : ∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks) :
    ∀ id, .param id ∉ effects.accessTargets := by
  have included := checkSummary_accessIncluded module callee context effects summary known checked
  intro id member
  have inside := included member
  simp only [List.mem_append] at inside
  rcases inside with ((read | write) | grow) | shrink
  · exact expandTargets_noParameterMember callee context summary.reads (by intro n h; exact noParameters n (by simp [h])) id read
  · exact expandTargets_noParameterMember callee context summary.writes (by intro n h; exact noParameters n (by simp [h])) id write
  · exact expandTargets_noParameterMember callee context summary.grows (by intro n h; exact noParameters n (by simp [h])) id grow
  · exact expandTargets_noParameterMember callee context summary.shrinks (by intro n h; exact noParameters n (by simp [h])) id shrink

theorem contextRootFactsAt_parameterized_summaryAvailable (module : Module) (context : Context) (callee : Impl)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt module context aliases calls escaping names)
    (present : module.impls[context.impl]? = some callee) (summary : Summary) (known : callee.summary = .known summary)
    (noParameters : ∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks)
    (arguments : List (List RootRef)) (before : Eff) (caller : RootInterpretation) (activation : RuntimeActivation) (initialized : Nat)
    (available : GlobalEffectsAvailable caller initialized (callEffects callee context arguments before)) :
    ∃ bodyContext actualEscapes value state,
      parameterBodyRootContext module callee context = .ok bodyContext ∧ bodyTargets module = .ok actualEscapes ∧
      rpBlockValue { mod := module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) ∧
      GlobalEffectsAvailable (CallInterpretation caller activation arguments) initialized state.eff ∧
      (∀ id, .param id ∉ state.eff.accessTargets) := by
  obtain ⟨actual, bodyContext, actualEscapes, value, state, effects, present', closed, targets, rooted,
    callsIncluded, included, summaryChecked⟩ := contextRootFactsAt_bodyEffects module context aliases calls escaping names facts
  have same : actual = callee := Option.some.inj (present'.symm.trans present)
  subst actual
  have globals := contextRootFactsAt_parameterized_globalAvailable module context callee aliases calls escaping names facts present summary known
    arguments before caller initialized available
  obtain ⟨otherContext, otherEscapes, otherValue, otherState, otherClosed, otherTargets, otherRooted, otherGlobals⟩ := globals
  have sameContext := Except.ok.inj (closed.symm.trans otherClosed)
  have sameEscapes := Except.ok.inj (targets.symm.trans otherTargets)
  subst otherContext otherEscapes
  obtain ⟨sameValue, sameState⟩ := Prod.mk.inj (Except.ok.inj (rooted.symm.trans otherRooted))
  subst otherValue otherState
  have noBodyParameters := checkSummary_noParameter_bodyEffects module callee context effects summary known summaryChecked noParameters
  refine ⟨bodyContext, actualEscapes, value, state, closed, targets, rooted, ?_⟩
  constructor
  · intro target member global instantiated
    cases target with
    | global id =>
      change global = id at instantiated
      subst global
      exact otherGlobals id member
    | param id => exact False.elim (noBodyParameters id (included member))
  · intro id member
    exact noBodyParameters id (included member)

theorem GlobalEffectsAvailable.retarget_noParameters (source target : RootInterpretation) (initialized : Nat) (effects : Eff)
    (available : GlobalEffectsAvailable source initialized effects)
    (noParameters : ∀ id, .param id ∉ effects.accessTargets) : GlobalEffectsAvailable target initialized effects := by
  intro effect member global instantiated
  cases effect with
  | global id => exact available (.global id) member global instantiated
  | param id => exact False.elim (noParameters id member)

#print axioms GlobalEffectsAvailable.retarget_noParameters
#print axioms contextRootFactsAt_parameterized_summaryAvailable
#print axioms checkSummary_noParameter_bodyEffects
#print axioms expandTargets_noParameterMember
#print axioms contextRootFactsAt_parameterized_bodyAvailable
#print axioms contextRootFactsAt_parameterized_globalAvailable
#print axioms checkSummary_global_bodyAvailable
#print axioms checkSummary_global_callEffects
#print axioms expandTargets_global_maps
#print axioms callEffects_parameter_globalAvailable
#print axioms callEffects_parameter_argument
#print axioms argumentRoots_globalAvailable
#print axioms mapCallTargets_parameter_argument
#print axioms rootedGlobal_argumentTarget
end Goose.Proofs.ConstructionAcceptedExecution
