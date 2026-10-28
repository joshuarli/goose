import Goose.Proofs.ConstructionAcceptedSource
import Goose.Proofs.ConstructionRootCorrespondenceCalls

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private theorem callEffects_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem effWithin_subset (name what : String) (found declared : List Target)
    (checked : effWithin name what found declared = .ok ()) : found ⊆ declared := by
  unfold effWithin at checked
  cases result : found.find? (fun target => !declared.contains target) with
  | some target =>
    change (match found.find? (fun target => !declared.contains target) with
      | some target => Goose.Core.reject .summary _
      | none => pure ()) = .ok () at checked
    rw [result] at checked
    cases checked
  | none =>
    intro target member
    have all := List.find?_eq_none.mp result target member
    simpa using all

private theorem callEffects_forAll_member {α : Type} (rows : List α) (action : α → Goose.Core.V Unit)
    (checked : Goose.Core.forAll rows action = .ok ()) : ∀ row ∈ rows, action row = .ok () := by
  induction rows with
  | nil => intro row absent; cases absent
  | cons row rows ih =>
    simp only [Goose.Core.forAll, bind, Except.bind] at checked
    cases first : action row with
    | error failure => simp only [first] at checked; cases checked
    | ok value =>
      cases value
      simp only [first] at checked
      intro selected member
      rcases List.mem_cons.mp member with same | member
      · subst selected; exact first
      · exact ih checked selected member

theorem checkSummaryTargets_noParameter (module : Module) (impl : Impl) (what : String) (targets : List Target)
    (parameters : impl.params = #[]) (checked : checkSummaryTargets module impl what targets = .ok ()) :
    ∀ id, Target.param id ∉ targets := by
  intro id member
  have accepted := callEffects_forAll_member targets _ checked (.param id) member
  simp [parameters, Goose.Core.reject] at accepted

theorem checkSummary_noParameter (module : Module) (impl : Impl) (context : Context) (effects : Eff)
    (summary : Summary) (known : impl.summary = .known summary) (parameters : impl.params = #[])
    (checked : checkSummary module impl context effects = .ok ()) :
    ∀ id, Target.param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks := by
  unfold checkSummary at checked
  rw [known] at checked
  obtain ⟨_, reads, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, writes, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, grows, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, shrinks, _⟩ := callEffects_bind_success _ _ _ checked
  intro id member
  simp only [List.mem_append] at member
  rcases member with ((read | write) | grow) | shrink
  · exact checkSummaryTargets_noParameter module impl "reads" summary.reads parameters reads id read
  · exact checkSummaryTargets_noParameter module impl "writes" summary.writes parameters writes id write
  · exact checkSummaryTargets_noParameter module impl "grows" summary.grows parameters grows id grow
  · exact checkSummaryTargets_noParameter module impl "shrinks" summary.shrinks parameters shrinks id shrink

theorem expandTargets_noParameters (impl : Impl) (context : Context) (targets : List Target)
    (noParameters : ∀ id, Target.param id ∉ targets) :
    expandTargets impl context targets = mapCallTargets impl context [] targets := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
    have tail : ∀ id, Target.param id ∉ rest := by
      intro id member
      exact noParameters id (List.mem_cons_of_mem _ member)
    cases target with
    | global id =>
      have same := ih tail
      simp only [expandTargets] at same ⊢
      simp only [List.flatMap_cons, mapCallTargets, List.singleton_append]
      exact congrArg (List.cons (.global id)) same
    | param id => exact False.elim (noParameters id (by simp))

theorem checkSummary_accessIncluded (module : Module) (impl : Impl) (context : Context) (effects : Eff)
    (summary : Summary) (known : impl.summary = .known summary)
    (checked : checkSummary module impl context effects = .ok ()) :
    effects.accessTargets ⊆ expandTargets impl context summary.reads ++
      expandTargets impl context summary.writes ++ expandTargets impl context summary.grows ++
      expandTargets impl context summary.shrinks := by
  unfold checkSummary at checked
  rw [known] at checked
  obtain ⟨_, _, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, _, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, _, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, _, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, _, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, _, checked⟩ := callEffects_bind_success _ _ _ checked
  obtain ⟨_, _, checked⟩ := callEffects_bind_success _ _ _ checked
  cases unknown : effects.unknown with
  | true => simp [unknown, Goose.Core.reject, bind, Except.bind] at checked
  | false =>
    simp only [unknown, Bool.false_eq_true, ↓reduceIte] at checked
    obtain ⟨_, reads, checked⟩ := callEffects_bind_success _ _ _ checked
    obtain ⟨_, writes, checked⟩ := callEffects_bind_success _ _ _ checked
    obtain ⟨_, grows, checked⟩ := callEffects_bind_success _ _ _ checked
    obtain ⟨_, shrinks, checked⟩ := callEffects_bind_success _ _ _ checked
    have r := effWithin_subset impl.name "reads" effects.reads _ reads
    have w := effWithin_subset impl.name "writes" effects.writes _ writes
    have g := effWithin_subset impl.name "grows" effects.grows _ grows
    have s := effWithin_subset impl.name "shrinks" effects.shrinks _ shrinks
    intro target member
    simp only [Eff.accessTargets, List.mem_append] at member ⊢
    rcases member with ((read | write) | grow) | shrink
    · exact Or.inl (Or.inl (Or.inl (r read)))
    · exact Or.inl (Or.inl (Or.inr (w write)))
    · exact Or.inl (Or.inr (g grow))
    · exact Or.inr (s shrink)

theorem callEffects_addTargets_members (before added : List Target) (target : Target) :
    target ∈ addTargets before added ↔ target ∈ before ∨ target ∈ added := by
  induction added generalizing before with
  | nil => simp [addTargets]
  | cons selected rest ih =>
    simp only [addTargets, List.foldl_cons]
    split
    · rename_i retained
      change target ∈ addTargets before rest ↔ _
      rw [ih]
      have present : selected ∈ before := by simpa using retained
      simp only [List.mem_cons]
      constructor
      · intro member
        rcases member with member | member
        · exact Or.inl member
        · exact Or.inr (Or.inr member)
      · intro member
        rcases member with member | equal | member
        · exact Or.inl member
        · exact Or.inl (equal ▸ present)
        · exact Or.inr member
    · change target ∈ addTargets (before ++ [selected]) rest ↔ _
      rw [ih]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]


theorem checkSummary_zeroArgument_callEffects (module : Module) (impl : Impl) (context : Context)
    (effects before : Eff) (summary : Summary) (known : impl.summary = .known summary)
    (parameters : impl.params = #[]) (checked : checkSummary module impl context effects = .ok ()) :
    EffectTargetsIncluded effects (callEffects impl context [] before) := by
  have included := checkSummary_accessIncluded module impl context effects summary known checked
  have noParameters := checkSummary_noParameter module impl context effects summary known parameters checked
  have reads : ∀ id, Target.param id ∉ summary.reads := by
    intro id member; exact noParameters id (by simp [member])
  have writes : ∀ id, Target.param id ∉ summary.writes := by
    intro id member; exact noParameters id (by simp [member])
  have grows : ∀ id, Target.param id ∉ summary.grows := by
    intro id member; exact noParameters id (by simp [member])
  have shrinks : ∀ id, Target.param id ∉ summary.shrinks := by
    intro id member; exact noParameters id (by simp [member])
  intro target member
  have inside := included member
  rw [expandTargets_noParameters impl context summary.reads reads,
    expandTargets_noParameters impl context summary.writes writes,
    expandTargets_noParameters impl context summary.grows grows,
    expandTargets_noParameters impl context summary.shrinks shrinks] at inside
  simp only [List.mem_append] at inside
  change target ∈ (callEffects impl context [] before).accessTargets
  simp only [callEffects, known, Eff.accessTargets, List.mem_append, callEffects_addTargets_members]
  rcases inside with ((read | write) | grow) | shrink
  · exact Or.inl (Or.inl (Or.inl (Or.inr read)))
  · exact Or.inl (Or.inl (Or.inr (Or.inr write)))
  · exact Or.inl (Or.inr (Or.inr grow))
  · exact Or.inr (Or.inr shrink)

theorem zeroArgument_body_effectsAvailable (module : Module) (impl : Impl) (context : Context)
    (effects before : Eff) (summary : Summary) (known : impl.summary = .known summary)
    (parameters : impl.params = #[]) (checked : checkSummary module impl context effects = .ok ())
    (caller : Goose.Proofs.ConstructionRootCorrespondence.RootInterpretation) (activation : RuntimeActivation)
    (initialized : Nat) (available : GlobalEffectsAvailable caller initialized (callEffects impl context [] before)) :
    GlobalEffectsAvailable (Goose.Proofs.ConstructionRootCorrespondence.CallInterpretation caller activation []) initialized effects := by
  have included := checkSummary_zeroArgument_callEffects module impl context effects before summary known parameters checked
  intro target member global instantiated
  cases target with
  | global id =>
    change global = id at instantiated
    subst global
    exact available (.global id) (included member) id rfl
  | param id =>
    obtain ⟨⟨roots, absent, _⟩, _⟩ := instantiated
    simp at absent

theorem contextRootFactsAt_zeroArgument_bodyAvailable (module : Module) (context : Context) (impl : Impl)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt module context aliases calls escaping names)
    (present : module.impls[context.impl]? = some impl) (summary : Summary) (known : impl.summary = .known summary)
    (parameters : impl.params = #[]) (before : Eff)
    (caller : Goose.Proofs.ConstructionRootCorrespondence.RootInterpretation) (activation : RuntimeActivation)
    (initialized : Nat) (available : GlobalEffectsAvailable caller initialized (callEffects impl context [] before)) :
    ∃ bodyContext actualEscapes value state,
      parameterBodyRootContext module impl context = .ok bodyContext ∧ bodyTargets module = .ok actualEscapes ∧
      rpBlockValue { mod := module, impl := impl, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] impl.body ⟨impl.params.size, {}, []⟩ = .ok (value, state) ∧
      GlobalEffectsAvailable (Goose.Proofs.ConstructionRootCorrespondence.CallInterpretation caller activation []) initialized state.eff := by
  obtain ⟨callee, bodyContext, actualEscapes, value, state, effects, present', closed, targets, rooted,
    callsIncluded, included, summaryChecked⟩ := contextRootFactsAt_bodyEffects module context aliases calls escaping names facts
  have same : callee = impl := Option.some.inj (present'.symm.trans present)
  subst callee
  have finalAvailable := zeroArgument_body_effectsAvailable module impl context effects before summary known parameters
    summaryChecked caller activation initialized available
  refine ⟨bodyContext, actualEscapes, value, state, closed, targets, rooted, ?_⟩
  intro target member global instantiates
  exact finalAvailable target (included member) global instantiates

#print axioms callEffects_addTargets_members
#print axioms contextRootFactsAt_zeroArgument_bodyAvailable
#print axioms zeroArgument_body_effectsAvailable
#print axioms checkSummary_zeroArgument_callEffects
#print axioms expandTargets_noParameters
#print axioms checkSummary_noParameter
#print axioms checkSummaryTargets_noParameter
#print axioms checkSummary_accessIncluded
#print axioms effWithin_subset
end Goose.Proofs.ConstructionAcceptedExecution
