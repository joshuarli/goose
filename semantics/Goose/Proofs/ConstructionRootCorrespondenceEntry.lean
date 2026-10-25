import Goose.Proofs.ConstructionRootCorrespondenceWrites
import Goose.Proofs.ConstructionRootCorrespondenceAliases
import Goose.Construct.Validate

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct

private theorem success_bind {α β : Type} (action : Goose.Core.V α)
    (next : α → Goose.Core.V β) (result : β) :
    (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

theorem validated_entry (module : Module) (accepted : validate module = .ok ()) :
    ∃ context implementation, module.contexts[module.entry]? = some context ∧
      module.impls[context.impl]? = some implementation ∧
      implementation.params = #[] ∧ implementation.results = #[] := by
  unfold validate at accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, checked, _⟩ := (success_bind _ _ _).mp accepted
  change (do
    let some context := module.contexts[module.entry]? |
      Goose.Core.reject .type "entry context is outside the context table"
    let some implementation := module.impls[context.impl]? |
      Goose.Core.reject .type "entry context names a missing implementation"
    unless implementation.params.isEmpty && implementation.results.isEmpty do
      Goose.Core.reject .type s!"the entry {implementation.name} must take no parameters and return nothing") =
        .ok () at checked
  cases contextAt : module.contexts[module.entry]? with
  | none => simp [contextAt, Goose.Core.reject] at checked
  | some context =>
    cases implementationAt : module.impls[context.impl]? with
    | none => simp [contextAt, implementationAt, Goose.Core.reject] at checked
    | some implementation =>
      refine ⟨context, implementation, rfl, implementationAt, ?_⟩
      simp only [contextAt, implementationAt] at checked
      split at checked
      · rename_i empty
        simpa using empty
      · cases checked

theorem parameterBodyRootContext_emptyParameters (module : Module) (implementation : Impl)
    (context : Context) (empty : implementation.params = #[]) :
    parameterBodyRootContext module implementation context = .ok context := by
  simp [parameterBodyRootContext, empty, pure, Except.pure]

def EntryInterpretation (environment : RuntimeActivation) (globalCount : Nat) : RootInterpretation :=
  ⟨environment, globalCount, fun _ _ => False⟩

theorem freshAct_emptyParameters_frontier (environment : RuntimeActivation) (globalCount : Nat)
    (state : ExecutionState) :
    freshAct state = .ok state.nextAct { state with nextAct := state.nextAct + 1 } ∧
      RootFrontier (EntryInterpretation { environment with act := state.nextAct } globalCount) (state.nextAct + 1) := by
  refine ⟨rfl, Nat.lt_succ_self _, ?_⟩
  intro index act scope variableId impossible
  exact impossible.elim

theorem entry_aliasComplete (environment : RuntimeActivation) (globalCount : Nat) :
    AliasComplete (EntryInterpretation environment globalCount) [] := by
  intro left right root leftInst rightInst
  cases leftInst <;> cases rightInst <;> simp_all [EntryInterpretation, RootAlias]
  all_goals omega

theorem validated_entry_bodyContext (module : Module) (accepted : validate module = .ok ()) :
    ∃ context implementation, module.contexts[module.entry]? = some context ∧
      module.impls[context.impl]? = some implementation ∧
      parameterBodyRootContext module implementation context = .ok context := by
  obtain ⟨context, implementation, contextAt, implementationAt, empty, _⟩ := validated_entry module accepted
  exact ⟨context, implementation, contextAt, implementationAt,
    parameterBodyRootContext_emptyParameters module implementation context empty⟩

theorem validated_moduleRootFacts (module : Module) (accepted : validate module = .ok ()) :
    ModuleRootFacts module := by
  unfold validate at accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  obtain ⟨_, _, accepted⟩ := (success_bind _ _ _).mp accepted
  exact checkModuleExitRoots_facts module accepted

end Goose.Proofs.ConstructionRootCorrespondence
