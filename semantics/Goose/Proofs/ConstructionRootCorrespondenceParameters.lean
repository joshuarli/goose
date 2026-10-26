import Goose.Proofs.ConstructionRootCorrespondenceScopes

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (RootInst VarId ScopeInst)

theorem bindAll_localValueCorrespondence (interpretation : RootInterpretation) (context : Context)
    (scopeInstance : ScopeInst) (values : List (VarId × Value)) (visible : List VarId)
    (before : ExecutionState)
    (resolved : ∀ entry ∈ values, rootOf interpretation.environment entry.1 before =
      .ok (.local interpretation.environment.act scopeInstance entry.1) before)
    (rooted : ∀ entry ∈ values, LocalValueRooted interpretation context entry.1 entry.2)
    (previous : LocalRootCorrespondence interpretation context visible before) :
    ∃ after, bindAll interpretation.environment.act scopeInstance values before = .ok () after ∧
      LocalRootCorrespondence interpretation context (values.map Prod.fst ++ visible) after := by
  induction values generalizing visible before with
  | nil => exact ⟨before, rfl, previous⟩
  | cons entry rest ih =>
    obtain ⟨middle, bound, valid⟩ := bindRoot_localValueCorrespondence interpretation context visible before
      entry.1 (.local interpretation.environment.act scopeInstance entry.1) entry.2
      (resolved entry (by simp)) (rooted entry (by simp)) previous
    obtain ⟨after, remaining, final⟩ := ih (entry.1 :: visible) middle
      (fun other member => rootOf_transfer interpretation other.1 before middle _ (resolved other (by simp [member])))
      (fun other member => rooted other (by simp [member])) valid
    refine ⟨after, ?_, ?_⟩
    · simpa [bindAll, List.forIn_cons, bind, pure, bound] using remaining
    · intro id member
      apply final id
      simpa only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append, or_assoc,
        or_left_comm, or_comm] using member

theorem validated_parameters_bindAll_localValueCorrespondence
    (module : Module) (implementationId : Nat) (implementation : Impl)
    (interpretation : RootInterpretation) (context : Context) (values : List (VarId × Value))
    (before : ExecutionState) (accepted : validate module = .ok ())
    (present : module.impls[implementationId]? = some implementation)
    (variables : interpretation.environment.vars = implementation.vars)
    (parameters : ∀ entry ∈ values, ∃ (index : Nat) (parameter : Param),
      implementation.params[index]? = some parameter ∧ parameter.var = entry.1)
    (rooted : ∀ entry ∈ values,
      LocalValueRooted (interpretation.enterScope implementation.body.scope before.nextScope) context entry.1 entry.2) :
    freshScope before = .ok before.nextScope { before with nextScope := before.nextScope + 1 } ∧
      ∃ after, bindAll interpretation.environment.act before.nextScope values
          { before with nextScope := before.nextScope + 1 } = .ok () after ∧
        LocalRootCorrespondence (interpretation.enterScope implementation.body.scope before.nextScope)
          context (values.map Prod.fst) after := by
  refine ⟨rfl, ?_⟩
  simpa only [List.append_nil, RootInterpretation.enterScope] using
    bindAll_localValueCorrespondence (interpretation.enterScope implementation.body.scope before.nextScope)
      context before.nextScope values [] { before with nextScope := before.nextScope + 1 }
      (by
        intro entry member
        obtain ⟨index, parameter, parameterAt, equal⟩ := parameters entry member
        have resolved := (validated_parameter_initialRoot module implementationId implementation index parameter
          interpretation before accepted present parameterAt variables).2
        simpa only [equal, RootInterpretation.enterScope] using resolved)
      rooted (by intro id member; cases member)

end Goose.Proofs.ConstructionRootCorrespondence
