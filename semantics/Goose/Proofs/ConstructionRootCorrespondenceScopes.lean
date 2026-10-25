import Goose.Proofs.ConstructionRootCorrespondenceWrites
import Goose.Proofs.ConstructionRootCorrespondenceAliases
import Goose.Construct.Validate

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (RootInst VarId ScopeInst)

def RootInterpretation.enterScope (interpretation : RootInterpretation) (scope : Nat) (scopeInstance : ScopeInst) :
    RootInterpretation :=
  { interpretation with environment := { interpretation.environment with
    scopes := (scope, scopeInstance) :: interpretation.environment.scopes } }

theorem instantiates_enterScope (interpretation : RootInterpretation) (scope : Nat) (scopeInstance : ScopeInst)
    (fresh : ∀ entry ∈ interpretation.environment.scopes, entry.1 ≠ scope)
    (symbolic : RootRef) (root : RootInst) (actual : Instantiates interpretation symbolic root) :
    Instantiates (interpretation.enterScope scope scopeInstance) symbolic root := by
  cases actual with
  | global id declared => exact .global id declared
  | static id synthetic => exact .static id synthetic
  | parameter id root supplied => exact .parameter id root supplied
  | «local» id descriptor oldInstance declared active =>
    have different := fresh (descriptor.scope, oldInstance) (List.mem_of_find?_eq_some active)
    apply Instantiates.local (interpretation := interpretation.enterScope scope scopeInstance) id descriptor oldInstance declared
    simp only [RootInterpretation.enterScope, List.find?_cons]
    have skipped : (scope == descriptor.scope) = false := beq_eq_false_iff_ne.mpr different.symm
    simp only [skipped, active]

theorem rootIn_enterScope (interpretation : RootInterpretation) (scope : Nat) (scopeInstance : ScopeInst)
    (fresh : ∀ entry ∈ interpretation.environment.scopes, entry.1 ≠ scope)
    (roots : List RootRef) (root : RootInst) (actual : RootIn interpretation roots root) :
    RootIn (interpretation.enterScope scope scopeInstance) roots root := by
  obtain ⟨symbolic, member, instantiated⟩ := actual
  exact ⟨symbolic, member, instantiates_enterScope interpretation scope scopeInstance fresh symbolic root instantiated⟩

theorem rootOf_enterScope_existing (interpretation : RootInterpretation) (scope : Nat) (scopeInstance : ScopeInst)
    (fresh : ∀ entry ∈ interpretation.environment.scopes, entry.1 ≠ scope)
    (id : VarId) (root : RootInst) (state : ExecutionState)
    (resolved : rootOf interpretation.environment id state = .ok root state) :
    rootOf (interpretation.enterScope scope scopeInstance).environment id state = .ok root state := by
  have actual := instantiates_enterScope interpretation scope scopeInstance fresh (.local id) root
    (rootOf_instantiates interpretation id state root resolved)
  cases actual with
  | «local» id descriptor oldInstance declared active => simp only [rootOf, declared, active, pure]

theorem rootOf_enterScope_current (interpretation : RootInterpretation) (scope : Nat) (scopeInstance : ScopeInst)
    (id : VarId) (descriptor : LocalVar) (state : ExecutionState)
    (declared : interpretation.environment.vars[id]? = some descriptor) (localScope : descriptor.scope = scope) :
    rootOf (interpretation.enterScope scope scopeInstance).environment id state =
      .ok (.local interpretation.environment.act scopeInstance id) state := by
  simp only [RootInterpretation.enterScope, rootOf, declared, List.find?_cons, localScope, beq_self_eq_true, pure]

theorem freshScope_localRoot (interpretation : RootInterpretation) (scope : Nat) (id : VarId)
    (descriptor : LocalVar) (state : ExecutionState)
    (declared : interpretation.environment.vars[id]? = some descriptor) (localScope : descriptor.scope = scope) :
    freshScope state = .ok state.nextScope { state with nextScope := state.nextScope + 1 } ∧
      rootOf (interpretation.enterScope scope state.nextScope).environment id
          { state with nextScope := state.nextScope + 1 } =
        .ok (.local interpretation.environment.act state.nextScope id) { state with nextScope := state.nextScope + 1 } :=
  ⟨rfl, rootOf_enterScope_current interpretation scope state.nextScope id descriptor _ declared localScope⟩

theorem validated_parameter_initialRoot (module : Module) (implementationId : Nat) (implementation : Impl)
    (index : Nat) (parameter : Param) (descriptor : LocalVar) (interpretation : RootInterpretation)
    (state : ExecutionState) (accepted : validate module = .ok ())
    (present : module.impls[implementationId]? = some implementation)
    (parameterAt : implementation.params[index]? = some parameter)
    (descriptorAt : implementation.vars[index]? = some descriptor)
    (variables : interpretation.environment.vars = implementation.vars) :
    freshScope state = .ok state.nextScope { state with nextScope := state.nextScope + 1 } ∧
      rootOf (interpretation.enterScope implementation.body.scope state.nextScope).environment parameter.var
          { state with nextScope := state.nextScope + 1 } =
        .ok (.local interpretation.environment.act state.nextScope parameter.var)
          { state with nextScope := state.nextScope + 1 } := by
  have parameterId := validated_parameter_variable module implementationId implementation index parameter accepted present parameterAt
  have parameterScope := validated_parameter_scope module implementationId implementation index parameter descriptor
    accepted present parameterAt descriptorAt
  have bodyScope := validated_body_scope module implementationId implementation accepted present
  have declared : interpretation.environment.vars[parameter.var]? = some descriptor := by
    rw [variables, parameterId]
    exact descriptorAt
  exact freshScope_localRoot interpretation implementation.body.scope parameter.var descriptor state declared
    (parameterScope.trans bodyScope.symm)

theorem localRootCorrespondence_enterScope (interpretation : RootInterpretation) (context : Context)
    (scope : Nat) (scopeInstance : ScopeInst) (visible : List VarId) (state : ExecutionState)
    (fresh : ∀ entry ∈ interpretation.environment.scopes, entry.1 ≠ scope)
    (active : ∀ id ∈ visible, ∃ root, rootOf interpretation.environment id state = .ok root state)
    (valid : LocalRootCorrespondence interpretation context visible state) :
    LocalRootCorrespondence (interpretation.enterScope scope scopeInstance) context visible state := by
  intro id member root value resolved found location reference
  obtain ⟨oldRoot, oldResolved⟩ := active id member
  have stillResolved := rootOf_enterScope_existing interpretation scope scopeInstance fresh id oldRoot state oldResolved
  rw [resolved] at stillResolved
  cases stillResolved
  obtain ⟨roots, annotated, rooted⟩ := valid id member root value oldResolved found location reference
  exact ⟨roots, annotated, rootIn_enterScope interpretation scope scopeInstance fresh roots location.root rooted⟩

theorem contentRootCorrespondence_enterScope (interpretation : RootInterpretation) (context : Context)
    (scope : Nat) (scopeInstance : ScopeInst) (visible : List VarId) (fuel : Nat) (layout : LayoutEnv)
    (state : ExecutionState) (fresh : ∀ entry ∈ interpretation.environment.scopes, entry.1 ≠ scope)
    (active : ∀ id ∈ visible, ∃ root, rootOf interpretation.environment id state = .ok root state)
    (valid : ContentRootCorrespondence interpretation context visible fuel layout state) :
    ContentRootCorrespondence (interpretation.enterScope scope scopeInstance) context visible fuel layout state := by
  intro id member root location value resolved found read interior reference
  obtain ⟨oldRoot, oldResolved⟩ := active id member
  have stillResolved := rootOf_enterScope_existing interpretation scope scopeInstance fresh id oldRoot state oldResolved
  rw [resolved] at stillResolved
  cases stillResolved
  obtain ⟨roots, annotated, rooted⟩ := valid id member root location value oldResolved found read interior reference
  exact ⟨roots, annotated, rootIn_enterScope interpretation scope scopeInstance fresh roots interior.root rooted⟩

theorem rootFrontier_enterScope (interpretation : RootInterpretation) (scope : Nat) (scopeInstance : ScopeInst)
    (nextAct : Nat) (frontier : RootFrontier interpretation nextAct) :
    RootFrontier (interpretation.enterScope scope scopeInstance) nextAct := frontier

end Goose.Proofs.ConstructionRootCorrespondence
