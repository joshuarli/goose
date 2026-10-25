import Goose.Lower.Validation.SourceReplacementCallContentsApartFormal
import Goose.Lower.Validation.SourceReplacementCallContentsApartSources
import Goose.Lower.Validation.AdmittedSourceCallArgumentTypes
import Goose.Lower.Validation.SourceCanonicalFactsParameterModes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem tyArgs_refSlice_local_slice {env : TEnv} {callee : Impl}
    {parameters : List Param} {arguments : List Arg} {start finish index slot : Nat}
    {parameter : Param} {parameterVar : LocalVar} {mutability : Mutability}
    (typed : tyArgs env callee parameters arguments start = .ok ((), finish))
    (arity : parameters.length = arguments.length)
    (parameterAt : parameters[index]? = some parameter)
    (_mode : parameter.mode = .byRef)
    (parameterRow : callee.vars[parameter.var]? = some parameterVar)
    (reference : parameterVar.ty.isRefSlice = true)
    (argumentAt : arguments[index]? = some (.byRef mutability (.var slot))) :
    ∃ localVar, env.vars[slot]? = some localVar ∧ localVar.ty.isSlice = true := by
  obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp argumentAt
  have split : arguments = arguments.take index ++
      .byRef mutability (.var slot) :: arguments.drop (index + 1) := by
    calc
      arguments = arguments.take index ++ arguments.drop index := (List.take_append_drop index arguments).symm
      _ = _ := by rw [List.drop_eq_getElem_cons bound, selected]
  obtain ⟨earlier, actual, later, childStart, childFinish,
    parameterSplit, parameterLength, _, currentTyped, _⟩ :=
    tyArgs_argument_checkpoint (by rw [← split]; exact arity) (by rw [← split]; exact typed)
  have actualAt : parameters[index]? = some actual := by
    rw [parameterSplit, ← List.length_take_of_le (Nat.le_of_lt bound), ← parameterLength]
    simp
  have same : actual = parameter := Option.some.inj (actualAt.symm.trans parameterAt)
  subst actual
  obtain ⟨actualVar, info, placeFinish, restStart, row, placeTyped, _, passable, _⟩ :=
    tyArgs_byRef_head currentTyped
  have same : actualVar = parameterVar := Option.some.inj (row.symm.trans parameterRow)
  subst actualVar
  have infoSlice : info.ty.isSlice = true := by
    cases type : parameterVar.ty <;> simp [type, Ty.isRefSlice] at reference
    case ref parameterMu payload =>
      cases payload <;> simp at reference
      case slice sliceMu element =>
        rw [type] at passable
        have samePayload : info.ty = .slice sliceMu element := by
          simp only [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at passable
          exact passable.1
        simpa [samePayload, Ty.isSlice] using reference
  simp only [tyPlace] at placeTyped
  obtain ⟨localVar, middle, found, returned⟩ := (st_bind_ok _ _ _ _).mp placeTyped
  have declared := (varOf_ok env slot childStart (localVar, middle)).mp found
  have infoEq := congrArg Prod.fst ((st_pure_ok _ _ _).mp returned)
  dsimp only at infoEq
  subst info
  exact ⟨localVar, declared.2.1, infoSlice⟩

theorem CallArgumentsTrace.local_slice_type {module : Core.Module} {env : PEnv}
    {syntaxArgs : List Arg} {args : List ValueId} {func : Func}
    {function index slot : Nat} {sourceOrigin : OriginId} {mutability : Mutability}
    {callee : Context} {implementation : Impl}
    (trace : CallArgumentsTrace env syntaxArgs args func function sourceOrigin)
    (accepted : Core.validate module = .ok ()) (envModule : env.mod = module)
    (calleeAt : module.contexts[function]? = some callee)
    (implementationAt : module.impls[callee.impl]? = some implementation)
    (reference : ((lowerContextAt module callee implementation).params[index]?).any Ty.isRefSlice = true)
    (argumentAt : syntaxArgs[index]? = some (.byRef mutability (.var slot))) :
    ∃ localVar, env.impl.vars[slot]? = some localVar ∧ localVar.ty.isSlice = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, typingEnv, start, finish, type,
    typingModule, typingVariables, typed⟩ := trace
  obtain ⟨actualContext, actualImpl, argsStart, argsFinish, resultStart, contextRow, implRow,
    arity, argumentsTyped, _⟩ := tyExpr_call_tables typed
  rw [typingModule, envModule, calleeAt] at contextRow
  cases Option.some.inj contextRow
  rw [typingModule, envModule, implementationAt] at implRow
  cases Option.some.inj implRow
  obtain ⟨parameter, parameterVar, parameterAt, parameterRow, mode, parameterReference⟩ :=
    lowerContext_refSlice_parameter_of_accepted accepted implementationAt reference
  obtain ⟨localVar, row, slice⟩ := tyArgs_refSlice_local_slice argumentsTyped arity
    (by simpa only [Array.getElem?_toList] using parameterAt) mode parameterRow parameterReference argumentAt
  exact ⟨localVar, typingVariables ▸ row, slice⟩

theorem ReplacementDemandContext.rhs_active_local_content_atoms_apart
    {module : Core.Module} {contextIndex : ContextId} {path : List Nat}
    {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module contextIndex path place rhs origin)
    {env : PEnv} (access : env.access = demand.planContext.approvals.access)
    {slot : Nat} {localVar : LocalVar} {ceiling : List RootRef}
    (variableAt : env.impl.vars[slot]? = some localVar)
    (slice : localVar.ty.isSlice = true) (annotation : env.ann slot = some ceiling)
    (used : slot ∈ rhs.variables) (active : slot ∈ demand.statement.expected.frame.active)
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (invalidates : target.invalidates = true)
    {func : Func} {queries : ReplacementQueries} {owner : ValueId}
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner)
      (target.roots.flatMap func.expandParameterRoot))
    {state : State} {address : Roots} {actual : List RootRef}
    (known : normalize func (content func state address) = some actual)
    (within : actual ⊆ ceiling.flatMap func.expandParameterRoot) :
    (content func state address).AtomsWithin (OwnerDependencyApart (lower module) func queries owner) := by
  have interior : localVar.ty.interiorTarget?.isSome = true := by
    cases type : localVar.ty <;> simp [type, Ty.isSlice] at slice
    case slice mu element => rfl
  have notRef : localVar.ty.isRefSlice = false := by
    cases type : localVar.ty <;> simp [type, Ty.isSlice] at slice
    case slice mu element => rfl
  let alias : RetainedAlias := ⟨localVar.ty, ceiling, AliasSource.variable slot⟩
  have aliasAt : demand.planContext.approvals.access.aliasVariable slot = .ok (some alias) := by
    rw [← access]
    simp only [PEnv.ann] at annotation
    simp [AccessEnv.aliasVariable, PEnv.access, variableAt, notRef, interior,
      AccessEnv.variableRoots, annotation, alias, pure, Except.pure, bind, Except.bind]
  exact demand.rhs_alias_content_atoms_apart used active targetAt invalidates aliasAt interior
    closed ownerKnown known within

theorem CallArgumentsPhysical.local_roots {env : PEnv} {upper : Prov}
    {syntaxArgs : List Arg} {args : List ValueId} {index argument slot : Nat} {mutability : Mutability}
    (physical : CallArgumentsPhysical env upper syntaxArgs args)
    (argumentAt : args[index]? = some argument)
    (sourceAt : syntaxArgs[index]? = some (.byRef mutability (.var slot))) :
    rootsAt upper.vals argument = [.local slot] := by
  have address := physical index argument _ argumentAt sourceAt mutability (.var slot) rfl ⟨slot, .inl rfl⟩
  cases address with
  | «local» varId same rootsEq => cases same; exact rootsEq
  | contents varId same _ _ => cases same

theorem canonical_call_local_content_atoms
    {module : GIR.Module} {func callee : Func} {types : Array (Option VTy)}
    {provenance upper : Prov} {results : Array (List RootRef)}
    (native : FunctionCanonicalFacts module func types provenance results)
    {final current : State} (canonical : final.CanonicalWithin func types provenance)
    {block : GIR.Block} {value function index argument slot : Nat}
    {arguments : List ValueId} {origin : Option OriginId}
    (member : block ∈ func.blocks.toList)
    (called : Inst.def value (.call function arguments origin) ∈ block.insts)
    (calleeAt : module.funcs[function]? = some callee)
    (reference : (callee.params[index]?).any Ty.isRefSlice = true)
    (argumentAt : arguments[index]? = some argument)
    (physical : rootsAt upper.vals argument = [.local slot])
    (below : rootsAt provenance.vals argument ⊆ rootsAt upper.vals argument)
    (growth : current.Extends final) {predicate : Atom → Prop}
    (cell : (flowAt current.slots slot).AtomsWithin predicate) :
    (content func current (flowAt current.values argument)).AtomsWithin predicate := by
  obtain ⟨callFacts⟩ := native.calls block member value function arguments origin called
  have same : callFacts.callee = callee := Option.some.inj (callFacts.calleeAt.symm.trans calleeAt)
  cases formal : callee.params[index]? with
  | none => simp [formal] at reference
  | some type =>
    have typeReference : type.isRefSlice = true := by simpa [formal] using reference
    obtain ⟨outer, inner, element, typeEq, flat⟩ := isRefSlice_shape typeReference
    subst type
    obtain ⟨found, actualMu, foundAt, typed, bounded⟩ := callFacts.references index outer (.slice inner element)
      (by simpa only [same] using formal)
    have equal : found = argument := Option.some.inj (foundAt.symm.trans argumentAt)
    subst found
    apply canonical_scoped_content_atoms canonical native.roots.parameters
      (by rw [canonical.shape.values]; exact bounded) typed rfl below growth
    constructor
    · intro receiver present
      rw [physical] at present
      have equal : receiver = slot := by simpa using present
      simpa only [equal] using cell
    · intro receiver present
      simp [physical] at present

#print axioms tyArgs_refSlice_local_slice
#print axioms CallArgumentsTrace.local_slice_type
#print axioms ReplacementDemandContext.rhs_active_local_content_atoms_apart
#print axioms canonical_call_local_content_atoms
#print axioms CallArgumentsPhysical.local_roots

end Goose.Lower.Validation
