import Goose.Lower.Validation.SourceReplacementLexicalWritersHolderPlaces
import Goose.Lower.Validation.SourceCanonicalFactsParameterModes
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsTypingCheckpoints

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem call_refSlice_argument_reference {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {function : FnId} {arguments : List ValueId}
    (site : Goose.GIR.ReplacementContentFlow.Model.CallSiteFacts module func types provenance function arguments)
    {callee : Func} (calleeAt : module.funcs[function]? = some callee)
    {index argument : Nat} (argumentAt : arguments[index]? = some argument)
    (reference : (callee.params[index]?).any Ty.isRefSlice = true) : valRefLike types argument = true := by
  have same := Option.some.inj (site.calleeAt.symm.trans calleeAt)
  subst callee
  cases formalAt : site.callee.params[index]? with
  | none => simp [formalAt] at reference
  | some formal =>
    cases formal with
    | ref mode payload =>
      obtain ⟨actual,actualMode,actualAt,typeAt,_⟩ := site.references index mode payload formalAt
      have same := Option.some.inj (actualAt.symm.trans argumentAt)
      subst actual
      simp [valRefLike,typeAt,VTy.refLike,Ty.isRefLike]
    | _ => simp [formalAt,Ty.isRefSlice] at reference

theorem typed_refSlice_argument_place {typing : TEnv} {callee : Impl}
    {parameters : List Param} {arguments : List Arg} {start finish index : Nat}
    {parameter : Param} {localVar : LocalVar}
    (typed : tyArgs typing callee parameters arguments start = .ok ((),finish))
    (arity : parameters.length = arguments.length)
    (parameterAt : parameters[index]? = some parameter)
    (mode : parameter.mode = .byRef) (parameterRow : callee.vars[parameter.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true) :
    ∃ mutability place info childStart childFinish,
      arguments[index]? = some (.byRef mutability place) ∧
      tyPlace typing place childStart = .ok (info,childFinish) ∧
      info.ty.isRefLike = true ∧ info.ty.readable = true := by
  have bound : index < arguments.length := arity ▸ (List.getElem?_eq_some_iff.mp parameterAt).1
  let argument := arguments[index]
  have selected : arguments[index]? = some argument := List.getElem?_eq_getElem bound
  have split : arguments = arguments.take index ++ argument :: arguments.drop (index+1) := by
    calc
      arguments = arguments.take index ++ arguments.drop index := (List.take_append_drop index arguments).symm
      _ = _ := by rw [List.drop_eq_getElem_cons bound]
  obtain ⟨earlier, actual, later, childStart, childFinish, parameterSplit, parameterLength,
    _, currentTyped, _⟩ := tyArgs_argument_checkpoint
      (by rw [← split]; exact arity) (by rw [← split]; exact typed)
  have actualAt : parameters[index]? = some actual := by
    rw [parameterSplit, ← List.length_take_of_le (Nat.le_of_lt bound), ← parameterLength]
    simp
  have same : actual = parameter := Option.some.inj (actualAt.symm.trans parameterAt)
  subst actual
  obtain ⟨mutability, place, info, placeFinish, argumentEq, placeTyped, refLike, readable, _⟩ :=
    tyArgs_refSlice_head mode parameterRow reference currentTyped
  exact ⟨mutability,place,info,childStart,placeFinish,argumentEq ▸ selected,placeTyped,refLike,readable⟩

theorem typed_call_local_holder_visible (facts : SourceReadyFunction)
    {typing : TEnv} (tables : SourceRootTables typing facts.source)
    {function : ContextId} {arguments : List Arg} {origin : OriginId} {type : Ty} {start finish : Nat}
    (typed : tyExpr typing (.call function arguments origin) start = .ok (type,finish))
    {callee : Context} {implementation : Impl}
    (contextAt : facts.source.mod.contexts[function]? = some callee)
    (implementationAt : facts.source.mod.impls[callee.impl]? = some implementation)
    {index : Nat}
    (reference : ((lowerContextAt facts.source.mod callee implementation).params[index]?).any Ty.isRefSlice = true)
    {returnTypes : List Ty} {before after : LS} {values : List ValueId} {argument : Nat}
    (bounded : LiveBound before)
    (run : lowerArgs arguments (lowerEnv typing.mod typing.vars returnTypes) before = (values,after))
    (nativeRow : values[index]? = some argument)
    (live : after.cur.isSome = true) (extension : after.Ext facts.completed)
    (nativeReference : valRefLike facts.types argument = true)
    {physicalEnv : PEnv} {physicalPlace : Place}
    (physical : ReadAddressPhysical physicalEnv physicalPlace (rootsAt facts.upper.vals argument))
    {tracked : VarId} (trackedMember : RootRef.local tracked ∈ rootsAt facts.provenance.vals argument) :
    (∃ mode, arguments[index]? = some (.byRef mode (.var tracked))) ∧ tracked ∈ typing.visible := by
  obtain ⟨actualContext, actualImpl, argsStart, argsFinish, resultStart, actualContextAt,
    actualImplAt, arity, argumentsTyped, _⟩ := tyExpr_call_tables typed
  rw [← tables.moduleEq,contextAt] at actualContextAt
  cases Option.some.inj actualContextAt
  rw [← tables.moduleEq,implementationAt] at actualImplAt
  cases Option.some.inj actualImplAt
  obtain ⟨parameter,localVar,parameterAt,parameterRow,mode,parameterReference⟩ :=
    lowerContext_refSlice_parameter_of_accepted facts.accepted implementationAt reference
  obtain ⟨mutability,place,info,childStart,childFinish,sourceRow,placeTyped,refLike,readable⟩ :=
    typed_refSlice_argument_place argumentsTyped arity
      (by simpa only [Array.getElem?_toList] using parameterAt) mode parameterRow parameterReference
  obtain ⟨rfl,visible⟩ := selected_holder_argument_visible facts tables placeTyped readable refLike
    bounded run sourceRow nativeRow live extension nativeReference physical trackedMember
  exact ⟨⟨mutability,sourceRow⟩,visible⟩

#print axioms call_refSlice_argument_reference
#print axioms typed_refSlice_argument_place
#print axioms typed_call_local_holder_visible

end Goose.Lower.Validation.SourceReplacementLexicalWriters
