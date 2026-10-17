import Goose.Lower.Validation.SourceReadyCheckCallsBounds
import Goose.Lower.Validation.SourceReadyCheckCallsInputs
import Goose.Lower.Validation.SourceReadyInductionFacts
import Goose.Lower.Validation.SourceReadyObservations
import Goose.Lower.Validation.AdmittedSourceCallsObserved

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow SummaryPreservation
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.check_call (facts : SourceReadyFunction)
    {block : GIR.Block} {value calleeId : Nat} {arguments : List ValueId} {origin : Option OriginId}
    {callee : Func}
    (member : block ∈ facts.func.blocks.toList)
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    (calleeAt : (lower facts.source.mod).funcs[calleeId]? = some callee)
    (occurrence : CallOccurrence facts.source facts.root facts.func facts.upper value calleeId arguments origin)
    (available : CallObservationReady callee facts.func facts.state arguments) :
    Model.checkCall (lower facts.source.mod) facts.func facts.state calleeId arguments = true := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, sourceRoots, argumentsAfter,
    returned, after, access, _, _, replayed, contentsChecked, callReplayed, _, _, argumentOrigins, _, trace⟩ := occurrence
  have moduleEq : localEnv.mod = facts.source.mod := congrArg AccessEnv.mod access
  have accepted : Core.validate localEnv.mod = .ok () := by simpa only [moduleEq] using facts.accepted
  obtain ⟨context, impl, contextAt, implAt, checkedArguments, _, _⟩ :=
    rpCall_ok localEnv calleeId sourceRoots argumentsAfter returned after callReplayed
  have contextRow : facts.source.mod.contexts[calleeId]? = some context := by
    simpa only [moduleEq] using contextAt
  have implementationRow : facts.source.mod.impls[context.impl]? = some impl := by
    simpa only [moduleEq] using implAt
  let nativeCallee := lowerContextAt facts.source.mod context impl
  have nativeCalleeAt : (lower facts.source.mod).funcs[calleeId]? = some nativeCallee :=
    lower_func_at contextRow implementationRow
  have calleeEq : callee = nativeCallee := Option.some.inj (calleeAt.symm.trans nativeCalleeAt)
  subst callee
  have calleeFacts := facts.moduleFacts.functions calleeId nativeCallee nativeCalleeAt
  have parameterCount : nativeCallee.params.length = impl.params.size := by
    simp only [nativeCallee, lowerContextAt, lowerImpl, lowerImplFromState, List.length_map, Array.length_toList]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, typingEnv, start, finish, type,
    typingModule, typingVariables, typedCall⟩ := trace
  obtain ⟨typedContext, typedImpl, argsStart, argsFinish, _, typedContextAt, typedImplAt, arity, typedArgs, _⟩ :=
    tyExpr_call_tables typedCall
  rw [typingModule, contextAt] at typedContextAt
  cases Option.some.inj typedContextAt
  rw [typingModule, implAt] at typedImplAt
  cases Option.some.inj typedImplAt
  have tables : SourceRootTables typingEnv localEnv := ⟨typingModule.symm, typingVariables.symm⟩
  have sourceArity : syntaxArgs.length = impl.params.size := by simpa only [Array.length_toList] using arity.symm
  have rootCount : sourceRoots.length = syntaxArgs.length := AdmittedSourceCalls.rpArgs_length replayed
  have parameterRows (index : Nat) (bounded : index < impl.params.size) :
      ∃ parameter localVar, impl.params[index]? = some parameter ∧
        impl.vars[parameter.var]? = some localVar ∧ nativeCallee.params[index]? = some localVar.ty := by
    let parameter := impl.params[index]
    have parameterAt : impl.params[index]? = some parameter := by simp [parameter, bounded]
    obtain ⟨aligned, localVar, variableAt, _, _⟩ :=
      (validate_modOk facts.source.mod facts.accepted).impl context.impl impl implementationRow |>.params index parameter parameterAt
    have variableRow : impl.vars[parameter.var]? = some localVar := by simpa only [aligned] using variableAt
    exact ⟨parameter, localVar, parameterAt, variableRow,
      lowerContext_parameter_type (module := facts.source.mod) (ctx := context) parameterAt variableRow⟩
  have actualWithin (index argument : Nat) (actual : List RootRef)
      (argumentAt : arguments[index]? = some argument)
      (known : normalize facts.func (flowAt facts.state.values argument) = some actual) :
      actual ⊆ (sourceRoots[index]?.getD []).flatMap facts.func.expandParameterRoot := by
    obtain ⟨_, roots, rootsAt, refined⟩ := argumentOrigins index argument argumentAt
    have bounded : argument < facts.func.numValues := facts.native.uses block member _ called argument
      (by simpa only [Inst.uses, Op.uses] using List.mem_of_getElem? argumentAt)
    have within := normalized_argument_source_bound facts.canonical facts.native.roots.closed bounded
      (facts.below argument) refined known
    simpa only [rootsAt, Option.getD_some] using within
  let argumentModels := fun (index : Nat) => arguments[index]?.bind fun argument =>
    normalize facts.func (flowAt facts.state.values argument)
  have parameterAdmission (index : Nat) (bounded : index < impl.params.size) :
      ∃ bound, admittedArgumentBound nativeCallee argumentModels index = some bound ∧
        bound.covers (some ((sourceRoots[index]?.getD []).flatMap facts.func.expandParameterRoot)) = true := by
    obtain ⟨parameter, localVar, parameterAt, variableAt, nativeType⟩ := parameterRows index bounded
    obtain ⟨argument, actual, argumentAt, known⟩ := available.arguments index (by rwa [parameterCount])
    have modelAt : argumentModels index = some actual := by simp only [argumentModels, argumentAt, Option.bind_some, known]
    by_cases reference : localVar.ty.isRefLike = true
    · have admission := accepted_reference_argument_admission (caller := facts.func)
        accepted contextAt implAt parameterAt variableAt reference (checkedArguments index bounded) modelAt
      simpa only [moduleEq] using admission
    · have scalar : localVar.ty.isRefLike = false := Bool.eq_false_iff.mpr reference
      have empty := sourceScalarArgRoots tables impl.params.toList typedArgs replayed
        (by simpa only [Array.getElem?_toList] using parameterAt) variableAt scalar
      obtain ⟨bound, found, covered⟩ := admitted_scalar_argument_empty nativeType scalar modelAt
      exact ⟨bound, found, by simpa only [empty, List.flatMap_nil] using covered⟩
  simp only [Model.checkCall, nativeCalleeAt]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    rintro ⟨parameterType, index⟩ present
    have formalAt : nativeCallee.params[index]? = some parameterType := List.mem_zipIdx_iff_getElem?.mp present
    have bounded : index < impl.params.size := by
      rw [← parameterCount]
      exact (List.getElem?_eq_some_iff.mp formalAt).1
    by_cases reference : parameterType.isRefLike = true
    · simp only [reference, Bool.not_true, Bool.false_eq_true, reduceIte]
      obtain ⟨argument, actual, argumentAt, known⟩ := available.arguments index (by rwa [parameterCount])
      obtain ⟨parameter, localVar, parameterAt, variableAt, nativeType⟩ := parameterRows index bounded
      have permitted := accepted_parameter_query_permitted (caller := facts.func)
        accepted contextAt implAt bounded (checkedArguments index bounded) (actualWithin index argument actual argumentAt known)
      simp only [moduleEq] at permitted
      simp only [argumentAt, known, Option.any_some]
      apply Eq.trans ?_ permitted
      apply congrArg (fun suffix => (nativeCallee.parameterRoots index).contains (.param index) || suffix)
      apply congrArg (fun predicate => actual.all predicate)
      funext root
      cases root <;> rfl
    · have scalar : parameterType.isRefLike = false := Bool.eq_false_iff.mpr reference
      simp [scalar]
  · apply List.all_eq_true.mpr
    rintro ⟨index, declared⟩ row
    have annotation := content_row_lookup calleeFacts.roots.unique row
    obtain ⟨mapped, mapping, _⟩ := AdmittedSourceCalls.checkContents_native_row_receiver_bounds
      facts.accepted contextRow implementationRow moduleEq contentsChecked sourceArity row
    obtain ⟨input, inputAt, covered⟩ := contentInputBound_covers_source_mapping (caller := facts.func) mapping (by
      intro parameter included
      obtain ⟨roots, rootsAt, _⟩ := (mapResultRoots_ok sourceRoots declared [] mapped mapping).2 (.param parameter) included
      have bounded : parameter < impl.params.size := by
        have rootBound := (List.getElem?_eq_some_iff.mp rootsAt).1
        omega
      exact parameterAdmission parameter bounded)
    obtain ⟨argument, actual, argumentAt, known, within⟩ := call_content_source_bound
      facts.native facts.canonical member called nativeCalleeAt calleeFacts.roots annotation mapping (by
        intro parameter argument roots included argumentAt rootsAt
        obtain ⟨_, selected, selectedAt, refined⟩ := argumentOrigins parameter argument argumentAt
        have same : selected = roots := Option.some.inj (selectedAt.symm.trans rootsAt)
        subst selected
        exact refined.actual_mono (facts.below argument)) available
    have admitted := ContentInputBound.covers_subset covered within
    simpa only [argumentModels, argumentAt, inputAt, known] using admitted

theorem SourceReadyFunction.check_call_observed (facts : SourceReadyFunction)
    {block : GIR.Block} {value calleeId : Nat} {arguments : List ValueId} {origin : Option OriginId}
    (member : block ∈ facts.func.blocks.toList)
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts)
    (observed : ReadyCallObservations (lower facts.source.mod) facts.func facts.state
      (.def value (.call calleeId arguments origin))) :
    Model.checkCall (lower facts.source.mod) facts.func facts.state calleeId arguments = true := by
  obtain ⟨site⟩ := facts.native.calls block member value calleeId arguments origin called
  have occurrence := (facts.occurrences block member _ called).2.2.1 value calleeId arguments origin rfl
  exact facts.check_call member called site.calleeAt occurrence
    (observed value calleeId arguments origin rfl site.callee site.calleeAt)

end Goose.Lower.Validation.ReplacementContentFlowSource
