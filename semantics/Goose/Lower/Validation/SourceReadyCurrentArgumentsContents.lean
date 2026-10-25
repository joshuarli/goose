import Goose.Lower.Validation.SourceReadyInductionFacts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsCheckpoints
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsTypingCheckpoints

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.argument_content (facts : SourceReadyFunction)
    {typingEnv : TEnv} {callee : Core.Impl} {parameters : List Param} {arguments : List Arg}
    {initial : LS} {results : List Ty} {startOffset finishOffset index : Nat}
    {argument : Arg} {value : ValueId} {parameter : Param} {parameterVar : LocalVar}
    {sourceEnv : PEnv} {sourcePlace : Place} {physicalRoots : List RootRef}
    (tables : SourceRootTables typingEnv facts.source)
    (typed : Core.tyArgs typingEnv callee parameters arguments startOffset = .ok ((), finishOffset))
    (arity : parameters.length = arguments.length)
    (sourceRow : arguments[index]? = some argument)
    (parameterAt : parameters[index]? = some parameter)
    (mode : parameter.mode = .byRef)
    (parameterRow : callee.vars[parameter.var]? = some parameterVar)
    (reference : parameterVar.ty.isRefSlice = true)
    (generated : GeneratedBuilderState initial)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (live : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.cur.isSome = true)
    (extension : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext facts.completed)
    (allocated : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ facts.completed.vals.size)
    (visible : VisibleSlotsReady typingEnv facts.state)
    (nativeRow : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).1[index]? = some value)
    (physical : ReadAddressPhysical sourceEnv sourcePlace physicalRoots)
    (below : rootsAt facts.provenance.vals value ⊆ physicalRoots)
    (available : flowAt facts.state.values value ≠ .pending) :
    content facts.func facts.state (flowAt facts.state.values value) ≠ .pending := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  obtain ⟨earlier, later, split, length, selected, advance, prefixLive, childLive⟩ :=
    lowerArgs_argument_checkpoint_live sourceRow env initial live
  obtain ⟨earlierParameters, selectedParameter, laterParameters, childStart, childFinish,
    parameterSplit, parameterLength, _, currentTyped, _⟩ :=
    tyArgs_argument_checkpoint (by rw [← split]; exact arity) (by rw [← split]; exact typed)
  have selectedAt : parameters[index]? = some selectedParameter := by
    rw [parameterSplit, ← length, ← parameterLength]
    simp
  have sameParameter : selectedParameter = parameter := Option.some.inj (selectedAt.symm.trans parameterAt)
  subst selectedParameter
  have sameValue : (lowerArg argument env (lowerArgs earlier env initial).2).1 = value :=
    Option.some.inj (selected.symm.trans nativeRow)
  let child := lowerArg argument env (lowerArgs earlier env initial).2
  have childRun : lowerArg argument env (lowerArgs earlier env initial).2 = (value, child.2) := by
    exact Prod.ext sameValue rfl
  have suffix : (lowerArgs later env child.2).2 = (lowerArgs arguments env initial).2 := by
    rw [split, lowerArgs_append_run]
    rfl
  have childNative : SummaryPreservation.NativeRows facts.types child.2 := by
    apply native.of_prefix
    rw [← suffix]
    exact types_lowerArgs later env child.2 _ _ rfl
  exact facts.frame.current_refSlice_argument_content facts.canonical facts.native.valuesSize
    facts.native.definitions facts.native.quiet facts.growth (facts.readable tables) currentTyped
    mode parameterRow reference (generated.lowerArgs earlier rfl) childRun childNative childLive
    (advance.ext.trans extension) (Nat.le_trans advance.vals allocated) visible
    (facts.sourceSlotSeeds tables) physical below available

#print axioms SourceReadyFunction.argument_content

end Goose.Lower.Validation.ReplacementContentFlowSource
