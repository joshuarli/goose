import Goose.Lower.Validation.SourceReadyCurrentArgumentsContents
import Goose.Lower.Validation.SourceReadyCallPhysical
import Goose.Lower.Validation.SourceCanonicalFactsParameters

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.call_contents (facts : SourceReadyFunction)
    {typingEnv : TEnv} {calleeId : ContextId} {callee : Context} {implementation : Impl}
    {syntaxArgs : List Arg} {initial : LS} {results : List Ty} {startOffset finishOffset : Nat}
    {value : ValueId} {origin : Option OriginId}
    (tables : SourceRootTables typingEnv facts.source)
    (calleeRow : facts.source.mod.contexts[calleeId]? = some callee)
    (implementationRow : facts.source.mod.impls[callee.impl]? = some implementation)
    (typed : Core.tyArgs typingEnv implementation implementation.params.toList syntaxArgs startOffset = .ok ((), finishOffset))
    (arity : implementation.params.toList.length = syntaxArgs.length)
    (generated : GeneratedBuilderState initial)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (extension : (lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext facts.completed)
    (allocated : (lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ facts.completed.vals.size)
    (visible : VisibleSlotsReady typingEnv facts.state)
    (ready : ValuesReadyAt facts.state (lowerArgs syntaxArgs) (lowerEnv typingEnv.mod typingEnv.vars results) initial)
    (occurrence : CallOccurrence facts.source facts.root facts.func facts.upper value calleeId
      (lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) initial).1 origin) :
    let lowered := lowerArgs syntaxArgs (lowerEnv typingEnv.mod typingEnv.vars results) initial
    lowered.2.cur.isSome = true → ∀ index argument,
      ((lowerContextAt facts.source.mod callee implementation).roots.contents.find? (·.1 == index)).isSome = true →
      lowered.1[index]? = some argument → content facts.func facts.state (flowAt facts.state.values argument) ≠ .pending := by
  dsimp only
  intro live index argument observed nativeRow
  have calleeFacts := facts.moduleFacts.functions calleeId _ (lower_func_at calleeRow implementationRow)
  obtain ⟨ceiling, found⟩ : ∃ ceiling,
      (lowerContextAt facts.source.mod callee implementation).roots.contents.find? (·.1 == index) = some (index, ceiling) := by
    cases found : (lowerContextAt facts.source.mod callee implementation).roots.contents.find? (·.1 == index) with
    | none => simp [found] at observed
    | some entry =>
      have listFound := found
      rw [← Array.find?_toList] at listFound
      obtain ⟨key, ceiling⟩ := entry
      have same : key = index := by simpa using List.find?_some listFound
      subst key
      exact ⟨ceiling, rfl⟩
  have reference := calleeFacts.roots.contentTypes index ceiling found
  obtain ⟨parameter, parameterVar, parameterAt, parameterRow, mode, parameterReference⟩ :=
    lowerContext_refSlice_parameter_of_accepted facts.accepted implementationRow reference
  have bounded : index < syntaxArgs.length := by
    rw [← arity, Array.length_toList]
    exact (Array.getElem?_eq_some_iff.mp parameterAt).1
  let syntaxArgument := syntaxArgs[index]
  have sourceRow : syntaxArgs[index]? = some syntaxArgument := by simp [syntaxArgument, bounded]
  obtain ⟨localEnv, place, physical⟩ := facts.call_argument_physical calleeRow implementationRow
    occurrence nativeRow observed
  exact facts.argument_content tables typed arity sourceRow
    (by simpa only [Array.getElem?_toList] using parameterAt) mode parameterRow parameterReference
    generated native live extension allocated visible nativeRow physical (facts.below argument)
    (ready.2 live argument (List.mem_of_getElem? nativeRow))

#print axioms SourceReadyFunction.call_contents

end Goose.Lower.Validation.ReplacementContentFlowSource
