import Goose.Core.DeclarativeTables
import Goose.Lower.Validation.ExpressionTypingCallOps
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsTypingCheckpoints
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsCheckpoints
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

private theorem byValue_parameter_not_reference {module : Core.Module} {callee : Core.Impl}
    (checked : Core.ImplementationTables module callee) {parameter : Param}
    (member : parameter ∈ callee.params.toList) (mode : parameter.mode = .byValue)
    {localVar : LocalVar} (variableRow : callee.vars[parameter.var]? = some localVar)
    (mutability : Mutability) (payload : Ty) : localVar.ty ≠ .ref mutability payload := by
  obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
  have parameterRow : callee.params[index]? = some parameter := by
    simpa only [Array.getElem?_toList] using row
  obtain ⟨identity, found, foundRow, _, shape⟩ := checked.parameters index parameter parameterRow
  have same : found = localVar := by
    rw [← identity] at foundRow
    exact Option.some.inj (foundRow.symm.trans variableRow)
  subst found
  intro reference
  simpa only [mode, reference, Core.ParameterModeType] using shape

private theorem reference_argument_source {typingEnv : TEnv} {callee : Core.Impl}
    {types : Array (Option VTy)} {results : List Ty} {parameters : List Param} {arguments : List Arg}
    {initial : LS} {start finish index value : Nat} {mutability : Mutability} {payload : Ty}
    (checked : Core.ImplementationTables typingEnv.mod callee)
    (members : ∀ parameter ∈ parameters, parameter ∈ callee.params.toList)
    (arity : parameters.length = arguments.length)
    (source : Core.tyArgs typingEnv callee parameters arguments start = .ok ((), finish))
    (generated : GeneratedBuilderState initial)
    (native : NativeRows types (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (live : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.cur.isSome = true)
    (row : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).1[index]? = some value)
    (reference : types[value]? = some (some (.data (.ref mutability payload)))) :
    ∃ borrowed place, arguments[index]? = some (.byRef borrowed place) := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  induction arguments generalizing parameters initial start index with
  | nil => simp [lowerArgs, pure_run] at row
  | cons argument rest ih =>
    cases parameters with
    | nil => simp at arity
    | cons parameter parameters =>
      cases index with
      | zero =>
        have valueEq : (lowerArg argument env initial).1 = value := by
          simpa only [lowerArgs, bind_run, pure_run, List.getElem?_cons_zero, Option.some.injEq] using row
        cases argument with
        | byRef borrowed place => exact ⟨borrowed, place, rfl⟩
        | byVal expression =>
          have mode : parameter.mode = .byValue := by
            cases selected : parameter.mode with
            | byValue => rfl
            | byRef => simp [Core.tyArgs, Core.argMode, selected, chk] at source
          obtain ⟨localVar, actual, childStart, childFinish, restStart, variableRow, typed, passable, _⟩ :=
            tyArgs_byVal_head source
          have childNative := native.of_prefix
            (types_lowerArgs rest env (lowerExpr expression env initial).2 _ _ rfl)
          have childLive := (dead_lowerArgs rest).live_before rfl live
          have tag := childNative.expression generated typed rfl childLive
          have actualEq : actual = .ref mutability payload := by
            change (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) initial).1 = value at valueEq
            rw [valueEq] at tag
            simpa only [Option.some.injEq, VTy.data.injEq] using tag.symm.trans reference
          have forbidden : ∀ borrowed target, localVar.ty ≠ .ref borrowed target :=
            fun borrowed target => byValue_parameter_not_reference checked (members parameter (by simp)) mode
              variableRow borrowed target
          rw [actualEq] at passable
          cases type : localVar.ty <;> first
          | exact False.elim (forbidden _ _ type)
          | simp_all [Ty.passableTo]
      | succ index =>
        obtain ⟨middle, _, remaining⟩ := tyArgs_cons_children source
        apply ih (parameters := parameters) (initial := (lowerArg argument env initial).2)
          (start := middle) (index := index)
        · intro selected member
          exact members selected (by simp [member])
        · simpa using arity
        · exact remaining
        · exact generated.lowerArg argument rfl
        · exact native
        · exact live
        · simpa only [lowerArgs, bind_run, pure_run, List.getElem?_cons_succ] using row

theorem call_reference_argument_is_byRef {typingEnv : TEnv} {callee : Core.Impl}
    {types : Array (Option VTy)} {results : List Ty} {arguments : List Arg}
    {initial : LS} {start finish index value : Nat} {mutability : Mutability} {payload : Ty}
    (checked : Core.ImplementationTables typingEnv.mod callee)
    (arity : callee.params.toList.length = arguments.length)
    (source : Core.tyArgs typingEnv callee callee.params.toList arguments start = .ok ((), finish))
    (generated : GeneratedBuilderState initial)
    (native : NativeRows types (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (live : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.cur.isSome = true)
    (row : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).1[index]? = some value)
    (reference : types[value]? = some (some (.data (.ref mutability payload)))) :
    ∃ borrowed place, arguments[index]? = some (.byRef borrowed place) :=
  reference_argument_source checked (fun _ member => member) arity source generated native live row reference

#print axioms call_reference_argument_is_byRef

end Goose.Lower.Validation.ReplacementContentFlowSource
