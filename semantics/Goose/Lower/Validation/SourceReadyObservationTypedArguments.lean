import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReferences
import Goose.Lower.Validation.SourceReadyObservationAccess
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyLists
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsCheckpoints
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsTypingCheckpoints
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyArgumentObservations

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

private theorem arguments_ready {module : GIR.Module} {func : Func} (state : State)
    (arguments : List Arg) (env : LEnv) (initial : LS)
    (step : ∀ earlier argument suffix, arguments = earlier ++ argument :: suffix →
      ValueReadyAt state (lowerArg argument) env (lowerArgs earlier env initial).2 ∧
      EmitsOnly (ReadyCallObservations module func state) (lowerArgs earlier env initial).2
        (lowerArg argument env (lowerArgs earlier env initial).2).2) :
    ValuesReadyAt state (lowerArgs arguments) env initial ∧
      EmitsOnly (ReadyCallObservations module func state) initial (lowerArgs arguments env initial).2 := by
  induction arguments generalizing initial with
  | nil => exact ⟨⟨.refl _ _, by simp [lowerArgs, pure_run]⟩, .refl _ _⟩
  | cons argument rest ih =>
    have first := step [] argument rest rfl
    simp only [lowerArgs, pure_run] at first
    have tail := ih (lowerArg argument env initial).2 (by
      intro earlier child suffix split
      have selected := step (argument :: earlier) child suffix (by simp [split])
      simpa only [lowerArgs, bind_run, pure_run] using selected)
    refine ⟨⟨?_, ?_⟩, ReadyCallObservations.argumentsCons argument rest first.2 tail.2⟩
    · exact first.1.1.trans tail.1.1
    · intro live value member
      simp only [lowerArgs, bind_run, pure_run] at live member
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact first.1.2 ((dead_lowerArgs rest).live_before rfl live)
      · exact tail.1.2 live value later

variable {module : GIR.Module} {callees : Array State} {func : Func}
  {types : Array (Option VTy)} {state : State} {completed initial : LS}
  {typingEnv : TEnv} {results : List Ty} {start finish : Nat}

theorem typedArgument (frame : SourceReadyFrame module callees func types state completed)
    (argument : Arg) (source : ArgumentTyping typingEnv argument start finish)
    (generated : GeneratedBuilderState initial)
    (native : NativeRows types (lowerArg argument (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (extension : (lowerArg argument (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed)
    (allocated : (lowerArg argument (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (expressionChild : ∀ expression, argument = .byVal expression → ∀ type childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (type, childFinish) →
      GeneratedBuilderState initial →
      NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) initial) ∧
      EmitsOnly (ReadyCallObservations module func state) initial
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (placeChild : ∀ mutability place, argument = .byRef mutability place → ∀ info childStart childFinish,
      Core.tyPlace typingEnv place childStart = .ok (info, childFinish) →
      GeneratedBuilderState initial →
      NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) initial) ∧
      EmitsOnly (ReadyCallObservations module func state) initial
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) initial).2) :
    ValueReadyAt state (lowerArg argument) (lowerEnv typingEnv.mod typingEnv.vars results) initial ∧
      EmitsOnly (ReadyCallObservations module func state) initial
        (lowerArg argument (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  cases argument with
  | byVal expression =>
    obtain ⟨type, typed⟩ := source
    have child := expressionChild expression rfl type start finish typed generated native extension allocated visible
    exact ⟨child.1, ReadyCallObservations.argumentValue expression child.2⟩
  | byRef mutability place =>
    obtain ⟨info, typed⟩ := source
    let addressed := lowerPlace place env initial
    let borrowed := Lower.borrowTo mutability addressed.1 env addressed.2
    have whole : lowerArg (.byRef mutability place) env initial = borrowed := rfl
    have tailAdvance : addressed.2.Adv borrowed.2 := advB_borrowTo mutability addressed.1 env addressed.2 _ _ rfl
    change NativeRows types (lowerArg (.byRef mutability place) env initial).2 at native
    change (lowerArg (.byRef mutability place) env initial).2.Ext completed at extension
    change (lowerArg (.byRef mutability place) env initial).2.vals.size ≤ completed.vals.size at allocated
    rw [whole] at native extension allocated
    have child := placeChild mutability place rfl info start finish typed generated
      (native.of_prefix (types_borrowTo mutability addressed.1 env addressed.2 _ _ rfl))
      (tailAdvance.ext.trans extension) (Nat.le_trans tailAdvance.vals allocated) visible
    refine ⟨frame.argumentReference (show lowerPlace place env initial = addressed from rfl)
      (show lowerArg (.byRef mutability place) env initial = borrowed from whole)
      extension allocated (generated.lowerPlace place rfl).live child.1, ?_⟩
    exact ReadyCallObservations.argumentReference mutability place child.2

theorem typedArguments (frame : SourceReadyFrame module callees func types state completed)
    {callee : Core.Impl} {parameters : List Param} {arguments : List Arg}
    (source : Core.tyArgs typingEnv callee parameters arguments start = .ok ((), finish))
    (arity : parameters.length = arguments.length)
    (generated : GeneratedBuilderState initial)
    (native : NativeRows types (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2)
    (extension : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.Ext completed)
    (allocated : (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2.vals.size ≤ completed.vals.size)
    (visible : VisibleSlotsReady typingEnv state)
    (expressionChild : ∀ earlier expression later, arguments = earlier ++ .byVal expression :: later →
      ∀ type childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (type, childFinish) →
      let before := (lowerArgs earlier (lowerEnv typingEnv.mod typingEnv.vars results) initial).2
      GeneratedBuilderState before →
      NativeRows types (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        ((lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (placeChild : ∀ earlier mutability place later, arguments = earlier ++ .byRef mutability place :: later →
      ∀ info childStart childFinish,
      Core.tyPlace typingEnv place childStart = .ok (info, childFinish) →
      let before := (lowerArgs earlier (lowerEnv typingEnv.mod typingEnv.vars results) initial).2
      GeneratedBuilderState before →
      NativeRows types (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ completed.vals.size →
      VisibleSlotsReady typingEnv state →
      (ValueReadyAt state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before) ∧
      EmitsOnly (ReadyCallObservations module func state) before
        ((lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    ValuesReadyAt state (lowerArgs arguments) (lowerEnv typingEnv.mod typingEnv.vars results) initial ∧
      EmitsOnly (ReadyCallObservations module func state) initial
        (lowerArgs arguments (lowerEnv typingEnv.mod typingEnv.vars results) initial).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  change NativeRows types (lowerArgs arguments env initial).2 at native
  change (lowerArgs arguments env initial).2.Ext completed at extension
  change (lowerArgs arguments env initial).2.vals.size ≤ completed.vals.size at allocated
  apply arguments_ready state arguments env initial
  intro earlier argument later split
  obtain ⟨earlierParameters, parameter, laterParameters, childStart, childFinish,
    _, _, childSource, _, _⟩ := tyArgs_argument_checkpoint
      (by rw [← split]; exact arity) (by rw [← split]; exact source)
  let before := (lowerArgs earlier env initial).2
  let child := lowerArg argument env before
  have suffix : (lowerArgs later env child.2).2 = (lowerArgs arguments env initial).2 := by
    rw [split, lowerArgs_append_run]
    rfl
  have advance : child.2.Adv (lowerArgs arguments env initial).2 := by
    rw [← suffix]
    exact advB_lowerArgs later env child.2 _ _ rfl
  have childNative : NativeRows types child.2 := by
    apply native.of_prefix
    rw [← suffix]
    exact types_lowerArgs later env child.2 _ _ rfl
  apply typedArgument frame argument childSource (generated.lowerArgs earlier rfl) childNative
    (advance.ext.trans extension) (Nat.le_trans advance.vals allocated) visible
  · intro expression same type expressionStart expressionFinish typed generated native extension allocated visible
    exact expressionChild earlier expression later (by simpa only [same] using split)
      type expressionStart expressionFinish typed generated native extension allocated visible
  · intro mutability place same info placeStart placeFinish typed generated native extension allocated visible
    exact placeChild earlier mutability place later (by simpa only [same] using split)
      info placeStart placeFinish typed generated native extension allocated visible

#print axioms typedArgument
#print axioms typedArguments

end Goose.Lower.Validation.ReplacementContentFlowSource.SourceReadyArgumentObservations
