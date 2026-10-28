import Goose.Proofs.ConstructionAcceptedScalarParameterList
import Goose.Proofs.ConstructionAcceptedVisibleFrame

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def advanceParameterFrames (frame : ConstructionSourceFrame) (start : Nat) : Nat → ConstructionSourceFrame
  | 0 => frame
  | count + 1 => advanceParameterFrames (advanceLocalFrame frame start) (start + 1) count

theorem advanceParameterFrames_facts (frame : ConstructionSourceFrame) (start count : Nat) :
    (advanceParameterFrames frame start count).typingCounter = frame.typingCounter + count ∧
    (advanceParameterFrames frame start count).rootCursor.nextVar = frame.rootCursor.nextVar + count ∧
    (advanceParameterFrames frame start count).typing.visible = (List.range' start count).reverse ++ frame.typing.visible ∧
    (advanceParameterFrames frame start count).interpretation = frame.interpretation ∧
    (advanceParameterFrames frame start count).initialized = frame.initialized := by
  induction count generalizing frame start with
  | zero => simp [advanceParameterFrames]
  | succ count ih =>
    have facts := ih (advanceLocalFrame frame start) (start + 1)
    simp only [advanceParameterFrames] at ⊢
    simp only [advanceLocalFrame] at facts
    simp only [List.range'_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    obtain ⟨counter, root, visible, interpretation, initialized⟩ := facts
    refine ⟨?_, ?_, ?_, interpretation, initialized⟩
    · simpa [advanceLocalFrame, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using counter
    · simpa [advanceLocalFrame, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using root
    · exact visible

theorem advanceParameterFrames_canonicalVisible {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (start count : Nat) (source : AcceptedFrame config accepted (advanceParameterFrames frame start count) state types) :
    AcceptedFrame config accepted
      { advanceParameterFrames frame start count with typing := {
        (advanceParameterFrames frame start count).typing with visible :=
          (List.range' start count ++ frame.typing.visible) } } state types := by
  apply source.withVisibleSubset
  intro id member
  rw [(advanceParameterFrames_facts frame start count).2.2.1]
  simp only [List.mem_append, List.mem_reverse] at member ⊢
  exact member

#print axioms advanceParameterFrames_facts
#print axioms advanceParameterFrames_canonicalVisible
end Goose.Proofs.ConstructionAcceptedExecution
