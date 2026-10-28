import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostRecursivePlaceWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel

private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def value : Expr := .arrLit (.arr (.int .i64) 1) [.lit .i64 7] 0
private def place : Place := .field (.elem (.val value) (.lit .i64 0) 0) 1
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed : ClosedModuleWithTails config := by
  intro contextId context implementation found implemented
  simp [config] at found

private theorem placeSyntax : PlaceSyntax config place := by
  unfold place
  apply PlaceSyntax.field
  apply PlaceSyntax.element
  · apply ViewSyntax.value
    apply ValueSyntax.aggregate value [.lit .i64 7]
    · exact .fixedArray (.arr (.int .i64) 1) [.lit .i64 7] 0 rfl
    · intro operand member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst operand
      exact .base (.integer .i64 7)
  · exact .base (.integer .i64 0)

theorem recursivePlace_history (fuel : Nat) :
    SourceHistory config fuel [] (.place environment place) .initial (evalPlace fuel config environment place .initial) :=
  fuelHistory_exists fuel config _ [] .initial ((syntaxFuel_existsWithTails fuel config closed).place environment place placeSyntax)

theorem recursivePlace_witness :
    SourceHistory config 20 [] (.place environment place) .initial (evalPlace 20 config environment place .initial) ∧
    evalPlace 20 config environment place .initial = .ok ⟨.global 0, [0, 1]⟩ (stepState (evalPlace 20 config environment place .initial)) := by
  refine ⟨recursivePlace_history 20, ?_⟩
  simp only [stepState, config, environment, place, value]
  cbv

private def slice : Expr := .slice .readOnly (.val value) (.expr (.lit .i64 0)) (.fromEnd (.lit .i64 0)) 0

private theorem sliceSyntax : ValueSyntax config slice := by
  unfold slice
  apply ValueSyntax.slice
  · apply ViewSyntax.value
    apply ValueSyntax.aggregate value [.lit .i64 7]
    · exact .fixedArray (.arr (.int .i64) 1) [.lit .i64 7] 0 rfl
    · intro operand member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst operand
      exact .base (.integer .i64 7)
  · exact .expression (.lit .i64 0) (.base (.integer .i64 0))
  · exact .fromEnd (.lit .i64 0) (.base (.integer .i64 0))

theorem recursiveSlice_history (fuel : Nat) :
    SourceHistory config fuel [] (.value environment slice) .initial (evalValue fuel config environment slice .initial) :=
  fuelHistory_exists fuel config _ [] .initial ((syntaxFuel_existsWithTails fuel config closed).value environment slice sliceSyntax)

theorem recursiveSlice_witness :
    SourceHistory config 20 [] (.value environment slice) .initial (evalValue 20 config environment slice .initial) ∧
    evalValue 20 config environment slice .initial = .ok (.slice ⟨.global 0, []⟩ 0 1)
      (stepState (evalValue 20 config environment slice .initial)) := by
  refine ⟨recursiveSlice_history 20, ?_⟩
  simp only [stepState, config, environment, slice, value]
  cbv

#print axioms recursiveSlice_history
#print axioms recursiveSlice_witness
#print axioms recursivePlace_history
#print axioms recursivePlace_witness
end Goose.Proofs.ConstructionGhostRecursivePlaceWitness
