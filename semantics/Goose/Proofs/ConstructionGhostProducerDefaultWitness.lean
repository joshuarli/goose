import Goose.Proofs.ConstructionGhostProducerDefault

namespace Goose.Proofs.ConstructionGhostProducerDefaultWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostScalarProducer
open Goose.Proofs.ConstructionGhostProducerDefault

private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def items : List Expr := [.lit .u8 65, .lit .u8 66]
private def array : Expr := .arrLit (.arr (.int .u8) 2) items 0
private def expression : Expr := .len (.val array)
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed : ClosedModuleWithTails config := by
  intro id actualContext actualImplementation found implemented
  cases id with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using found.symm
      subst actualContext
      have implEq : actualImplementation = implementation := by simpa [config, context] using implemented.symm
      subst actualImplementation
      exact ⟨0, [], none, rfl, by simp, .none⟩
  | succ n => simp [config] at found

private theorem source : ValueSyntax config expression := by
  apply ValueSyntax.length
  apply ViewSyntax.value
  apply ValueSyntax.aggregate array items (.fixedArray _ _ _ rfl)
  intro operand member
  simp only [items, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .base (.integer .u8 65)
  · exact .base (.integer .u8 66)

theorem length_history (fuel : Nat) :
    SourceHistory config fuel [] (.producerWith environment [.register (.int .i64)] expression) .initial
      (evalProduce fuel config environment [.register (.int .i64)] expression .initial) :=
  defaultProducer_history fuel config closed environment [.register (.int .i64)] expression .initial (.length _) source

theorem length_actual :
    evalProduce 40 config environment [.register (.int .i64)] expression .initial =
      .ok [.register (.int .i64 2)] (stepState (evalProduce 40 config environment [.register (.int .i64)] expression .initial)) := by
  simp only [stepState, config, context, implementation, environment, expression, array, items]
  cbv

#print axioms length_history
#print axioms length_actual
end Goose.Proofs.ConstructionGhostProducerDefaultWitness
