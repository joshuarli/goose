import Goose.Proofs.ConstructionGhostMaterializedGlobalEvents

namespace Goose.Proofs.ConstructionGhostMaterializedGlobalEventsWitness
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostMaterializedGlobalEvents

private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def element : Expr := .len (.val bytes)
private def expression : Expr := .values [.arrLit (.arr (.int .i64) 1) [element] 0]
private def global : Global := ⟨"g", .varr (.int .i64), .immutable, expression, 0⟩
private def context : Context := ⟨0, "entry", [], [], []⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[global], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def ready : ExecutionState := { ExecutionState.initial with nextAct := 1 }
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem supported : FuelSupport config 38 (.value environment expression) := by
  apply FuelSupport.legacy
  apply SupportedOperation.singleton environment (.arrLit (.arr (.int .i64) 1) [element] 0)
  apply SupportedOperation.aggregate environment (.arrLit (.arr (.int .i64) 1) [element] 0) [element]
    (.fixedArray (.arr (.int .i64) 1) [element] 0 rfl)
  intro operand member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst operand
  exact .lengthValue environment (.val bytes) (.valueView environment bytes (.valueBytes environment (.varr (.int .u8)) [65, 66] 0))

theorem materializedGlobal_sourceEvents : ∃ after visits,
    OperandReplay (globalInitializer 38 config) 0 [0] [] .initial (.ok [()] after) visits ∧
    (∃ visit ∈ visits,
      SourceHistory config 38 [visit.ordinal, 0] (.value environment expression) ready
        (evalValue 38 config environment expression ready) ∧
      Goose.Proofs.ConstructionExecution.EventPrefix
        (Goose.Proofs.Exit.stepState (evalValue 38 config environment expression ready)).construction.events
        (Goose.Proofs.Exit.stepState visit.outcome).construction.events) ∧
    (Goose.Proofs.Exit.stepState (evalValue 38 config environment expression ready)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  let after := stepState (globalInitializer 38 config 0 .initial)
  have actual : globalInitializer 38 config 0 .initial = .ok () after := by
    unfold after stepState globalInitializer config global context implementation expression element bytes
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  have sourceEvents : (Goose.Proofs.Exit.stepState (evalValue 38 config environment expression ready)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
    unfold config environment ready expression element bytes global context implementation
    unfold evalValue
    cbv
    unfold evalValue
    cbv
  let visit : Invocation Goose.Core.GlobalId Unit := ⟨0, 0, .initial, .ok () after⟩
  have replay : OperandReplay (globalInitializer 38 config) 0 [0] [] .initial (.ok [()] after) [visit] :=
    .next actual (.done 1 [()] after)
  have count : ordinaryProducerCount? 38 ⟨config.module, #[]⟩ expression = some 1 := by
    unfold config expression element bytes global context implementation
    cbv
  obtain ⟨history, initial, retained⟩ := materializedGlobal_visit_sourceEvents replay visit (by simp [visit]) global 1 rfl rfl count supported
  exact ⟨after, [visit], replay, ⟨visit, by simp, history, retained⟩, sourceEvents⟩

#print axioms materializedGlobal_sourceEvents
end Goose.Proofs.ConstructionGhostMaterializedGlobalEventsWitness
