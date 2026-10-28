import Goose.Construct.DestinationTrace

namespace Goose.Proofs.ConstructionStageOperationTrace
open Goose.Construct Goose.Core

theorem stageDestination_success_trace (before after : ConstructionState) (id : DestinationId)
    (executed : stageDestination id before = .ok () after) :
    ∃ row capacity slotBytes receiver,
      before.destinations[id]? = some row ∧ row.progress = .open 0 ∧ row.layout = .limited capacity slotBytes ∧
      row.backing = .direct receiver ∧ row.knownCount = none ∧ row.use = .receiver ∧
      after.events = before.events ++ [.stage id] := by
  simp only [stageDestination, writableDestination_result, bind] at executed
  cases present : before.destinations[id]? with
  | none => simp only [present] at executed; cases executed
  | some row =>
    cases allowed : destinationCanWrite before id with
    | false => simp only [present, allowed] at executed; cases executed
    | true =>
      simp only [present, allowed] at executed
      have inside := (Array.getElem?_eq_some_iff.mp present).1
      cases progress : row.progress with
      | «open» count =>
        cases count with
        | succ count => simp [progress, ConstructionM.fail] at executed
        | zero =>
          cases layout : row.layout <;> cases backing : row.backing <;>
            cases known : row.knownCount <;> cases use : row.use <;>
            simp_all only [ConstructionM.fail, reduceCtorEq]
          all_goals
            simp_all [reserveStorage, ConstructionM.get, ConstructionM.set, bind, pure,
              replaceDestination_result, emit_result, ConstructionM.fail]
            rw [← executed]
      | built count | published count | attached count | suspended count child | exiting count child =>
        simp [progress, ConstructionM.fail] at executed
      | abandoned | cancelled | retired => simp [progress, ConstructionM.fail] at executed

private def stagedConstruction : ConstructionM Unit := do
  let storage ← reserveStorage
  let destination ← openDestinationDirect storage
    ⟨0, ⟨.local 0 0 0, []⟩, .varr (.int .u8), .varr (.int .u8), .elementRun, 0, 0⟩
    (.limited 4 1) none
  stageDestination destination

theorem stageDestination_realizable :
    ∃ state, stagedConstruction .initial = .ok () state ∧ state.events = [.begin 0, .stage 0] := by
  refine ⟨(stagedConstruction .initial).finalState, ?_, ?_⟩ <;> unfold stagedConstruction <;> cbv

#print axioms stageDestination_realizable
#print axioms stageDestination_success_trace

end Goose.Proofs.ConstructionStageOperationTrace
