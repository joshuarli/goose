import Goose.Proofs.ExitExecutionChecks

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecutionChecks

def publishedBranchReturn : Module := Id.run do
  let owner : Ty := .varr (.int .u8)
  let entry : Impl := ⟨"entry", #[], #[], #[⟨"v", owner, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none, .unknown⟩
  let producer : Impl := ⟨"producer", #[], #[⟨owner, .value, none⟩], #[⟨"x", owner, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.bytes owner [65] 0) 0,
      .ifS (.bool true) (.mk 1 [.retValues [.resultLocal 0 0] 0] none)
        (some (.mk 2 [.retValues [.copy owner (.var 0) 0] 0] none)) 0] none, .unknown⟩
  return ⟨#["published-local.goose"], #[.int .u8, owner], #[], #[entry, producer],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "producer", [], [[]], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

theorem published_branch_return_validated : validate publishedBranchReturn = .ok () := by cbv

theorem published_branch_return_execution :
    returnedObservation (eval 200 .release publishedBranchReturn) =
      some ([65, 10], [.begin 0, .begin 1, .write 1 0, .publish 1, .copy (.storage 1 []) 0, .write 0 0, .publish 0]) := by cbv

theorem published_branch_return_unnamed :
    (publishedBranchReturn.impls[1]?).map (fun implementation => implementation.results.toList.map (·.namedLocal)) =
      some [none] := by cbv

#print axioms published_branch_return_validated
#print axioms published_branch_return_execution
#print axioms published_branch_return_unnamed

end Goose.Proofs.ConstructionAcceptedExecution
