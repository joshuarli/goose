import Goose.Proofs.ConstructionAcceptedOwnerLineage
import Goose.Proofs.ConstructionByteOwnerInitialization

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def byteOwner (bytes : List UInt8) : Option (Nat × Nat × Option Nat) := Id.run do
  let module := Goose.Proofs.ConstructionRepresentation.byteOwnerModule []
  let config : EvalConfig := ⟨.release, module⟩
  let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
  let action : EvalM (Nat × Nat × Option Nat) := do
    let destination ← newDestination config.layout environment.act (.varr (.int .u8)) .value 0 none (some bytes.length)
    buildExpr 5 config environment destination (.bytes (.varr (.int .u8)) bytes 0)
    publishCarriers 0 [.completed destination]
    let stored ← storedDestination destination
    pure (destination, stored.storage, stored.destination)
  match action .initial with
  | .ok result _ => return some result
  | _ => return none

#guard byteOwner [] == some (0, 0, some 0)
#guard byteOwner [1, 2, 3] == some (0, 0, some 0)

private def distinctOriginDeclaration : Option (Nat × Nat × Nat) := Id.run do
  let module := Goose.Proofs.ConstructionRepresentation.byteOwnerModule []
  let config : EvalConfig := ⟨.release, module⟩
  let vars : Array LocalVar := #[⟨"owner", .varr (.int .u8), .mutable, 0, 0⟩]
  let environment : RuntimeActivation := ⟨0, 0, vars, [(0, 0)], []⟩
  let statement : Stmt := .letS 0 (.bytes (.varr (.int .u8)) [1, 2, 3] 1) 2
  match execStmt 10 config environment statement .initial with
  | .ok (.normal .unit) state =>
    match state.objects.lookup (.local 0 0 0) with
    | some (.stored stored) =>
      match sampledStored stored state with
      | .ok (_, run) _ => return some (stored.storage, run.count, run.byteStart)
      | _ => return none
    | _ => return none
  | _ => return none

#guard distinctOriginDeclaration == some (0, 3, 4)

end Goose.Proofs.ConstructionAcceptedExecution
