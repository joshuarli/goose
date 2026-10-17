import Goose.Lower.Validation.SnapshotContentsModule
namespace Goose.Lower.Validation.SnapshotContentsModuleChecks
open Goose.Core Goose.GIR
private def place : Place := .deref (.ref .readOnly (.var 0))
private def main : Impl :=
  { name := "main", params := #[], results := #[],
    vars := #[⟨"array", .arr (.int .i64) 1, .immutable, 0, 0⟩],
    body := .mk 0 [.letS 0 (.arrLit (.arr (.int .i64) 1) [.lit .i64 0]) 0,
      .expr (.len (.of place)) 0] none, summary := .unknown }
private def module : Core.Module :=
  { files := #["snapshot.goose"], types := #[], globals := #[], impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩] }
private theorem accepted : Core.validate module = .ok () := by cbv
#guard match (lower module).funcs[0]? with
  | some func => func.blocks.toList.any (fun block => block.insts.any (fun inst =>
      match inst with
      | .def value (.snapshot .borrowed _) =>
        (func.valueTypes (lower module))[value]? == some (some (.view .mutable (.int .i64)))
      | _ => false))
  | none => false
example : MutableSnapshotGraphs (lower module) (lowerImpl module main) (cfg_implState module main) :=
  lowerImpl_mutableSnapshotGraphs_of_accepted accepted (index := 0) rfl

example : MutableSnapshotGraphs (lower module)
    (lowerContextAt module ⟨0, "main", [], [], []⟩ main) (cfg_implState module main) :=
  lowerContext_mutableSnapshotGraphs_of_accepted accepted (index := 0) rfl

end Goose.Lower.Validation.SnapshotContentsModuleChecks
