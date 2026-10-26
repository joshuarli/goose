import Goose.Construct.Validate
import Goose.Construct.Eval

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence.StaticBoundary
open Goose.Construct
open Goose.Core (RootInst)

private def slice : Ty := .slice .readOnly (.int .u8)

private def helper : Impl :=
  ⟨"first-byte", #[⟨0, .byValue⟩], #[⟨.int .u8, .register, none⟩],
    #[⟨"bytes", slice, .immutable, 0, 0⟩],
    .mk 0 [] (some (.read (.elem (.val (.read (.var 0))) (.lit .i64 0) 0))),
    .known ⟨[.param 0], [], [], [], [], [], [], [], true, false⟩⟩

private def argument : Arg := .byVal (.bytes slice [65] 0)

private def entry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [.print [.expr (.call 1 [argument] 0)] 0] none, .unknown⟩

private def program : Module :=
  ⟨#["static-parameter.goose"], #[.int .u8, slice], #[], #[entry, helper],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "first-byte", [(0, [.param 0])], [[]], []⟩],
    0, #[⟨0, 17, "call"⟩], #[], #[]⟩

private def stdout : Option (List UInt8) :=
  match eval 64 .release program with
  | .done .returned output _ => some output.data.toList
  | _ => none

private def argumentRoot : Option RootInst :=
  match evalArguments 32 ⟨.release, program⟩ ⟨0, 0, #[], [(0, 0)], []⟩ helper.vars helper.params.toList [argument]
      { ExecutionState.initial with nextAct := 1, nextScope := 1 } with
  | .ok [.slice location _ _] _ => some location.root
  | _ => none

theorem static_parameter_read_validated : validate program = .ok () := by cbv

theorem static_parameter_read_runs : stdout = some [54, 53, 10] := by cbv

theorem static_argument_uses_synthetic_global :
    program.globals.size = 0 ∧ argumentRoot = some (.global 1) := by cbv

end Goose.Proofs.ConstructionRootCorrespondence.StaticBoundary
