import Goose.Construct.Validate
import Goose.Construct.Eval
set_option Elab.async false
namespace Goose.Proofs.ConstructionRootCorrespondence.ContentBoundary
open Goose.Construct
private def slice : Ty := .slice .readOnly (.int .i64)
private def owner : Ty := .arr (.int .i64) 1
private def helper : Impl :=
  ⟨"read-holder", #[⟨0, .byRef⟩, ⟨1, .byRef⟩], #[⟨slice, .register, none⟩],
    #[⟨"holder", .ref .mutable slice, .immutable, 0, 0⟩,
      ⟨"owner", .ref .readOnly owner, .immutable, 0, 0⟩],
    .mk 0 [] (some (.read (.deref (.read (.var 0))))), .unknown⟩
private def entry (called : Bool) : Impl :=
  ⟨"entry", #[], #[],
    if called then #[⟨"owner", owner, .mutable, 0, 0⟩, ⟨"holder", slice, .mutable, 0, 0⟩,
      ⟨"returned", slice, .immutable, 0, 0⟩] else #[],
    .mk 0 (if called then [
      .letS 0 (.arrLit owner [.lit .i64 7] 0) 0,
      .letS 1 (.slice .readOnly (.of (.var 0)) .omitted .omitted 0) 0,
      .letS 2 (.call 1 [.byRef .mutable (.var 1), .byRef .readOnly (.var 0)] 0) 0,
      .print [.expr (.read (.elem (.val (.read (.var 2))) (.lit .i64 0) 0))] 0] else []) none,
    .unknown⟩
private def program (contents : List RootRef) (called : Bool) : Module :=
  ⟨#["content-roots.goose"], #[.int .i64, owner, slice], #[], #[entry called, helper],
    #[⟨0, "entry", if called then [(1, [.local 0]), (2, [.local 0])] else [], [], []⟩,
      ⟨1, "read-holder", [(0, [.param 0]), (1, [.param 1])], [contents], [(0, contents)]⟩],
    0, #[⟨0, 17, "call"⟩], #[], #[]⟩
private def rejection (module : Module) : Option (Goose.Core.Rule × String) :=
  match validate module with | .ok () => none | .error error => some (error.rule, error.message)
private def stdout (module : Module) : Option (List UInt8) :=
  match eval 64 .release module with | .done .returned output _ => some output.data.toList | _ => none
theorem owner_content_call_validated : validate (program [.param 1] true) = .ok () := by cbv

theorem owner_content_call_reads_pointee : stdout (program [.param 1] true) = some [55, 10] := by cbv

theorem grounded_self_content_rejected : rejection (program [.param 0] true) = some (.call,
    "argument 0: the callee context's content roots {local 1} do not cover the roots {local 0} of the slice variable passed") := by cbv

theorem unused_self_content_validated : validate (program [.param 0] false) = .ok () := by cbv

private def callerAccess : AccessEnv :=
  let module := program [.param 1] true
  ⟨module, entry true, module.contexts[0]'(by decide)⟩

theorem physical_argument_roots : callerAccess.argsRoots [.byRef .mutable (.var 1), .byRef .readOnly (.var 0)] =
    .ok [[.local 1], [.local 0]] := by cbv

theorem loaded_holder_content_roots : callerAccess.exprRoots (.read (.var 1)) = .ok [.local 0] := by cbv

private def relay : Impl := { helper with
  name := "forward-holder"
  body := .mk 0 [] (some (.call 2 [.byRef .mutable (.deref (.read (.var 0))),
    .byRef .readOnly (.deref (.read (.var 1)))] 0)) }

private def forwarded (contents : List RootRef) : Module :=
  let original := program [.param 1] true
  { original with
    impls := #[entry true, relay, helper]
    contexts := original.contexts.push
      ⟨2, "read-holder", [(0, [.param 0]), (1, [.param 1])], [contents], [(0, contents)]⟩ }

theorem forwarded_owner_content_validated : validate (forwarded [.param 1]) = .ok () := by cbv

theorem forwarded_owner_content_reads_pointee : stdout (forwarded [.param 1]) = some [55, 10] := by cbv

theorem forwarded_self_content_rejected : rejection (forwarded [.param 0]) = some (.call,
    "argument 0: the callee context's content roots {param 0} differ from the content roots {param 1} of the reference passed") := by cbv
end Goose.Proofs.ConstructionRootCorrespondence.ContentBoundary
