import Goose.Construct.GIR.Typing

namespace Goose.Construct.GIR.LimitedReferenceChecks

private def limited : Ty := .limited (.int .i64) 4
private def environment : TyEnv := {
  slots := #[⟨limited, .immutable, 0, 0⟩]
  globals := #[(limited, .immutable)]
  sigs := #[([.ref .mutable limited], [])]
  vals := #[] }

private def acceptsAddress (operation : Op) : Bool :=
  match Op.resultTy environment operation with
  | .error _ => false
  | .ok ty => ({ environment with vals := #[some ty] }.checkCall 0 [0] []).isOk

#guard acceptsAddress (.slotAddr 0)
#guard acceptsAddress (.globalAddr 0)
#guard !({ environment with vals := #[some (.data (.ref .readOnly limited))] }.checkCall 0 [0] []).isOk
private def readonlyEnvironment : TyEnv := { environment with
  sigs := #[([.ref .readOnly limited], [])]
  vals := #[some (.data (.ref .readOnly limited))] }
#guard (readonlyEnvironment.checkCall 0 [0] []).isOk

end Goose.Construct.GIR.LimitedReferenceChecks
