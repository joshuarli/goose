import Goose.Construct.Roots

namespace Goose.Construct.ExclusionChecks
open Goose.Core (Rule)

private def bytes : Ty := .varr (.int .u8)
private def arrays : Ty := .grow bytes
private def known : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def context : Context := ⟨0, "builder", [], [], []⟩

private def implementation (statement : Stmt) : Impl :=
  ⟨"builder", #[], #[],
    #[⟨"first", arrays, .mutable, 0, 0⟩, ⟨"second", arrays, .mutable, 0, 0⟩],
    .mk 0 [.letS 0 (.arrLit arrays [] 0) 0, .letS 1 (.arrLit arrays [] 0) 0, statement] none, known⟩

private def module (implementation : Impl) : Module :=
  ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩

private def rejects (statement : Stmt) (rule : Rule) : Bool :=
  let impl := implementation statement
  match checkContext (module impl) context with
  | .error rejection => rejection.rule == rule
  | .ok _ => false

private def producer (grows : Nat) : Expr :=
  .blockE (.mk 1 [.expr (.push (.var grows) (.bytes bytes [10] 0) (some 0)) 0]
    (some (.bytes bytes [20] 0))) 0

#guard rejects (.expr (.push (.var 0) (producer 0) (some 0)) 0) .call
#guard !rejects (.expr (.push (.var 0) (producer 1) (some 0)) 0) .call
#guard rejects (.assignWhole (.var 0) (.copy arrays (.var 0) 0) 0) .whole
#guard !rejects (.assignWhole (.var 0) (.copy arrays (.var 1) 0) 0) .whole

private def fixed : Ty := .grow (.int .u8)
private def fixedImplementation : Impl :=
  ⟨"fixed", #[], #[], #[⟨"owner", fixed, .mutable, 0, 0⟩],
    .mk 0 [.letS 0 (.arrLit fixed [] 0) 0,
      .expr (.push (.var 0) (.blockE (.mk 1
        [.expr (.push (.var 0) (.lit .u8 10) (some 0)) 0] (some (.lit .u8 20))) 0) (some 0)) 0] none, known⟩
#guard match checkContext (module fixedImplementation) context with
  | .ok _ => true | .error _ => false

private def helper : Impl :=
  ⟨"helper", #[⟨0,.byRef⟩], #[⟨bytes,.value,none⟩],
    #[⟨"owner", .ref .mutable arrays, .immutable, 0, 0⟩],
    .mk 0 [.expr (.push (.deref (.read (.var 0))) (.bytes bytes [10] 0) (some 0)) 0,
      .retValues [.bytes bytes [20] 0] 0] none,
    .known ⟨[], [.param 0], [.param 0], [], [], [0], [], [], false, false⟩⟩
private def helperContext : Context := ⟨1, "helper", [(0,[.param 0])], [[]], []⟩
private def caller : Impl := implementation
  (.expr (.push (.var 0) (.call 1 [.byRef .mutable (.var 0)] 0) (some 0)) 0)
private def callModule : Module := { module caller with
  impls := #[caller, helper], contexts := #[context, helperContext] }
#guard match checkContext callModule helperContext with
  | .ok _ => true | .error _ => false
#guard match checkContext callModule context with
  | .error rejection => rejection.rule == .call | .ok _ => false

end Goose.Construct.ExclusionChecks
