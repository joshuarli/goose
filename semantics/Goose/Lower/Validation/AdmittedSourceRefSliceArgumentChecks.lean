import Goose.GIR.AdmittedRegionsChecks
namespace Goose.Lower.Validation.AdmittedSourceRefSliceArgumentChecks
open Goose Goose.Core Goose.GIR Goose.Lower
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
private def backing : Ty := .arr (.int .i64) 1
private def slice : Ty := .slice .readOnly (.int .i64)
private def main : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body := .mk 0 [] none, summary := .unknown }
private def wrapper : Impl :=
  { name := "wrapper", params := #[⟨0,.byRef⟩], results := #[],
    vars := #[⟨"q",.ref .mutable slice,.immutable,0,0⟩,⟨"holder",slice,.mutable,0,0⟩],
    body := .mk 0 [
      .letS 1 (.slice .readOnly (.of (.global 0)) .omitted .omitted 0) 0,
      .expr (.call 2 [.byRef .readOnly (.var 1),.byRef .mutable (.deref (.read (.var 0)))] 0) 0] none,
    summary := .unknown }
private def callee : Impl :=
  { name := "callee", params := #[⟨0,.byRef⟩,⟨1,.byRef⟩], results := #[],
    vars := #[⟨"holder",.ref .readOnly slice,.immutable,0,0⟩,
      ⟨"dependency",.ref .mutable slice,.immutable,0,0⟩],
    body := .mk 0 [] none, summary := .unknown }
private def source : Core.Module :=
  { files := #["unused-holder-dependency"], types := #[],
    globals := #[⟨"G",backing,.immutable,.arrLit backing [.lit .i64 0],0⟩,
      ⟨"H",backing,.immutable,.arrLit backing [.lit .i64 1],0⟩],
    impls := #[main,wrapper,callee],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"wrapper",[(0,[.global 0,.global 1]),(1,[.global 0,.global 1])],[],[]⟩,
      ⟨2,"callee",[(0,[.param 0]),(1,[.global 0,.global 1])],[],[(0,[.param 1])]⟩],
    entry := 0, origins := #[⟨0,1,"expr"⟩] }
example : Core.validate source = .ok () := by cbv
#guard (GIR.validate (lower source)).isOk
#guard ((lower source).funcs[1]?).any fun func => (func.roots.values.getD #[]).any fun row =>
  row.2 == [.global 0, .global 1, .param 0]
example : (GIR.validate { lower source with funcs := (lower source).funcs.map fun func =>
    { func with roots := { func.roots with values := none } } }).mapError (·.code) =
      .error .v050 := by cbv

private def twoFormals : Impl :=
  { wrapper with
    params := #[⟨0,.byRef⟩,⟨1,.byRef⟩],
    vars := #[⟨"q",.ref .mutable slice,.immutable,0,0⟩,
      ⟨"r",.ref .mutable slice,.immutable,0,0⟩,⟨"holder",slice,.mutable,0,0⟩],
    body := .mk 0 [
      .letS 2 (.slice .readOnly (.of (.global 0)) .omitted .omitted 0) 0,
      .expr (.call 2 [.byRef .readOnly (.var 2),.byRef .mutable (.deref (.read (.var 0)))] 0) 0] none }
private def sharedAnnotation : Core.Module :=
  { source with
    impls := #[main,twoFormals,callee],
    contexts := source.contexts.set! 1
      ⟨1,"wrapper",[(0,[.global 0,.global 1]),(1,[.global 0,.global 1]),
        (2,[.global 0,.global 1])],[],[]⟩ }
example : Core.validate sharedAnnotation = .ok () := by cbv
#guard (GIR.validate (lower sharedAnnotation)).isOk
#guard ((lower sharedAnnotation).funcs[1]?).any fun func => (func.roots.values.getD #[]).any fun row =>
  row.2 == [.global 0, .global 1, .param 0] && !row.2.contains (.param 1)

private def observingWrapper : Impl :=
  { name := "observing", params := #[⟨0,.byRef⟩,⟨1,.byRef⟩], results := #[],
    vars := #[⟨"q",.ref .mutable slice,.immutable,0,0⟩,
      ⟨"unused",.ref .readOnly backing,.immutable,0,0⟩],
    body := .mk 0 [.expr (.call 2 [.byRef .mutable (.deref (.read (.var 0)))] 0) 0] none,
    summary := .unknown }
private def observingTarget : Impl :=
  { name := "observed", params := #[⟨0,.byRef⟩], results := #[],
    vars := #[⟨"q",.ref .mutable slice,.immutable,0,0⟩],
    body := .mk 0 [] none, summary := .unknown }
private def observing : Core.Module :=
  { source with
    impls := #[main,observingWrapper,observingTarget],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"observing",[(0,[.param 0]),(1,[])],[],[(0,[.global 0,.global 1])]⟩,
      ⟨2,"observed",[(0,[.param 0])],[],[(0,[.global 0,.global 1])]⟩] }
example : Core.validate observing = .ok () := by cbv
#guard (GIR.validate (lower observing)).isOk
#guard ((lower observing).funcs[1]?).any fun func =>
  (func.roots.values.getD #[]).toList.map Prod.snd == [[.param 0]]
#guard let gir := lower observing
  (gir.funcs[1]?).any fun func =>
    let provenance := func.provenance (GIR.resultRoots gir gir.implTypes) (func.valueTypes gir) gir.rootCount
    (func.roots.values.getD #[]).all fun row => rootsAt provenance.vals row.1 == [.param 0]

private def invalidLocal : Impl :=
  { name := "invalid", params := #[], results := #[],
    vars := #[⟨"q",.ref .mutable slice,.immutable,0,0⟩],
    body := .mk 0 [.expr (.read (.var 0)) 0] none, summary := .unknown }
private def invalidLocalSource : Core.Module :=
  { source with
    impls := #[main,invalidLocal],
    contexts := #[⟨0,"main",[],[],[]⟩,⟨1,"invalid",[(0,[.global 0])],[],[]⟩] }
#guard ((lower invalidLocalSource).funcs[1]?).any fun func =>
  (func.roots.values.getD #[]).toList.map Prod.snd == [[.global 0]]
#guard match GIR.validate (lower invalidLocalSource) with
  | .error violation => violation.code == .v010
  | .ok _ => false
private def misaligned : Impl :=
  { invalidLocal with
    params := #[⟨1,.byRef⟩],
    vars := #[⟨"q",.ref .mutable slice,.immutable,0,0⟩,
      ⟨"other",.ref .readOnly backing,.immutable,0,0⟩] }
private def misalignedSource : Core.Module :=
  { invalidLocalSource with
    impls := #[main,misaligned],
    contexts := #[⟨0,"main",[],[],[]⟩,⟨1,"invalid",[(0,[.global 0]),(1,[])],[],[]⟩] }
#guard ((lower misalignedSource).funcs[1]?).any fun func =>
  (func.roots.values.getD #[]).toList.map Prod.snd == [[.global 0]]
private def missingVariable : Core.Module :=
  { invalidLocalSource with
    impls := #[main,{ invalidLocal with vars := #[] }] }
#guard ((lower missingVariable).funcs[1]?).any (·.roots.values.isNone)
private def scalarRead : Core.Module :=
  { invalidLocalSource with
    impls := #[main,{ invalidLocal with
      vars := #[⟨"scalar",.int .i64,.immutable,0,0⟩] }] }
#guard ((lower scalarRead).funcs[1]?).any (·.roots.values.isNone)

end Goose.Lower.Validation.AdmittedSourceRefSliceArgumentChecks
