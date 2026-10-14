import Goose.Construct.Roots

namespace Goose.Construct.RootChecks
open Goose.Core (Rule)

private def slice : Ty := .slice .readOnly (.int .u8)
private def array : Ty := .varr (.int .u8)
private def known (reads : List Target := []) : SummaryAnn :=
  .known ⟨reads, [], [], [], [], [1], [], [], false, false⟩

private def implementation : Impl :=
  ⟨"bytes", #[], #[⟨slice, .register, none⟩, ⟨array, .value, none⟩], #[],
    .mk 0 [] (some (.values [.bytes slice [0, 255] 0, .bytes array [128] 0])), known⟩

private def context : Context := ⟨0, "bytes", [], [[.static], []], []⟩
private def module : Module :=
  ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩

private def accepts (module : Module) (context : Context) : Bool :=
  match checkContext module context with | .ok _ => true | .error _ => false

#guard accepts module context
#guard !accepts module { context with resultRoots := [[], []] }
#guard !accepts module { context with resultRoots := [[.static], [.static]] }

private def receiver : Impl := { implementation with
  results := #[⟨slice, .register, none⟩]
  vars := #[⟨"view", slice, .immutable, 0, 0⟩, ⟨"scalar", .int .i64, .immutable, 0, 0⟩]
  body := .mk 0 [.receive [0, 1] (.values [.bytes slice [0, 255] 0, .lit .i64 7]) 0,
    .retValues [.read (.var 0)] 0] none }

private def receiveContext : Context := ⟨0, "receive", [(0,[.static])], [[.static]], []⟩
#guard accepts { module with impls := #[receiver], contexts := #[receiveContext] } receiveContext
#guard !accepts { module with impls := #[receiver], contexts := #[receiveContext] }
  { receiveContext with varRoots := [(0,[])] }

private def copiesGlobal : Impl := { implementation with
  results := #[⟨array, .value, none⟩]
  body := .mk 0 [.retValues [.copy array (.global 0) 0] 0] none
  summary := known }
private def copyContext : Context := ⟨0, "copy", [], [[]], []⟩
private def copyModule : Module := { module with
  globals := #[⟨"global", .grow (.int .u8), .mutable, .arrLit (.grow (.int .u8)) [], 0⟩]
  impls := #[copiesGlobal], contexts := #[copyContext] }
#guard !accepts copyModule copyContext
#guard accepts { copyModule with
  impls := #[{ copiesGlobal with summary := .known ⟨[.global 0],[],[],[],[],[0],[],[],true,false⟩ }] } copyContext

private def copiesSliceParameter : Impl :=
  ⟨"copy-slice", #[⟨0,.byValue⟩], #[⟨array,.value,none⟩],
    #[⟨"source",slice,.immutable,0,0⟩],
    .mk 0 [.retValues [.copy array (.var 0) 0] 0] none,
    .known ⟨[],[],[],[],[],[0],[],[],false,false⟩⟩
private def sliceParameterContext : Context := ⟨0,"copy-slice",[(0,[.param 0])],[[]],[]⟩
private def sliceParameterModule : Module := { module with
  impls := #[copiesSliceParameter], contexts := #[sliceParameterContext] }
#guard !accepts sliceParameterModule sliceParameterContext

private def limitedLiteral (expression : Expr) : Impl :=
  ⟨"limited",#[],#[⟨.limited (.int .u8) 1,.value,none⟩],#[],
    .mk 0 [.retValues [expression] 0] none,
    .known ⟨[],[],[],[],[],[0],[],[],false,false⟩⟩
#guard !accepts { module with impls := #[limitedLiteral (.bytes (.limited (.int .u8) 1) [1,2] 0)], contexts := #[copyContext] } copyContext
#guard !accepts { module with impls := #[limitedLiteral
  (.arrLit (.limited (.int .u8) 1) [.lit .u8 1, .lit .u8 2])], contexts := #[copyContext] } copyContext

#guard accepts { sliceParameterModule with impls := #[{ copiesSliceParameter with
  summary := .known ⟨[.param 0],[],[],[],[],[0],[],[],true,false⟩ }] } sliceParameterContext
private def limitedWithAbort : Impl := { limitedLiteral (.bytes (.limited (.int .u8) 1) [1,2] 0) with
  summary := .known ⟨[],[],[],[],[],[0],[],[],true,false⟩ }
#guard accepts { module with impls := #[limitedWithAbort], contexts := #[copyContext] } copyContext
#guard accepts { module with impls := #[limitedLiteral (.bytes (.limited (.int .u8) 1) [1] 0)], contexts := #[copyContext] } copyContext

#guard !accepts { module with impls := #[limitedLiteral (.bytes (.limited (.int .u8) 2) [1,2] 0)], contexts := #[copyContext] } copyContext

end Goose.Construct.RootChecks
