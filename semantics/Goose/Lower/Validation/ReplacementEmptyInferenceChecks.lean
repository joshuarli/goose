import Goose.GIR.Validate

namespace Goose.Lower.Validation.ReplacementEmptyInferenceChecks

open Goose.Core Goose.GIR

private def slice : Ty := .slice .readOnly (.int .i64)
private def holder : Ty := .ref .mutable slice
private def func (insts : List Inst) : Func :=
  { name := "query", params := [holder], results := [], slots := #[⟨slice, .mutable, 0, 0⟩],
    scopes := #[none], blocks := #[⟨[(0, .data holder)], insts⟩],
    roots := { contents := #[(0, [])] }, summary := .unknown, org := none }
private def module (funcs : Array Func := #[]) : GIR.Module :=
  { files := #[], globals := #[], funcs, entry := 0, origins := #[], profile := .shrink }
private def types : Array (Option VTy) :=
  #[some (.data holder), some (.data slice), some (.data holder), some (.data slice)]
private def roots : Prov := ⟨#[[]], #[[.param 0], [], [.local 0], []]⟩
private def query (insts : List Inst) (result : ValueId := 1) : ReplacementRootQuery :=
  (replacementQueries (module) (func insts) types roots).value result

#guard query [.def 1 (.load 0)] == some []
#guard query [.def 1 (.load 2)] == none
#guard query [.eff (.slotInit 0 1 none), .def 1 (.load 2)] == none
#guard query [.eff (.slotInit 0 1 none), .def 1 (.load 2), .def 3 (.refFreeze 1)] 3 == none
#guard query [.eff (.slotInit 0 1 none), .def 1 (.load 0), .def 3 (.load 2)] 3 == some []
#guard query [.eff (.slotInit 0 1 none), .eff (.store 0 3 none), .def 1 (.load 0)] == none
#guard query [.def 1 (.call 0 [] none)] == none
#guard query [.def 3 (.call 0 [] none), .def 1 (.load 0)] == none

private def pureCallee : Func :=
  { name := "pure", params := [], results := [], slots := #[], scopes := #[none],
    blocks := #[⟨[], [.term (.ret [] none)]⟩],
    summary := .known ⟨[], [], [], [], [], false, false⟩, org := none }

#guard (replacementQueries (module #[pureCallee])
  (func [.def 3 (.call 0 [] none), .def 1 (.load 0)]) types roots).value 1 == some []
#guard (replacementQueries (module #[{ pureCallee with summary := .known ⟨[], [.global 0], [], [], [], false, false⟩ }])
  (func [.def 3 (.call 0 [] none), .def 1 (.load 0)]) types roots).value 1 == none

private def joined (incoming : List ValueId) : Func :=
  { func [.def 1 (.load 0)] with blocks :=
    #[⟨[(0, .data holder)], [.def 1 (.load 0), .term (.br 1 incoming)]⟩,
      ⟨[(3, .data slice)], [.term (.ret [] none)]⟩] }
#guard (replacementQueries (module) (joined [1]) types roots).value 3 == some []
#guard (replacementQueries (module) (joined [2]) types roots).value 3 == none

private def seedless : Func :=
  { func [] with blocks := #[⟨[(0, .data holder)], [.term (.br 1 [1])]⟩,
    ⟨[(1, .data slice)], [.eff (.slotInit 0 1 none), .def 3 (.load 2), .term (.br 1 [3])]⟩] }
#guard (replacementQueries (module) seedless types roots).value 1 == none
#guard (replacementQueries (module) seedless types roots).value 3 == none

end Goose.Lower.Validation.ReplacementEmptyInferenceChecks
