import Goose.GIR.Validate

namespace Goose.Lower.Validation.ReplacementEmptyInferenceChecks

open Goose.Core Goose.GIR

private def slice : Ty := .slice .readOnly (.int .i64)
private def holder : Ty := .ref .mutable slice
private def func (insts : List Inst) : Func :=
  { name := "query", params := [holder], results := [], slots := #[⟨slice, .mutable, 0, 0⟩],
    scopes := #[none], blocks := #[⟨[(0, .data holder)], .def 2 (.slotAddr 0) :: insts ++ [.term (.ret [] none)]⟩],
    roots := { contents := #[(0, [])] }, summary := .unknown, org := none }
private def module (funcs : Array Func := #[]) : GIR.Module :=
  { files := #[], globals := #[], funcs := #[{
      name := "main", params := [], results := [], slots := #[], scopes := #[none],
      blocks := #[⟨[], [.term (.ret [] none)]⟩], summary := .unknown, org := none }] ++ funcs,
    entry := 0, origins := #[], profile := .shrink }
private def query (insts : List Inst) (result : ValueId := 1) : ReplacementRootQuery :=
  let source := func insts
  (replacementQueries (module) source (source.valueTypes (module))).value result

#guard query [.def 1 (.load 0)] == some []
#guard query [.def 1 (.load 2)] == none
#guard query [.eff (.slotInit 0 1 none), .def 1 (.load 2)] == none
#guard query [.eff (.slotInit 0 1 none), .def 1 (.load 2), .def 3 (.refFreeze 1)] 3 == none
#guard query [.eff (.slotInit 0 1 none), .def 1 (.load 0), .def 3 (.load 2)] 3 == some []
#guard query [.eff (.slotInit 0 1 none), .eff (.store 0 3 none), .def 1 (.load 0)] == none
#guard query [.def 1 (.call 99 [] none)] == none
#guard query [.def 3 (.call 99 [] none), .def 1 (.load 0)] == none

private def pureCallee : Func :=
  { name := "pure", params := [], results := [], slots := #[], scopes := #[none],
    blocks := #[⟨[], [.term (.ret [] none)]⟩],
    summary := .known ⟨[], [], [], [], [], false, false⟩, org := none }

#guard (let input := module #[pureCallee]; let source := func [.def 3 (.call 1 [] none), .def 1 (.load 0)];
  replacementQueries input source (source.valueTypes input)).value 1 == some []

#guard (let input := module #[{ pureCallee with summary := .known ⟨[], [.global 0], [], [], [], false, false⟩ }]
        let source := func [.def 3 (.call 1 [] none), .def 1 (.load 0)]
        let types := source.valueTypes input
        callDependencies input types (replacementQueries input source types) 1 []) == some [.global 0]

private def joined (incoming : List ValueId) : Func :=
  { func [.def 1 (.load 0)] with blocks :=
    #[⟨[(0, .data holder)], [.def 2 (.slotAddr 0), .def 1 (.load 0), .term (.br 1 incoming)]⟩,
      ⟨[(3, .data slice)], [.term (.ret [] none)]⟩] }
#guard (replacementQueries (module) (joined [1]) ((joined [1]).valueTypes (module))).value 3 == some []
#guard (replacementQueries (module) (joined [2]) ((joined [2]).valueTypes (module))).value 3 == none

private def seedless : Func :=
  { func [] with blocks := #[⟨[(0, .data holder)], [.def 2 (.slotAddr 0), .term (.br 1 [1])]⟩,
    ⟨[(1, .data slice)], [.eff (.slotInit 0 1 none), .def 3 (.load 2), .term (.br 1 [3])]⟩] }
#guard (replacementQueries (module) seedless (seedless.valueTypes (module))).value 1 == none
#guard (replacementQueries (module) seedless (seedless.valueTypes (module))).value 3 == none

end Goose.Lower.Validation.ReplacementEmptyInferenceChecks
