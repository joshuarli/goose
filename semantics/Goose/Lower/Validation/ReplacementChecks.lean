import Goose.Lower.CoreToGir
import Goose.Core.Validate
import Goose.GIR.Validate
namespace Goose.Lower.Validation.ReplacementChecks

open Goose Goose.Core Goose.Lower
private def module : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let receiver : Impl :=
    { name := "replace", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩], results := #[],
      vars := #[⟨"p", .ref .mutable owner, .immutable, 0, 0⟩,
        ⟨"q", .ref .readOnly (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.assignWhole (.deref (.read (.var 0)))
        (.arrLit owner [.read (.deref (.read (.var 1)))]) 0] none, summary := .unknown }
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := .mk 0 [.expr (.call 1 [.byRef .mutable (.global 0), .byRef .readOnly (.global 1)] 0) 0] none,
      summary := .unknown }
  { files := #["replacement-specialized"], types := #[],
    globals := #[⟨"owner", owner, .mutable, .arrLit owner [], 0⟩,
      ⟨"other", .int .i64, .immutable, .lit .i64 1, 0⟩],
    impls := #[main, receiver], contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "replace", [(0, [.global 0]), (1, [.global 1])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

#guard (Core.validate module).toBool
#guard (GIR.validate (lower module)).toBool

private def rejectedGir (input : GIR.Module) (code : GIR.Code) : Bool :=
  match GIR.validate input with | .ok () => false | .error rejection => rejection.code == code

private def genericParameters : GIR.Module :=
  let lowered := lower module
  { lowered with funcs := lowered.funcs.modify 1 fun func =>
    { func with roots := { func.roots with params := #[(0, [.param 0]), (1, [.param 1])] } } }

private def incorrectAnnotation : GIR.Module :=
  let lowered := lower module
  { lowered with funcs := lowered.funcs.modify 1 fun func =>
    { func with roots := { func.roots with params := #[(0, [.global 0]), (1, [.global 0])] } } }

private def sharedGlobal : Core.Module :=
  { module with
    globals := module.globals.modify 0 fun global =>
      { global with init := .arrLit global.ty [.lit .i64 1] },
    impls := module.impls.modify 0 fun impl =>
      { impl with body := .mk 0 [.expr (.call 1 [.byRef .mutable (.global 0),
        .byRef .readOnly (.elem (.of (.global 0)) (.lit .i64 0) 0)] 0) 0] none },
    contexts := module.contexts.modify 1 fun ctx =>
      { ctx with varRoots := [(0, [.global 0]), (1, [.global 0])] } }

#guard rejectedGir genericParameters .v060
#guard rejectedGir incorrectAnnotation .v050
#guard match Core.validate sharedGlobal with | .ok () => false | .error rejection => rejection.rule == .shrink
#guard rejectedGir (lower sharedGlobal) .v060
#guard GIR.rootsOverlap [.param 0] [.param 1]

private def emptyParameterContext : Core.Module :=
  { module with
    impls := module.impls.modify 0 fun impl => { impl with body := .mk 0 [] none },
    contexts := module.contexts.modify 1 fun context =>
      { context with varRoots := [(0, [.global 0]), (1, [])] } }

#guard (Core.validate emptyParameterContext).toBool
#guard (GIR.validate (lower emptyParameterContext)).toBool
#guard GIR.replacementOverlap none (some [.global 0])
#guard GIR.replacementOverlap none none
#guard !GIR.replacementOverlap (some []) none
#guard !GIR.replacementOverlap (some []) (some [])
#guard (GIR.ReplacementQueries.mk #[(0, [])] #[[.param 0]] #[]).value 0 == some []
#guard (GIR.ReplacementQueries.mk #[(0, [])] #[[]] #[]).value 0 == none
#guard (GIR.ReplacementQueries.mk #[] #[[.param 0]] #[]).value 0 == some [.param 0]

private def unknownQueries : GIR.ReplacementQueries := ⟨#[], #[[.global 0], []], #[]⟩
private def queryTypes : Array (Option GIR.VTy) :=
  #[some (.data (.ref .mutable (.growshrink (.int .i64)))),
    some (.data (.ref .readOnly (.int .i64)))]

#guard GIR.killEmptyFacts [0] (unknownQueries.value 1) unknownQueries == []
#guard GIR.transferEmptyInst (lower module) queryTypes unknownQueries [0] (.def 2 (.load 1)) == []
#guard GIR.transferEmptyInst (lower module) queryTypes unknownQueries [0] (.def 2 (.call 99 [1] none)) == []
#guard GIR.transferEmptyInst (lower module) queryTypes unknownQueries [0] (.def 2 (.call 99 [] none)) == []

private def emptyQueries : GIR.ReplacementQueries := ⟨#[(1, [])], #[[.global 0], [.param 1]], #[]⟩
#guard GIR.transferEmptyInst (lower module) queryTypes emptyQueries [0] (.def 2 (.load 1)) == [0]
#guard GIR.transferEmptyInst (lower module) queryTypes emptyQueries [0] (.def 2 (.call 99 [1] none)) == []

end Goose.Lower.Validation.ReplacementChecks
