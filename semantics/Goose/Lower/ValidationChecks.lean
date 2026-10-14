import Goose.Core.Validate
import Goose.GIR.Validate
import Goose.Lower.CoreToGir
import Goose.Proofs.Lower

namespace Goose.Lower.ValidationChecks

open Goose.Core Goose.GIR Goose.Lower

def emptySummary : Core.Summary :=
  { reads := [], writes := [], grows := [], shrinks := [], rebinds := [], aborts := false, outputs := false }

def specializedResult : Core.Module :=
  let f : Core.Impl :=
    { name := "f"
      params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩]
      results := #[.ref .mutable (.int .i64)]
      vars := #[⟨"x", .ref .mutable (.int .i64), .immutable, 0, 0⟩,
        ⟨"y", .ref .mutable (.int .i64), .immutable, 0, 0⟩]
      body := .mk 0 [] (some (.read (.var 0)))
      summary := .known emptySummary }
  let main : Core.Impl :=
    { name := "main"
      params := #[]
      results := #[]
      vars := #[]
      body := .mk 0 [.expr (.call 0 [.byRef .mutable (.global 0), .byRef .mutable (.global 0)] 0) 0] none
      summary := .known emptySummary }
  { files := #["test.goose"]
    types := #[.int .i64, .ref .mutable (.int .i64)]
    globals := #[⟨"g", .int .i64, .mutable, .lit .i64 1, 0⟩]
    impls := #[f, main]
    contexts := #[⟨0, "f", [(0, [.global 0]), (1, [.global 0])], [[.global 0]], []⟩,
      ⟨1, "main", [], [], []⟩]
    entry := 1
    origins := #[⟨0, 1, "test"⟩] }

def orphanUnderstatedSummary : Core.Module :=
  let emptyImpl (name : String) : Core.Impl :=
    { name, params := #[], results := #[], vars := #[], body := .mk 0 [] none,
      summary := .known emptySummary }
  let main := emptyImpl "main"
  let orphan := { emptyImpl "orphan" with body := .mk 0 [.abort "stop" 0] none }
  { files := #["test.goose"]
    types := #[.int .i64]
    globals := #[]
    impls := #[main, orphan]
    contexts := #[⟨0, "main", [], [], []⟩]
    entry := 0
    origins := #[⟨0, 1, "test"⟩] }

#guard match Core.validate specializedResult with
  | .ok _ => true
  | _ => false

#guard match GIR.validate (lower specializedResult) with
  | .ok _ => true
  | _ => false

#guard (lower specializedResult).funcs[0]?.map (·.roots.results) ==
  some #[[.global 0, .param 0, .param 1]]

#guard match Core.validate orphanUnderstatedSummary with
  | .error ⟨.root, _⟩ => true
  | _ => false

#guard match GIR.validate (lower orphanUnderstatedSummary) with
  | .error ⟨.v050, _⟩ => true
  | _ => false

/-- A value-returning function need not reach a return when its loop has no exit. -/
def loopResult (body : Core.Block) : Core.Module :=
  let spin : Core.Impl :=
    { name := "spin", params := #[], results := #[.int .i64], vars := #[],
      body := .mk 0 [.while (.bool true) body 0] none, summary := .unknown }
  let main : Core.Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := .mk 0 [] none, summary := .unknown }
  { files := #["loop_result.goose"], types := #[.int .i64], globals := #[],
    impls := #[main, spin], contexts := #[⟨0, "main", [], [], []⟩, ⟨1, "spin", [], [[]], []⟩],
    entry := 0, origins := #[⟨0, 1, "while"⟩], profile := .shrink, structs := #[] }

def acceptsLoop (body : Core.Block) : Bool :=
  let m := loopResult body
  match Core.validate m, GIR.validate (lower m) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard acceptsLoop (.mk 1 [] none)
#guard acceptsLoop (.mk 1 [.cont 0] none)
#guard acceptsLoop (.mk 1 [.ret (some (.lit .i64 7)) 0] none)

def loopVoid : Core.Module :=
  let m := loopResult (.mk 1 [] none)
  { m with
    impls := m.impls.modify 1 (fun impl => { impl with results := #[] })
    contexts := m.contexts.modify 1 (fun ctx => { ctx with resultRoots := [] }) }

def loopingEntry : Core.Module :=
  { loopVoid with entry := 1 }

#guard match Core.validate loopingEntry with
  | .ok _ => true
  | _ => false
#guard Goose.Proofs.Lower.moduleOk loopingEntry
#guard !Goose.Proofs.Lower.moduleOk specializedResult

def tailResult : Core.Module :=
  let m := loopResult (.mk 1 [] none)
  { m with impls := m.impls.modify 1 (fun impl =>
    { impl with body := .mk 0 [] (some (.lit .i64 7)) }) }

def malformedResultEntry : Core.Module :=
  let m := loopResult (.mk 1 [] none)
  { m with entry := 1, impls := m.impls.modify 1 (fun impl =>
    { impl with body := .mk 0 [] none }) }

#guard match Core.validate loopVoid, GIR.validate (lower loopVoid) with
  | .ok _, .ok _ => true
  | _, _ => false
#guard match (lower loopVoid).funcs[1]? with
  | some f => f.blocks.size == 4 && (match f.blocks[3]?.bind (fun block : GIR.Block => block.lastTerm?) with
    | some (GIR.Term.ret [] none) => true | _ => false)
  | none => false
#guard match Core.validate tailResult, GIR.validate (lower tailResult) with
  | .ok _, .ok _ => true
  | _, _ => false
#guard match (lower tailResult).funcs[1]? with
  | some f => f.blocks.size == 1 && (match f.blocks[0]?.bind (fun block : GIR.Block => block.lastTerm?) with
    | some (GIR.Term.ret [0] none) => true | _ => false)
  | none => false
#guard Goose.Proofs.Lower.moduleOk malformedResultEntry
#guard match (lower malformedResultEntry).funcs[1]? with
  | some f => f.blocks.size == 1 && (match f.blocks[0]?.bind (fun block : GIR.Block => block.lastTerm?) with
    | some (GIR.Term.ret [] none) => true | _ => false)
  | none => false
#guard match Core.eval 20 .release malformedResultEntry,
    GIR.run 20 .release (lower malformedResultEntry) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

end Goose.Lower.ValidationChecks
