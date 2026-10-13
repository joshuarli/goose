import Goose.Core.Validate
import Goose.Core.Json
import Goose.Core.Writer

namespace Goose.Core.ValidationChecks

open Goose.Core

def emptySummary : Summary :=
  { reads := [], writes := [], grows := [], shrinks := [], rebinds := [], aborts := false, outputs := false }

def originTable : Array Origin := #[⟨0, 1, "let"⟩]

def impl (body : Block) (vars : Array LocalVar := #[]) (summary : SummaryAnn := .known emptySummary) : Impl :=
  { name := "main", params := #[], results := #[], vars, body, summary }

def module (main : Impl) (impls : Array Impl := #[main]) (contexts : Array Context := #[⟨0, "main", [], [], []⟩]) : Module :=
  { files := #["test.goose"], types := #[.int .i64, .bool], globals := #[], impls, contexts,
    entry := 0, origins := originTable }

def badRebindSummary : Module :=
  module (impl (.mk 0 [] none) #[] (.known { emptySummary with rebinds := [.param 0] }))

def summaryWithTarget (field : Nat) (target : Target) : Summary :=
  { reads := if field == 0 then [target] else []
    writes := if field == 1 then [target] else []
    grows := if field == 2 then [target] else []
    shrinks := if field == 3 then [target] else []
    rebinds := if field == 4 then [target] else []
    aborts := false
    outputs := false }

def summaryTargetRejected (field : Nat) (target : Target) : Bool :=
  match validate (module (impl (.mk 0 [] none) #[] (.known (summaryWithTarget field target)))) with
  | .error ⟨.summary, _⟩ => true
  | _ => false

def summaryTargetCases : List (Nat × Target) :=
  (List.range 5).flatMap fun field => [(field, .param 0), (field, .global 0)]

def repeatedSiblingScopes : Module :=
  let nested (branchScope : Nat) : Block :=
    .mk branchScope [.expr (.blockE (.mk 2 [] none)) 0] none
  module (impl (.mk 0 [.ifS (.bool true) (nested 1) (some (nested 3)) 0] none))

def orderedSiblingScopes : Module :=
  let nested (outer inner : Nat) : Block :=
    .mk outer [.expr (.blockE (.mk inner [] none)) 0] none
  module (impl (.mk 0 [.ifS (.bool true) (nested 1 2) (some (nested 3 4)) 0] none))

def nestedGlobalInitializer : Module :=
  let base := module (impl (.mk 0 [] none))
  { base with globals := #[⟨"g", .int .i64, .immutable,
    .ifE (.bool true) (.mk 0 [] (some (.lit .i64 1))) (.mk 1 [] (some (.lit .i64 2))), 0⟩] }

def badLocalOrigin : Module :=
  module (impl (.mk 0 [.letS 0 (.lit .i64 1) 0] none)
    #[⟨"x", .int .i64, .immutable, 0, 7⟩])

def orphanWithUnderstatedSummary : Module :=
  let entry := impl (.mk 0 [] none)
  let orphan :=
    { entry with name := "orphan", body := .mk 0 [.abort "stop" 0] none }
  module entry #[entry, orphan]

#guard match validate badRebindSummary with
  | .error ⟨.summary, _⟩ => true
  | _ => false

#guard summaryTargetCases.all (fun (field, target) => summaryTargetRejected field target)

#guard match validate repeatedSiblingScopes with
  | .error ⟨.type, _⟩ => true
  | _ => false

#guard match validate badLocalOrigin with
  | .error ⟨.type, _⟩ => true
  | _ => false

#guard match validate orphanWithUnderstatedSummary with
  | .error ⟨.root, _⟩ => true
  | _ => false

#guard match validate orderedSiblingScopes with
  | .ok _ => true
  | _ => false

#guard match Decode.decodeBytes (Writer.module orderedSiblingScopes).toUTF8 with
  | .ok decoded =>
      match decoded.impls[0]? with
      | some f => scopeParents (blockScopes none f.body) == #[none, some 0, some 1, some 0, some 3]
      | none => false
  | .error _ => false

#guard match validate nestedGlobalInitializer with
  | .ok _ => true
  | _ => false

#guard match Decode.decodeBytes (Writer.module nestedGlobalInitializer).toUTF8 with
  | .ok decoded =>
      match decoded.globals[0]? with
      | some g => scopeParents (exprScopes none g.init) == #[none, none]
      | none => false
  | .error _ => false

end Goose.Core.ValidationChecks
