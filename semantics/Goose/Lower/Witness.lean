import Goose.Proofs.Lower
import Goose.Core.Run
import Goose.Lower.Commands
import Goose.Lower.While
import Goose.Lower.Range

namespace Goose.Lower.Witness

open Goose.Proofs.Lower

def legacyCovered (bs : ByteArray) : Bool :=
  match Core.Decode.decodeBytes bs with
  | .ok m => moduleOk m
  | .error _ => false

/-- The line `agree` prints for the module and its lowering. -/
def agreeLine (profile : Core.NumProfile) (bs : ByteArray) : String :=
  match Core.Decode.decodeBytes bs with
  | .error msg => msg
  | .ok m =>
    match GIR.Json.decodeBytes (GIR.Json.write (lower m)).toUTF8 with
    | .error msg => msg
    | .ok _ => (Commands.agreeBytes { profile } bs (GIR.Json.write (lower m)).toUTF8).1

def straight : String := include_str "../../../test/gir/golden/gir_straight.core.json"
def divZero : String := include_str "../../../test/gir/golden/gir_div_zero.core.json"
def sliceOob : String := include_str "../../../test/gir/golden/gir_slice_oob.core.json"
def intOverflow : String := include_str "../../../test/gir/golden/gir_int_overflow_debug.core.json"

def branches : String := include_str "../../../test/gir/golden/gir_branches.core.json"
def assertFail : String := include_str "../../../test/gir/golden/gir_assert_fail.core.json"
def userAbort : String := include_str "../../../test/gir/golden/gir_user_abort.core.json"
def exitCode : String := include_str "../../../test/gir/golden/gir_exit_code.core.json"
def blockValue : String := include_str "../../../test/gir/golden/gir_ord02.core.json"
def structLocal : String := include_str "../../../test/semantics/golden/struct_local.core.json"

def countingWhile : String :=
  (include_str "../../../test/gir/golden/gir_loop_small.core.json").replace "\"20000\"" "\"3\""

def nestedWhile : String :=
  countingWhile.replace "[\"block\",1,[[\"s_assign_op\""
    "[\"block\",1,[[\"s_while\",[\"e_bool\",0],[\"block\",2,[],[]],4],[\"s_assign_op\""

/-- A statement covered by the local while theorem, irrespective of the module predicate. -/
def hasCoveredWhile (bs : ByteArray) : Bool :=
  match Core.Decode.decodeBytes bs with
  | .error _ => false
  | .ok m => m.impls.any fun impl => impl.body.stmts.any fun
    | .while c body _ => exprOk c && blockOk body
    | _ => false

def coreAccepted (bs : ByteArray) : Bool :=
  match Core.Decode.decodeBytes bs with
  | .ok m => match Core.validate m with
    | .ok _ => true
    | .error _ => false
  | .error _ => false

#guard !legacyCovered straight.toUTF8
#guard coreAccepted straight.toUTF8
#guard !legacyCovered branches.toUTF8
#guard coreAccepted branches.toUTF8
#guard legacyCovered assertFail.toUTF8
#guard legacyCovered userAbort.toUTF8
#guard legacyCovered exitCode.toUTF8
#guard !legacyCovered blockValue.toUTF8
#guard coreAccepted blockValue.toUTF8
#guard !legacyCovered divZero.toUTF8
#guard coreAccepted divZero.toUTF8
#guard !legacyCovered sliceOob.toUTF8
#guard coreAccepted sliceOob.toUTF8
#guard !legacyCovered intOverflow.toUTF8
#guard coreAccepted intOverflow.toUTF8

#guard !legacyCovered countingWhile.toUTF8
#guard coreAccepted countingWhile.toUTF8
#guard !legacyCovered nestedWhile.toUTF8
#guard coreAccepted nestedWhile.toUTF8
#guard (agreeLine .release nestedWhile.toUTF8).startsWith "[\"agree\",[\"done\",[\"returned\"],\"3\\n\"]"
#guard (agreeLine .debug nestedWhile.toUTF8).startsWith "[\"agree\",[\"done\",[\"returned\"],\"3\\n\"]"
#guard hasCoveredWhile countingWhile.toUTF8
#guard (agreeLine .release countingWhile.toUTF8).startsWith "[\"agree\",[\"done\",[\"returned\"],\"3\\n\"]"
#guard (agreeLine .debug countingWhile.toUTF8).startsWith "[\"agree\",[\"done\",[\"returned\"],\"3\\n\"]"

#guard (agreeLine .release straight.toUTF8).startsWith "[\"agree\""
#guard (agreeLine .debug straight.toUTF8).startsWith "[\"agree\""
#guard (agreeLine .release sliceOob.toUTF8).startsWith "[\"agree\",[\"done\",[\"aborted\",\"slice_oob\""
#guard (agreeLine .release branches.toUTF8).startsWith "[\"agree\",[\"done\",[\"aborted\",\"assert\""
#guard (agreeLine .debug branches.toUTF8).startsWith "[\"agree\",[\"done\",[\"aborted\",\"assert\""
#guard (agreeLine .debug intOverflow.toUTF8).startsWith "[\"agree\",[\"done\",[\"aborted\",\"int_overflow\""

#guard !legacyCovered structLocal.toUTF8
#guard coreAccepted structLocal.toUTF8
#guard (agreeLine .release structLocal.toUTF8).startsWith
  "[\"agree\",[\"done\",[\"returned\"],\"1 42 7\\n\"]"
#guard (agreeLine .debug structLocal.toUTF8).startsWith
  "[\"agree\",[\"done\",[\"returned\"],\"1 42 7\\n\"]"

open Goose.Core Goose.GIR

def legacyControlModule : Core.Module :=
  let impl : Core.Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := .mk 0 [.ifS (.bool true) (.mk 1 [.print [.text "control"] 1] none) none 0,
        .while (.bool false) (.mk 2 [] none) 2, .ret none 3] none,
      summary := .unknown }
  { files := #["legacy-control.goose"], types := #[], globals := #[],
    impls := #[impl], contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "if"⟩, ⟨0, 1, "print"⟩, ⟨0, 1, "while"⟩, ⟨0, 1, "return"⟩] }

#guard moduleOk legacyControlModule
#guard match Core.validate legacyControlModule, GIR.validate (lower legacyControlModule) with
  | .ok _, .ok _ => true
  | _, _ => false
#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 30 profile legacyControlModule, GIR.run 100 profile (lower legacyControlModule) with
  | .done .returned "control\n", .done .returned "control\n" => true
  | _, _ => false

def rangeBody : Core.Block :=
  .mk 1 [.print [.expr (.read (.var 0))] 0] none

def rangeStmt : Stmt := .forRange 0 (.lit .i64 0) (.lit .i64 3) rangeBody 0

def rangeModule : Core.Module :=
  let impl : Core.Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"i", .int .i64, .immutable, 1, 0⟩],
      body := .mk 0 [rangeStmt] none, summary := .unknown }
  { files := #["range.goose"], types := #[.int .i64], globals := #[],
    impls := #[impl],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "for"⟩] }

def rangeVars : Array LocalVar := #[⟨"i", .int .i64, .immutable, 1, 0⟩]

def rangeBuilder : LS :=
  (lowerStmt none rangeStmt (lowerEnv rangeModule rangeVars []) startLS).2

def rangeFunction : Func :=
  { name := "range", params := [], results := [],
    slots := rangeVars.mapIdx fun i lv => ⟨lv.ty, lv.kind, lv.scope, i⟩,
    scopes := #[none, some 0], blocks := finishBlocks rangeBuilder.blocks,
    summary := .unknown, org := none }

theorem concrete_range_statement (n : Nat) (p : NumProfile) :
    SimG ⟨⟨p, lower rangeModule⟩, rangeFunction⟩ (0, 0) ⟨0, [], {}, 0⟩
      (execStmt n ⟨p, rangeModule⟩ ⟨rangeVars, 0, [], 0⟩ rangeStmt)
      (fun flow pt' fr' => flow = .normal .unit ∧
        Post ⟨p, rangeModule⟩ ⟨rangeVars, 0, [], 0⟩ ⟨⟨p, lower rangeModule⟩, rangeFunction⟩
          startLS ⟨0, [], {}, 0⟩ rangeBuilder fr' pt' []) := by
  apply stmt_range_sim n none 0 (.lit .i64 0) (.lit .i64 3) rangeBody 0 rfl rfl rfl
    (lowerEnv rangeModule rangeVars []) startLS rangeBuilder () (0, 0)
    ⟨p, rangeModule⟩ ⟨rangeVars, 0, [], 0⟩ ⟨⟨p, lower rangeModule⟩, rangeFunction⟩
    ⟨0, [], {}, 0⟩
  · exact ⟨⟨"i", .int .i64, .immutable, 1, 0⟩, rfl, rfl⟩
  · apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  · rfl
  · exact extT_finish rangeBuilder
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#guard match Core.validate rangeModule, GIR.validate (lower rangeModule) with
  | .ok _, .ok _ => true
  | _, _ => false
#guard !moduleOk rangeModule
#guard match Core.eval 50 .release rangeModule, GIR.run 100 .release (lower rangeModule) with
  | .done .returned "0\n1\n2\n", .done .returned "0\n1\n2\n" => true
  | _, _ => false
#guard match Core.eval 50 .debug rangeModule, GIR.run 100 .debug (lower rangeModule) with
  | .done .returned "0\n1\n2\n", .done .returned "0\n1\n2\n" => true
  | _, _ => false

end Goose.Lower.Witness
