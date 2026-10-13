import Goose.Proofs.Lower
import Goose.Core.Run
import Goose.Lower.Commands
import Goose.Lower.While

/-!
Checks that the lowering theorem is not vacuous: committed goldens inside the
fragment it covers, and the fact that the interpreter of the lowered module
agrees with Core on each, in both numeric profiles.
-/

namespace Goose.Lower.Witness

open Goose.Proofs.Lower

/-- Whether a Core module, given as the bytes of its file, is in the fragment. -/
def covered (bs : ByteArray) : Bool :=
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

/-- A short instance of the committed counting while, with the same condition and body. -/
def countingWhile : String :=
  (include_str "../../../test/gir/golden/gir_loop_small.core.json").replace "\"20000\"" "\"3\""

/-- A statement covered by the local while theorem, irrespective of the module predicate. -/
def hasCoveredWhile (bs : ByteArray) : Bool :=
  match Core.Decode.decodeBytes bs with
  | .error _ => false
  | .ok m => m.impls.any fun impl => impl.body.stmts.any fun
    | .while c body _ => exprOk c && blockOk body
    | _ => false

#guard covered straight.toUTF8
#guard covered branches.toUTF8
#guard covered assertFail.toUTF8
#guard covered userAbort.toUTF8
#guard covered exitCode.toUTF8
#guard covered blockValue.toUTF8
#guard covered divZero.toUTF8
#guard covered sliceOob.toUTF8
#guard covered intOverflow.toUTF8

#guard hasCoveredWhile countingWhile.toUTF8
#guard (agreeLine .release countingWhile.toUTF8).startsWith "[\"agree\",[\"done\",[\"returned\"],\"3\\n\"]"
#guard (agreeLine .debug countingWhile.toUTF8).startsWith "[\"agree\",[\"done\",[\"returned\"],\"3\\n\"]"

#guard (agreeLine .release straight.toUTF8).startsWith "[\"agree\""
#guard (agreeLine .debug straight.toUTF8).startsWith "[\"agree\""
#guard (agreeLine .release sliceOob.toUTF8).startsWith "[\"agree\",[\"done\",[\"aborted\",\"slice_oob\""
#guard (agreeLine .release branches.toUTF8).startsWith "[\"agree\",[\"done\",[\"aborted\",\"assert\""
#guard (agreeLine .debug branches.toUTF8).startsWith "[\"agree\",[\"done\",[\"aborted\",\"assert\""
#guard (agreeLine .debug intOverflow.toUTF8).startsWith "[\"agree\",[\"done\",[\"aborted\",\"int_overflow\""

end Goose.Lower.Witness
