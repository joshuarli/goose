import Goose.Core.Run
import Goose.Core.Validate
import Goose.Share.Cli

/-!
Evaluated examples for sharing, over the Core modules in `test/semantics/share`
and the first golden. Each is checked when the library builds.

* what the proposer merges and what it must keep apart;
* that the checker accepts the proposals and refuses forged claims;
* that the premise is needed: bodies that the checker refuses to identify do
  behave differently when a forged module identifies them.
-/

namespace Goose.Share.Examples

open Goose.Core

def firstJson : String := include_str "../../../test/semantics/golden/first.core.json"
def freeVariableJson : String := include_str "../../../test/semantics/share/free_variable_two_locals.core.json"
def differJson : String := include_str "../../../test/semantics/share/differ_one_operation.core.json"
def differForgedJson : String := include_str "../../../test/semantics/share/differ_one_operation.forged.json"
def mutualJson : String := include_str "../../../test/semantics/share/mutual_pair.core.json"
def mergeableJson : String := include_str "../../../test/semantics/share/mergeable_callee.core.json"
def distinctJson : String := include_str "../../../test/semantics/share/distinct_callees.core.json"
def forgedBodyJson : String := include_str "../../../test/semantics/share/forged_merged_body.json"
def forgedCalleeJson : String := include_str "../../../test/semantics/share/forged_wrong_callee.json"

def load (text : String) : Option Module :=
  match Decode.decodeBytes text.toUTF8 with
  | .ok m => some m
  | .error _ => none

/-- Number of implementations after sharing, when the proposal passes the check. -/
def sharedClasses (text : String) : Option Nat := do
  let m ← load text
  let p ← (propose m).toOption
  if checkQuotient m p.shared p.implMap p.contextMap then some p.shared.impls.size else none

/-- Whether the checker accepts `shared` as a quotient of `unshared`. -/
def accepts (unshared shared : String) : Bool :=
  match load unshared, load shared with
  | some m, some m' =>
    checkQuotient m m' (reconstructImplMap m m') (reconstructContextMap m m')
  | _, _ => false

/-- The line `run` prints for a module. -/
def outcome (text : String) : String := (Run.runBytes {} text.toUTF8).1

/-- The proposal for a module, written out. -/
def proposed (text : String) : Option String := do
  let m ← load text
  let p ← (propose m).toOption
  some (Goose.Core.Writer.module p.shared)

-- Two contexts of one function, called with a global-rooted and a local-rooted
-- slice, have identical implementations and merge.
#guard sharedClasses firstJson == some 2
#guard (proposed firstJson).map outcome == some (outcome firstJson)
#guard outcome firstJson == "[\"done\",[\"returned\"],\"33\\n\"]"

-- A free variable bound to two outer locals: two identical implementations merge.
#guard sharedClasses freeVariableJson == some 2

-- A mutually recursive pair under two contexts merges as a pair.
#guard sharedClasses mutualJson == some 3

-- Bodies differing only in a callee that is itself mergeable merge after one round.
#guard sharedClasses mergeableJson == some 3

-- Bodies that call different callees stay distinct, and so do bodies that differ
-- in one operation.
#guard sharedClasses distinctJson == some 5
#guard sharedClasses differJson == some 3

-- Writing and decoding a module that nothing merges gives it back.
#guard (proposed distinctJson).map (· ++ "\n") == some distinctJson
#guard (proposed differJson).map (· ++ "\n") == some differJson

-- The checker refuses forged claims: bodies differing in one operation, a merged
-- body that is no member's, and callees that run different implementations.
#guard accepts differJson differForgedJson == false
#guard accepts mergeableJson forgedBodyJson == false
#guard accepts distinctJson forgedCalleeJson == false

-- The premise is necessary: identifying implementations the checker refuses to
-- identify changes the behaviour.
#guard outcome differJson == "[\"done\",[\"returned\"],\"11\\n9\\n\"]"
#guard outcome differForgedJson == "[\"done\",[\"returned\"],\"11\\n11\\n\"]"
#guard outcome distinctJson != outcome forgedCalleeJson

-- The checker accepts a module as its own quotient.
#guard accepts differJson differJson

-- Root annotations matter to validation and not to execution: with every
-- context's annotations erased the first golden is rejected, yet it runs to the
-- same output.
#guard match load firstJson with
  | some m =>
    (match validate (eraseRoots m) with
      | .error _ => true
      | .ok () => false) &&
    Run.render m (eval 10000000 .release (eraseRoots m)) == Run.render m (eval 10000000 .release m)
  | none => false

end Goose.Share.Examples
