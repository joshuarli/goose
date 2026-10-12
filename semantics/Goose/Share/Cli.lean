import Goose.Core.Run
import Goose.Share.Propose

/-!
The `goose-semantics share` command as pure functions from file bytes to one
output line and an exit status.

* `share UNSHARED.json SHARED.json` checks that the second module is a
  quotient of the first. It prints `["ok",CLASSES]` with status 0, where
  `CLASSES` is the number of implementations after sharing, or
  `["rejected",MESSAGE]` with status 5. Either file failing to decode prints
  `["malformed",MESSAGE]` with status 2.
* `share --propose UNSHARED.json` merges every group of implementations with
  equal bodies, passes the result through the same check, and prints the
  shared module in the Core encoding with status 0. A proposal the check
  refuses is `["rejected",MESSAGE]` with status 5.
-/

namespace Goose.Share.Cli

open Goose.Core

def rejected (msg : String) : String × UInt32 :=
  (s!"[\"rejected\",{Run.quote msg}]", 5)

/-- The unshared module and the shared one, with the maps rebuilt from their
context tables. -/
def check (m m' : Module) : String × UInt32 :=
  let qt := reconstructImplMap m m'
  let rt := reconstructContextMap m m'
  if checkQuotient m m' qt rt then (s!"[\"ok\",{m'.impls.size}]", 0)
  else rejected (explainQuotient m m' qt rt)

def checkBytes (unshared shared : ByteArray) : String × UInt32 :=
  match Decode.decodeBytes unshared with
  | .error msg => Run.malformed s!"unshared module: {msg}"
  | .ok m =>
    match Decode.decodeBytes shared with
    | .error msg => Run.malformed s!"shared module: {msg}"
    | .ok m' => check m m'

def proposeBytes (bs : ByteArray) : String × UInt32 :=
  match Decode.decodeBytes bs with
  | .error msg => Run.malformed msg
  | .ok m =>
    match propose m with
    | .error msg => rejected msg
    | .ok p =>
      if checkQuotient m p.shared p.implMap p.contextMap then (Write.module p.shared, 0)
      else rejected s!"the proposal failed the check: {explainQuotient m p.shared p.implMap p.contextMap}"

end Goose.Share.Cli
