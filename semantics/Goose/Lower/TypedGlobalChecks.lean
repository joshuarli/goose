import Goose.Lower.TypedGlobals
import Goose.GIR.Validate

namespace Goose.Lower.TypedGlobalChecks

open Goose.Core Goose.GIR

def global : Core.Global := ⟨"ready", .bool, .immutable, .bool true, 0⟩

def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [.assertS (.read (.global 0)) 1] none, summary := .unknown }

def module (profile : ArtifactProfile) : Core.Module :=
  { profile, files := #["typed-global.goose"], types := #[], globals := #[global],
    impls := #[implementation],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "global"⟩, ⟨0, 2, "assert"⟩] }

theorem initializer_simulation (artifact : ArtifactProfile) (profile : NumProfile) (fuel : Nat)
    (accepted : Core.validate (module artifact) = .ok ()) :
    EventualM
      (freshAct >>= fun act => evalExpr fuel ⟨profile, module artifact⟩ ⟨#[], act, [], 0⟩ global.init)
      (fun k => enterFn k ⟨profile, lower (module artifact)⟩ 0
        (lowerGlobal (module artifact) global).init []) St.initial := by
  apply typedGlobal_simulation accepted (by rfl) (InitializedGlobals.initial _).invariant
  exact typedExprClaim_bool fuel ⟨profile, module artifact⟩ [global.ty] true

#guard [ArtifactProfile.pilot, .shrink].all fun profile =>
  match Core.validate (module profile), GIR.validate (lower (module profile)) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 30 profile (module artifact), GIR.run 60 profile (lower (module artifact)) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

end Goose.Lower.TypedGlobalChecks
