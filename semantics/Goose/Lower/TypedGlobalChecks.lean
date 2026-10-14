import Goose.Lower.TypedGlobals
import Goose.GIR.Validate

namespace Goose.Lower.TypedGlobalChecks

open Goose.Core Goose.GIR

def global : Core.Global := ⟨"ready", .bool, .immutable, .bool true, 0⟩

def dependent : Core.Global := ⟨"copied", .bool, .immutable, .read (.global 0), 0⟩

def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [.assertS (.read (.global 1)) 1] none, summary := .unknown }

def module (profile : ArtifactProfile) : Core.Module :=
  { profile, files := #["typed-global.goose"], types := #[], globals := #[global, dependent],
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

theorem initializers_simulation (artifact : ArtifactProfile) (profile : NumProfile) (fuel : Nat)
    (accepted : Core.validate (module artifact) = .ok ()) :
    EventualM (Core.initGlobals fuel ⟨profile, module artifact⟩ (List.range 2))
      (fun k => GIR.initGlobals k ⟨profile, lower (module artifact)⟩ (List.range 2)) St.initial := by
  apply typedGlobals_simulation fuel accepted
  intro id found present
  cases id with
  | zero =>
    have foundEq : found = global := by simpa [module] using present.symm
    subst found
    exact typedExprClaim_bool fuel ⟨profile, module artifact⟩ [global.ty] true
  | succ id =>
    cases id with
    | zero =>
      have foundEq : found = dependent := by simpa [module] using present.symm
      subst found
      cases fuel with
      | zero => exact typedExprClaim_zero _ _ _
      | succ fuel =>
        exact typedExprClaim_read (typedPlaceClaim_global fuel ⟨profile, module artifact⟩ [dependent.ty] 0)
    | succ id => simp [module] at present

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
