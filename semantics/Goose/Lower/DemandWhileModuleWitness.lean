import Goose.Lower.DemandWhileImmediateGlobals
import Goose.Lower.DemandWhileMixedChecks

namespace Goose.Lower.DemandWhileModuleWitness
open Goose.Core Goose.GIR Goose.Lower.DemandWhileMixedChecks

theorem immediate (artifact : ArtifactProfile) : ImmediateGlobalInitializers (module artifact) := by
  intro id global globalAt
  cases id with
  | zero =>
    simp [module] at globalAt
    subst global
    exact .boolean true
  | succ id => simp [module] at globalAt

theorem fragment (profile : NumProfile) (artifact : ArtifactProfile) (state : St) (ctx : Context) (impl : Impl)
    (contextAt : (module artifact).contexts[(module artifact).entry]? = some ctx)
    (implAt : (module artifact).impls[ctx.impl]? = some impl) :
    ∀ middle : St, WhileMixedStatements ⟨profile, module artifact⟩
      { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := 1 } impl.body.stmts := by
  simp [module] at contextAt
  subst ctx
  simp [module] at implAt
  subst impl
  intro middle
  exact supported _ _

theorem noValue (artifact : ArtifactProfile) (ctx : Context) (impl : Impl)
    (contextAt : (module artifact).contexts[(module artifact).entry]? = some ctx)
    (implAt : (module artifact).impls[ctx.impl]? = some impl) : impl.body.value = none := by
  simp [module] at contextAt
  subst ctx
  simp [module] at implAt
  subst impl
  rfl

theorem success (profile : NumProfile) (artifact : ArtifactProfile) {fuel : Nat} {after : St}
    (accepted : Core.validate (module artifact) = .ok ()) (run : GIR.runModule fuel ⟨profile, lower (module artifact)⟩ St.initial = .ok () after) :
    ∃ sourceFuel, Core.runModule sourceFuel ⟨profile, module artifact⟩ St.initial = .ok () after :=
  accepted_generated_immediate_module_success accepted (immediate artifact)
    (fragment profile artifact) (noValue artifact) run

theorem stopped (profile : NumProfile) (artifact : ArtifactProfile) {fuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate (module artifact) = .ok ()) (nonTimeout : stop ≠ .timeout)
    (run : GIR.runModule fuel ⟨profile, lower (module artifact)⟩ St.initial = .stop stop after) :
    ∃ sourceFuel, Core.runModule sourceFuel ⟨profile, module artifact⟩ St.initial = .stop stop after :=
  accepted_generated_immediate_module_nonTimeout_stop accepted (immediate artifact)
    (fragment profile artifact) (noValue artifact) nonTimeout run

#print axioms success
#print axioms stopped
end Goose.Lower.DemandWhileModuleWitness
