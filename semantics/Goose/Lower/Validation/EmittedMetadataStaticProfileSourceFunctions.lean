import Goose.Lower.Validation.EmittedMetadataStaticProfileSource
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem EmittedProfile.initState (profile : ArtifactProfile) : EmittedProfile profile initState := by
  intro inst member
  cases member

theorem EmittedProfileRun.finishFunction {profile : ArtifactProfile} {le : LEnv} (impl : Core.Impl) (value : ValueId) :
    EmittedProfileRun profile le (Goose.Lower.finishFunction impl value) := by
  unfold Goose.Lower.finishFunction
  refine EmittedProfileRun.read.bind fun env => EmittedProfileRun.isLive.bind fun live => ?_
  cases live
  · exact EmittedProfileRun.pure ()
  · simp only [ite_true]
    split
    · exact (EmittedProfileRun.newBlock []).bind fun sink =>
        (EmittedProfileRun.emitTerm (.br sink.1 []) trivial).bind fun _ =>
          (EmittedProfileRun.setCur _).bind fun _ => EmittedProfileRun.emitTerm (.br sink.1 []) trivial
    · exact EmittedProfileRun.emitTerm (.ret _ none) trivial

theorem lowerImpl_emittedProfile {module : Core.Module} {impl : Core.Impl} {type : Ty} {finish : Nat}
    (typed : Core.tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish)) :
    EmittedProfile module.profile (cfg_implState module impl) := by
  have action : EmittedProfileRun module.profile (lowerEnv module impl.vars impl.results.toList) (cfg_implAction impl) := by
    apply (EmittedProfileRun.newBlock _).bind
    intro entry
    apply (EmittedProfileRun.setCur _).bind
    intro ignored
    exact (profile_source_block impl.body (implEnv module impl) impl.results.toList typed none _ false).bind fun value =>
      EmittedProfileRun.finishFunction impl value
  exact action initState _ _ rfl (.initState module.profile)

theorem lowerGlobal_emittedProfile {module : Core.Module} {global : Core.Global} {index finish : Nat}
    (typed : Core.tyExpr (initEnv module index) global.init 0 = .ok (global.ty, finish)) :
    EmittedProfile module.profile (cfg_globalState module global) := by
  have action : EmittedProfileRun module.profile (lowerEnv module #[] [global.ty]) (cfg_globalAction global) := by
    apply (EmittedProfileRun.newBlock []).bind
    intro entry
    apply (EmittedProfileRun.setCur _).bind
    intro ignored
    exact (profile_source_expression global.init (initEnv module index) [global.ty] typed).bind fun value =>
      EmittedProfileRun.emitTerm (.ret [value] (some global.org)) trivial
  exact action initState _ _ rfl (.initState module.profile)

theorem lowerImpl_emittedProfile_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {impl : Core.Impl} {index : Nat} (row : module.impls[index]? = some impl) :
    EmittedProfile module.profile (cfg_implState module impl) := by
  obtain ⟨type, finish, typed, _⟩ := ((validate_modOk module accepted).impl index impl row).body
  exact lowerImpl_emittedProfile typed

theorem lowerGlobal_emittedProfile_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {global : Core.Global} {index : Nat} (row : module.globals[index]? = some global) :
    EmittedProfile module.profile (cfg_globalState module global) := by
  obtain ⟨finish, typed⟩ := ((validate_modOk module accepted).glob index global row).init
  exact lowerGlobal_emittedProfile typed

def EmittedFunctionProfile (profile : ArtifactProfile) (func : GIR.Func) : Prop :=
  ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, EmittedProfileInst profile inst

theorem EmittedProfile.finishBlocks {profile : ArtifactProfile} {state : LS}
    (checked : EmittedProfile profile state) {func : GIR.Func}
    (blocks : func.blocks = Goose.Lower.finishBlocks state.blocks) : EmittedFunctionProfile profile func := by
  intro block member inst atInst
  rw [blocks] at member
  simp only [Goose.Lower.finishBlocks, Array.toList_map, List.mem_map] at member
  obtain ⟨body, bodyMember, rfl⟩ := member
  exact checked inst (by
    apply List.mem_flatMap.mpr
    exact ⟨body, bodyMember, atInst⟩)

theorem lowerImpl_functionProfile_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {impl : Core.Impl} {index : Nat} (row : module.impls[index]? = some impl) :
    EmittedFunctionProfile module.profile (lowerImpl module impl) :=
  (lowerImpl_emittedProfile_of_accepted accepted row).finishBlocks (cfg_impl_blocks module impl)

theorem lowerContextAt_functionProfile_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {context : Context} {impl : Core.Impl} (row : module.impls[context.impl]? = some impl) :
    EmittedFunctionProfile module.profile (lowerContextAt module context impl) :=
  (lowerImpl_emittedProfile_of_accepted accepted row).finishBlocks (cfg_context_blocks module context impl)

theorem lowerGlobal_functionProfile_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {global : Core.Global} {index : Nat} (row : module.globals[index]? = some global) :
    EmittedFunctionProfile module.profile (lowerGlobal module global).init :=
  (lowerGlobal_emittedProfile_of_accepted accepted row).finishBlocks (cfg_global_blocks module global)

end Goose.Lower.Validation
