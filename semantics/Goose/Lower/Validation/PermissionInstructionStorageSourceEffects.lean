import Goose.Lower.Validation.PermissionInstructionStorageSourceBase

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permissionStorage_mutation_tail {env : Core.TEnv} {func : Func} {results : List Ty}
    {owner : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env owner start = .ok (info, finish))
    (container : ContentsTarget info.ty) (contents : info.contentsWritable = true)
    (placeChild : PermissionStoragePlaceChild env func results owner)
    {before middle effectState after : LS} {address : ValueId} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (placeRun : lowerPlace owner (lowerEnv env.mod env.vars results) before = (address, middle))
    {α : Type} {action : B α} {value : α}
    (tailRun : action (lowerEnv env.mod env.vars results) middle = (value, effectState))
    (tailIssued : NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results)
      middle.vals.size middle effectState)
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (framed : GeneratedTargetFrameRun none action) (dead : DeadRun action)
    (effectGenerated : GeneratedBuilderState effectState) {effect : Effect} {result : Unit}
    (mutation : ContentsMutation address (.eff effect))
    (effectRun : emitEffect effect (lowerEnv env.mod env.vars results) effectState = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  have middleGenerated := generated.lowerPlace owner placeRun
  have middleBound := Nat.le_trans bound (advB_lowerPlace owner _ _ _ _ placeRun).vals
  have priorIssued := (placeChild source generated placeRun).weaken bound
  have composed := priorIssued.compose_framed (tailIssued.weaken middleBound) tailRun dense advances typed framed
    middleGenerated (by trivial)
  apply permissionStorage_appendEffect composed effectGenerated effectRun
  intro live
  have middleLive := dead.live_before tailRun live
  have evidence := (lowerPlace_generated_contents owner source container contents placeRun middleLive generated).weaken bound
  have atEffect := evidence.of_framed_run tailRun dense advances typed framed middleGenerated.dense
    middleGenerated.live (by trivial)
  have atEnd := atEffect.of_framed_run effectRun (dense_emitEffect effect) (advB_emitEffect effect)
    (types_emitEffect effect) (generatedTargetFrame_emitEffect none effect) effectGenerated.dense
    effectGenerated.live (by trivial)
  exact .mutation mutation atEnd

theorem permissionStorage_store_tail {env : Core.TEnv} {func : Func} {results : List Ty}
    {owner : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env owner start = .ok (info, finish))
    (binding : info.bindingWritable = true) (demand : BindingTarget env.mod.profile info.ty)
    (placeChild : PermissionStoragePlaceChild env func results owner)
    {before middle effectState after : LS} {address value : ValueId} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (placeRun : lowerPlace owner (lowerEnv env.mod env.vars results) before = (address, middle))
    {action : B ValueId}
    (tailRun : action (lowerEnv env.mod env.vars results) middle = (value, effectState))
    (tailIssued : NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results)
      middle.vals.size middle effectState)
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (framed : GeneratedTargetFrameRun none action) (dead : DeadRun action)
    (effectGenerated : GeneratedBuilderState effectState)
    (transfer : effectState.cur.isSome = true →
      PermissionTransfer env.mod.profile (FreshWritableEvidence (lowerEnv env.mod env.vars results) first effectState)
        (FreshContentsEvidence (lowerEnv env.mod env.vars results) first effectState) value info.ty)
    {origin : Option OriginId} {result : Unit}
    (effectRun : emitEffect (.store address value origin) (lowerEnv env.mod env.vars results) effectState = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  have middleGenerated := generated.lowerPlace owner placeRun
  have middleBound := Nat.le_trans bound (advB_lowerPlace owner _ _ _ _ placeRun).vals
  have priorIssued := (placeChild source generated placeRun).weaken bound
  have composed := priorIssued.compose_framed (tailIssued.weaken middleBound) tailRun dense advances typed framed
    middleGenerated (by trivial)
  apply permissionStorage_appendEffect composed effectGenerated effectRun
  intro live
  have middleLive := dead.live_before tailRun live
  have evidence := (lowerPlace_generated_binding owner source binding demand placeRun middleLive generated).weaken bound
  have atEffect := evidence.of_framed_run tailRun dense advances typed framed middleGenerated.dense
    middleGenerated.live (by trivial)
  have atEnd := atEffect.of_framed_run effectRun (dense_emitEffect _) (advB_emitEffect _)
    (types_emitEffect _) (generatedTargetFrame_emitEffect none _) effectGenerated.dense
    effectGenerated.live (by trivial)
  obtain ⟨mu, row⟩ := lowerPlace_generated_typed owner source placeRun middleLive generated
  have tailRow := typed _ _ _ _ tailRun _ _ row
  have endRow := types_emitEffect _ _ _ _ _ effectRun _ _ tailRow
  exact .store endRow atEnd ((transfer live).fresh_of_framed_run effectRun (dense_emitEffect _)
    (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _) effectGenerated (by trivial))

#print axioms permissionStorage_mutation_tail
#print axioms permissionStorage_store_tail

end Goose.Lower.Validation
