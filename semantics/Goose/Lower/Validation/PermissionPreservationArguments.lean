import Goose.Lower.Validation.PermissionPreservationGenerated
import Goose.Lower.Validation.PermissionPreservationTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerArg_mutable_binding {env : Core.TEnv} {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (reference : info.canReference place = true)
    (writable : info.referenceWritable env.mod.profile = true)
    (demand : BindingTarget env.mod.profile info.ty)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerArg (.byRef .mutable place) (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  have lowering := run
  simp only [lowerArg] at lowering
  obtain ⟨owner, middle, placeRun, borrowed⟩ := bind_eq.mp lowering
  have middleLive := (dead_borrowTo .mutable owner).live_before borrowed live
  have middleGenerated := generated.lowerPlace place placeRun
  have typed := lowerPlace_generated_writable_typed place source writable placeRun middleLive (generated := generated)
  by_cases resizable : (∃ element, info.ty = .grow element) ∨ (∃ element, info.ty = .growshrink element) ∨
      (∃ element capacity, info.ty = .limited element capacity)
  · have profile : env.mod.profile = .shrink := by
      rcases resizable with ⟨element, same⟩ | ⟨element, same⟩ | ⟨element, capacity, same⟩ <;>
        simpa only [BindingTarget, same] using demand
    have container : ContentsTarget info.ty := by
      rcases resizable with ⟨element, same⟩ | ⟨element, same⟩ | ⟨element, capacity, same⟩ <;> rw [same] <;> trivial
    have contents := source_place_reference_contents source container reference writable
    have evidence := lowerPlace_generated_contents place source container contents placeRun middleLive (generated := generated)
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact (borrowTo_owner_fresh_permissions evidence middleGenerated.dense middleGenerated.live
        current profile typed resizable borrowed).1
  · have ordinary : BindingTarget .pilot info.ty := by
      cases same : info.ty <;> simp_all [BindingTarget]
    have binding : info.bindingWritable = true := by
      cases same : info.ty <;> simp_all [BindingTarget, PlaceInfo.referenceWritable]
    have evidence := lowerPlace_generated_binding place source binding demand placeRun middleLive generated
    exact borrowTo_ordinary_fresh_binding evidence typed ordinary borrowed

theorem lowerArg_mutable_contents {env : Core.TEnv} {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (reference : info.canReference place = true)
    (writable : info.referenceWritable env.mod.profile = true) (container : ContentsTarget info.ty)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerArg (.byRef .mutable place) (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  have lowering := run
  simp only [lowerArg] at lowering
  obtain ⟨owner, middle, placeRun, borrowed⟩ := bind_eq.mp lowering
  have middleLive := (dead_borrowTo .mutable owner).live_before borrowed live
  have middleGenerated := generated.lowerPlace place placeRun
  have typed := lowerPlace_generated_writable_typed place source writable placeRun middleLive (generated := generated)
  have contents := source_place_reference_contents source container reference writable
  have evidence := lowerPlace_generated_contents place source container contents placeRun middleLive (generated := generated)
  cases current : middle.cur with
  | none => simp [current] at middleLive
  | some block => exact evidence.borrowTo_mutable typed middleGenerated.dense middleGenerated.live current borrowed

set_option maxHeartbeats 2000000 in
theorem lowerArgs_generated_permissions (args : List Arg)
    {env : Core.TEnv} {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    {results : List Ty} {before after : LS} {values : List ValueId}
    (run : lowerArgs args (lowerEnv env.mod env.vars results) before = (values, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    ∀ entry ∈ (params.map (fun param => tyOfVar callee param.var)).zip values,
      PermissionTransfer env.mod.profile
        (FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after)
        (FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after) entry.2 entry.1 := by
  induction args generalizing params start before after values with
  | nil =>
    cases params with
    | nil => simp
    | cons _ _ => simp at sameLength
  | cons arg args ih =>
    cases params with
    | nil => simp at sameLength
    | cons param params =>
      obtain ⟨value, middle, childRun, lowered⟩ := bind_eq.mp run
      obtain ⟨restValues, restAfter, restRun, returned⟩ := bind_eq.mp lowered
      obtain ⟨rfl, rfl⟩ := pure_eq.mp returned
      have middleGenerated := generated.lowerArg arg childRun
      have middleLive := (dead_lowerArgs args).live_before restRun live
      have growth := (advB_lowerArg arg _ _ _ _ childRun).vals
      have restPermissions {restStart : Nat}
          (restSource : Core.tyArgs env callee params args restStart = .ok ((), finish)) :=
        ih (by simpa using sameLength) restSource restRun live middleGenerated
      have headPermission : PermissionTransfer env.mod.profile
          (FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size middle)
          (FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size middle)
          value (tyOfVar callee param.var) := by
        cases arg with
        | byVal expr =>
          obtain ⟨localVar, argTy, childStart, childFinish, restStart, row, childSource, compatible, _⟩ :=
            tyArgs_byVal_head source
          rw [show tyOfVar callee param.var = localVar.ty by simp [tyOfVar, row]]
          apply PermissionTransfer.of_source compatible
          · intro referent same demand
            rw [same] at childSource
            exact lowerExpr_generated_binding expr childSource demand childRun middleLive generated
          · intro referent same container
            rw [same] at childSource
            exact lowerExpr_generated_contents expr childSource container childRun middleLive (generated := generated)
        | byRef mu place =>
          obtain ⟨localVar, info, childFinish, restStart, row, placeSource, reference, writable, compatible, _⟩ :=
            source_argument_permissions source
          rw [show tyOfVar callee param.var = localVar.ty by simp [tyOfVar, row]]
          apply PermissionTransfer.of_source compatible
          · intro referent same demand
            cases mu with
            | readOnly => cases same
            | mutable =>
              cases (Ty.ref.inj same).2
              exact lowerArg_mutable_binding placeSource reference (writable rfl) demand childRun middleLive generated
          · intro referent same container
            cases mu with
            | readOnly => cases same
            | mutable =>
              cases (Ty.ref.inj same).2
              exact lowerArg_mutable_contents placeSource reference (writable rfl) container childRun middleLive generated
      have retainedHead := headPermission.mono
        (fun _ evidence => evidence.of_framed_run (loop := none) restRun (dense_lowerArgs args)
          (advB_lowerArgs args) (types_lowerArgs args) (generatedTargetFrame_lowerArgs none args)
          middleGenerated.dense middleGenerated.live trivial)
        (fun _ evidence => evidence.of_framed_run (loop := none) restRun (dense_lowerArgs args)
          (advB_lowerArgs args) (types_lowerArgs args) (generatedTargetFrame_lowerArgs none args)
          middleGenerated.dense middleGenerated.live trivial)
      intro entry member
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact retainedHead
      · cases arg with
        | byVal expr =>
          obtain ⟨_, _, _, _, _, _, _, _, restSource⟩ := tyArgs_byVal_head source
          exact (restPermissions restSource entry member).mono
            (fun _ evidence => evidence.weaken growth) (fun _ evidence => evidence.weaken growth)
        | byRef mu place =>
          obtain ⟨_, _, _, _, _, _, _, _, restSource⟩ := tyArgs_byRef_head source
          exact (restPermissions restSource entry member).mono
            (fun _ evidence => evidence.weaken growth) (fun _ evidence => evidence.weaken growth)

#print axioms lowerArg_mutable_binding
#print axioms lowerArg_mutable_contents
#print axioms lowerArgs_generated_permissions

end Goose.Lower.Validation
