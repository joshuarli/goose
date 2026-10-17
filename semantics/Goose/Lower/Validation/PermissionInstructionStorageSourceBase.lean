import Goose.Lower.Validation.PermissionPreservationInstructionRules
import Goose.Lower.Validation.PermissionPreservationSourceValues
import Goose.Lower.Validation.PermissionInstructionControl
import Goose.Lower.Validation.SourceStatementTyping
import Goose.Lower.Validation.SourceStorage
import Goose.Lower.Validation.FieldTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def PermissionStorageExprChild (env : Core.TEnv) (func : Func) (results : List Ty) (expr : Expr) : Prop :=
  ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
      lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after) →
      NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) before.vals.size before after

def PermissionStoragePlaceChild (env : Core.TEnv) (func : Func) (results : List Ty) (place : Place) : Prop :=
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
      lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after) →
      NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) before.vals.size before after

def PermissionStorageViewChild (env : Core.TEnv) (func : Func) (results : List Ty) (view : View) : Prop :=
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
      lowerView view (lowerEnv env.mod env.vars results) before = (value, after) →
      NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) before.vals.size before after

theorem PermissionTransfer.fresh_weaken {profile : ArtifactProfile} {le : LEnv} {first earlier : Nat}
    {state : LS} {value : ValueId} {target : Ty}
    (transfer : PermissionTransfer profile (FreshWritableEvidence le first state)
      (FreshContentsEvidence le first state) value target) (bound : earlier ≤ first) :
    PermissionTransfer profile (FreshWritableEvidence le earlier state)
      (FreshContentsEvidence le earlier state) value target :=
  transfer.mono (fun _ evidence => evidence.weaken bound) (fun _ evidence => evidence.weaken bound)

theorem PermissionTransfer.fresh_of_framed_run {α : Type} {action : B α}
    {profile : ArtifactProfile} {le : LEnv} {first : Nat} {before after : LS} {value : ValueId}
    {target : Ty} {result : α} {loop : Option LoopCtx}
    (transfer : PermissionTransfer profile (FreshWritableEvidence le first before)
      (FreshContentsEvidence le first before) value target)
    (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before) :
    PermissionTransfer profile (FreshWritableEvidence le first after)
      (FreshContentsEvidence le first after) value target :=
  transfer.mono
    (fun _ evidence => evidence.of_framed_run run dense advances typed frameRun generated.dense generated.live frames)
    (fun _ evidence => evidence.of_framed_run run dense advances typed frameRun generated.dense generated.live frames)

theorem permissionStorage_owner_target {type element : Ty} (owner : type.ownerElem? = some element) :
    ContentsTarget type := by
  cases type <;> simp_all [Ty.ownerElem?, ContentsTarget]

theorem permissionStorage_readable_binding_target {type : Ty} (readable : type.readable = true)
    (profile : ArtifactProfile) : BindingTarget profile type := by
  cases type <;> simp_all [Ty.readable, Ty.flat, BindingTarget]

theorem permissionStorage_passable_self (type : Ty) : type.passableTo type = true := by
  cases type with
  | ref mu type | slice mu type => cases mu <;> simp [Ty.passableTo, Mutability.atLeast]
  | _ => simp [Ty.passableTo]

private theorem permissionStorage_equal_caps {info : PlaceInfo} (profile : ArtifactProfile)
    (same : info.bindingWritable = info.contentsWritable) :
    info.ownerMutationWritable profile = info.contentsWritable := by
  cases profile <;> cases shape : info.ty <;> simp [PlaceInfo.ownerMutationWritable, shape, same]

theorem permissionStorage_owner_contents {env : Core.TEnv} {place : Place} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env place start = .ok (info, finish))
    (permission : info.ownerMutationWritable env.mod.profile = true) : info.contentsWritable = true := by
  cases profile : env.mod.profile with
  | shrink => simpa [PlaceInfo.ownerMutationWritable, profile] using permission
  | pilot =>
    cases place with
    | field owner index => cases profile.symm.trans (tyPlace_field_profile source)
    | var index =>
      simp only [Core.tyPlace] at source
      obtain ⟨localVar, next, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      rw [shape]
    | global index =>
      simp only [Core.tyPlace] at source
      split at source
      · cases row : env.mod.globals[index]? with
        | none => simp [row, rej_ok] at source
        | some descriptor =>
          simp only [row] at source
          have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
          dsimp only at shape
          rw [shape]
      · exact (rej_ok _ _ _ _).mp source |>.elim
    | deref expression =>
      simp only [Core.tyPlace] at source
      obtain ⟨type, next, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      cases type <;> try exact (rej_ok _ _ _ _).mp source |>.elim
      case ref mu target =>
        have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        dsimp only at shape
        have same : info.bindingWritable = info.contentsWritable := by rw [shape]
        simpa only [permissionStorage_equal_caps _ same] using permission
    | elem view index origin =>
      simp only [Core.tyPlace] at source
      obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨⟨element, writable⟩, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      have same : info.bindingWritable = info.contentsWritable := by rw [shape]
      simpa only [permissionStorage_equal_caps _ same] using permission

theorem permissionStorage_appendEffect {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {before middle after : LS} {effect : Effect} {result : Unit}
    (head : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState middle) (run : emitEffect effect le middle = (result, after))
    (issued : middle.cur.isSome = true → FreshPermissionInstruction module func le first after (.eff effect)) :
    NewPermissionInstructions module func le first before after :=
  head.compose_framed (.emitEffect run issued) run (dense_emitEffect effect) (advB_emitEffect effect)
    (types_emitEffect effect) (generatedTargetFrame_emitEffect none effect) generated (by trivial)

#print axioms permissionStorage_owner_contents
#print axioms PermissionTransfer.fresh_of_framed_run

end Goose.Lower.Validation
