import Goose.Lower.Validation.PermissionInstructionReferencesOps
import Goose.Lower.Validation.PermissionPreservationGenerated
import Goose.Lower.Validation.PermissionInstructionControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem newPermissions_borrowTo {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {owner value : ValueId} {requested actual : Mutability}
    {referent : Ty}
    (typed : before.vals[owner]? = some (some (.data (.ref actual referent))))
    (authority : requested = .mutable → le.mod.profile = .shrink →
      ((∃ element, referent = .grow element) ∨ (∃ element, referent = .growshrink element) ∨
        (∃ element capacity, referent = .limited element capacity)) →
      before.cur.isSome = true → FreshContentsEvidence le first before owner)
    (generated : GeneratedBuilderState before)
    (run : borrowTo requested owner le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  have lowering := run
  simp only [borrowTo, bind_run, read_apply] at lowering
  rw [valTy_of_recorded (le := le) typed] at lowering
  let ownerKind := match (VTy.data (.ref actual referent)) with
    | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) |
      .data (.ref .mutable (.limited _ _)) => true
    | _ => false
  change (if (requested == .mutable && le.mod.profile == .shrink && ownerKind) = true
    then emitDef (.ownerBorrow owner) else freezeTo requested owner) le before = (value, after) at lowering
  split at lowering
  · rename_i guard
    have flags := Bool.and_eq_true_iff.mp guard
    have earlier := Bool.and_eq_true_iff.mp flags.1
    have requestedMutable : requested = .mutable := by simpa using earlier.1
    have profile : le.mod.profile = .shrink := by simpa using earlier.2
    have resizable : (∃ element, referent = .grow element) ∨ (∃ element, referent = .growshrink element) ∨
        (∃ element capacity, referent = .limited element capacity) := by
      cases actual <;> cases referent <;> simp_all [ownerKind]
    apply NewPermissionInstructions.emitDef lowering
    intro live
    have evidence := authority requestedMutable profile resizable live
    have retained := evidence.of_framed_run lowering (dense_emitDef _) (advB_emitDef _)
      (types_emitDef _) (generatedTargetFrame_emitDef none _) generated.dense generated.live (by trivial)
    exact .ownerBorrow retained
  · exact newPermissions_freezeTo lowering

theorem newPermissions_borrowTo_dead {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {owner value : ValueId} {requested : Mutability}
    (dead : before.cur = none) (run : borrowTo requested owner le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  rcases borrowTo_cases run with freeze | emitted
  · exact newPermissions_freezeTo freeze
  · rw [emitDef_none _ _ dead] at emitted
    obtain ⟨_, rfl⟩ := Prod.mk.inj emitted
    exact .of_blocks_eq rfl

theorem newPermissions_borrowTo_of_source_place {env : Core.TEnv} {place : Place}
    {info : PlaceInfo} {start finish : Nat} {requested : Mutability}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (reference : info.canReference place = true)
    (writable : requested = .mutable → info.referenceWritable env.mod.profile = true)
    {func : Func} {results : List Ty} {first : Nat} {before middle after : LS} {owner value : ValueId}
    (floor : first ≤ before.vals.size)
    (placeRun : lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, middle))
    (generated : GeneratedBuilderState before)
    (run : borrowTo requested owner (lowerEnv env.mod env.vars results) middle = (value, after)) :
    NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results) first middle after := by
  cases current : middle.cur with
  | none => exact newPermissions_borrowTo_dead current run
  | some block =>
    have live : middle.cur.isSome = true := by simp [current]
    obtain ⟨actual, typed⟩ := lowerPlace_generated_typed place source placeRun live (generated := generated)
    apply newPermissions_borrowTo typed _ (generated.lowerPlace place placeRun) run
    intro requestedMutable profile resizable _
    have container : ContentsTarget info.ty := by
      rcases resizable with ⟨element, same⟩ | ⟨element, same⟩ | ⟨element, capacity, same⟩ <;> rw [same] <;> trivial
    have contents := source_place_reference_contents source container reference (writable requestedMutable)
    exact (lowerPlace_generated_contents place source container contents placeRun live
      (generated := generated)).weaken floor

theorem newPermissions_lowerExpr_ref {env : Core.TEnv} {place : Place} {requested : Mutability}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.ref requested place) start = .ok (type, finish))
    {func : Func} {results : List Ty} {first : Nat} {before after : LS} {value : ValueId}
    (floor : first ≤ before.vals.size)
    (children : ∀ info next, Core.tyPlace env place start = .ok (info, next) →
      ∀ before middle owner, GeneratedBuilderState before →
      lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, middle) →
      NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results)
        before.vals.size before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.ref requested place) (lowerEnv env.mod env.vars results) before = (value, after)) :
    NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨info, next, placeSource, _, writable⟩ := tyExpr_ref_place source
  have reference : info.canReference place = true := by
    simp only [Core.tyExpr] at source
    obtain ⟨actualInfo, actualNext, actualPlace, source⟩ := (Goose.Core.Sound.st_bind_ok _ _ _ _).mp source
    rw [placeSource] at actualPlace
    cases actualPlace
    obtain ⟨_, _, fieldSource, _⟩ := (Goose.Core.Sound.st_bind_ok _ _ _ _).mp source
    exact (Goose.Core.Sound.checkFieldReference_ok _ _ _ _).mp fieldSource |>.1
  have lowering := run
  simp only [lowerExpr] at lowering
  obtain ⟨owner, middle, placeRun, borrowed⟩ := bind_eq.mp lowering
  have head := (children info next placeSource before middle owner generated placeRun).weaken floor
  have sourceWritable : requested = .mutable → info.referenceWritable env.mod.profile = true := by
    intro same
    subst requested
    cases permission : info.referenceWritable env.mod.profile <;> simp_all [Mutability.atLeast]
  have tail := newPermissions_borrowTo_of_source_place (func := func) placeSource reference sourceWritable floor placeRun generated borrowed
  exact head.compose_framed tail borrowed (dense_borrowTo _ _) (advB_borrowTo _ _)
    (types_borrowTo _ _) (generatedTargetFrame_borrowTo none _ _) (generated.lowerPlace place placeRun) (by trivial)

#print axioms newPermissions_borrowTo
#print axioms newPermissions_borrowTo_of_source_place
#print axioms newPermissions_lowerExpr_ref

end Goose.Lower.Validation
