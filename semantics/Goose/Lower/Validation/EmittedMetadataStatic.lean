import Goose.Lower.Validation.OperandBounds
import Goose.Lower.Validation.ResolvedTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedProfileInst (profile : ArtifactProfile) : Inst → Prop
  | .def _ (.pop ..) | .def _ (.fieldAddr ..)
  | .eff (.popN ..) | .eff (.resize ..) | .eff (.clear ..) | .eff (.replace ..) => profile = .shrink
  | .term (.abort kind _) =>
      kind ∈ [AbortKind.popEmpty, .popNRange, .resizeNegative, .resizeFill, .capacity] → profile = .shrink
  | _ => True

def EmittedAnnotationResolved (module : Core.Module) : Inst → Prop
  | .def _ (.structLit type _) | .def _ (.arrLit type _) | .def _ (.arrFill type _) =>
      Core.checkResolvedType module type = .ok ()
  | _ => True

def EmittedVTyResolved (module : Core.Module) : VTy → Prop
  | .data type | .view _ type => Core.checkResolvedType module type = .ok ()

structure EmittedBodyResolved (module : Core.Module) (state : LS) : Prop where
  parameters : ∀ block ∈ state.blocks.toList, ∀ parameter ∈ block.params,
    EmittedVTyResolved module parameter.2
  annotations : ∀ inst ∈ state.insts, EmittedAnnotationResolved module inst

structure EmittedStatic (module : Core.Module) (state : LS) : Prop where
  profiles : ∀ inst ∈ state.insts, EmittedProfileInst module.profile inst
  resolved : EmittedBodyResolved module state

def EmittedStaticRun (module : Core.Module) (le : LEnv) (action : B α) : Prop :=
  ∀ before result after, action le before = (result, after) →
    EmittedStatic module before → EmittedStatic module after

theorem EmittedStaticRun.pure (module : Core.Module) (le : LEnv) (value : α) :
    EmittedStaticRun module le (pure value) := by
  intro before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem EmittedStaticRun.bind {module : Core.Module} {le : LEnv}
    {action : B α} {next : α → B β} (first : EmittedStaticRun module le action)
    (second : ∀ value, EmittedStaticRun module le (next value)) :
    EmittedStaticRun module le (action >>= next) := by
  intro before result after run checked
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ secondRun (first _ _ _ firstRun checked)

theorem EmittedStatic.initState (module : Core.Module) : EmittedStatic module initState := by
  constructor
  · intro inst member
    cases member
  · constructor
    · intro block member
      cases member
    · intro inst member
      cases member

theorem EmittedStatic.of_transport {module : Core.Module} {before after : LS}
    (checked : EmittedStatic module before)
    (parameters : ∀ block ∈ after.blocks.toList, ∀ parameter ∈ block.params,
      (∃ old ∈ before.blocks.toList, parameter ∈ old.params) ∨ EmittedVTyResolved module parameter.2)
    (instructions : ∀ inst ∈ after.insts,
      inst ∈ before.insts ∨ (EmittedProfileInst module.profile inst ∧ EmittedAnnotationResolved module inst)) :
    EmittedStatic module after := by
  constructor
  · intro inst member
    rcases instructions inst member with old | fresh
    · exact checked.profiles inst old
    · exact fresh.1
  · constructor
    · intro block member parameter atParameter
      rcases parameters block member parameter atParameter with ⟨old, oldMember, oldParameter⟩ | fresh
      · exact checked.resolved.parameters old oldMember parameter oldParameter
      · exact fresh
    · intro inst member
      rcases instructions inst member with old | fresh
      · exact checked.resolved.annotations inst old
      · exact fresh.2

theorem EmittedStatic.appendInst {module : Core.Module} {before : LS}
    (checked : EmittedStatic module before) (block : BlockId) (inst : Inst)
    (profile : EmittedProfileInst module.profile inst)
    (annotation : EmittedAnnotationResolved module inst) :
    EmittedStatic module (before.appendInst block inst) := by
  apply checked.of_transport
  · intro body member parameter atParameter
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    change (before.blocks.modify block fun b => { b with insts := b.insts.push inst })[index]? = some body at lookup
    rw [Array.getElem?_modify] at lookup
    by_cases same : block = index
    · simp only [same, ↓reduceIte] at lookup
      cases old : before.blocks[index]? with
      | none => simp [old] at lookup
      | some prior =>
        simp only [old, Option.map_some, Option.some.injEq] at lookup
        subst body
        exact Or.inl ⟨prior, Array.mem_toList_iff.mpr (Array.mem_of_getElem? old), atParameter⟩
    · simp only [same, ↓reduceIte] at lookup
      exact Or.inl ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), atParameter⟩
  · intro next member
    rcases insts_appendInst_member member with old | rfl
    · exact Or.inl old
    · exact Or.inr ⟨profile, annotation⟩

end Goose.Lower.Validation
