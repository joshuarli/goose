import Goose.Evidence.SSA

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Goose.GIR

open Goose.Core

theorem validated_checkTypes {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs) :
    ∃ label, checkTypes m label fn (fn.valueTypes m) = .ok () := by
  obtain ⟨info, hi, hfn, hvt⟩ := mem_infos hf
  refine ⟨info.label, ?_⟩
  have checked := checkAll_mem (validate_stages h).1 hi
  simpa only [hfn, hvt] using checked

theorem checkTypes_instructions {m : Module} {fn : Func} {label : String}
    {vt : Array (Option VTy)} (h : checkTypes m label fn vt = .ok ()) :
    (∀ block ∈ fn.blocks, ∀ inst ∈ block.insts,
      checkInstTypes fn { m.tyEnv fn with vals := vt } vt inst = .ok ()) ∧
    (∃ entry, fn.blocks[0]? = some entry ∧
      entry.params.map Prod.snd = fn.params.map VTy.data) := by
  unfold checkTypes at h
  have h := asCheck_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, hb, he⟩ := bind_ok h
  refine ⟨fun block hblock inst hinst =>
    checkAll_mem (checkAll_mem hb (Array.mem_toList_iff.mpr hblock)) hinst, ?_⟩
  cases hentry : fn.blocks[0]? with
  | none => simp [hentry, throw, throwThe, MonadExceptOf.throw] at he
  | some entry =>
    refine ⟨entry, rfl, ?_⟩
    by_cases hp : entry.params.map Prod.snd = fn.params.map VTy.data
    · exact hp
    · simp [hentry, hp, throw, throwThe, MonadExceptOf.throw] at he

theorem validated_checkInstTypes {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {block : Block} (hb : block ∈ fn.blocks) {inst : Inst} (hi : inst ∈ block.insts) :
    checkInstTypes fn { m.tyEnv fn with vals := fn.valueTypes m }
      (fn.valueTypes m) inst = .ok () := by
  obtain ⟨label, checked⟩ := validated_checkTypes h hf
  exact (checkTypes_instructions checked).1 block hb inst hi

theorem validated_effect_types {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {block : Block} (hb : block ∈ fn.blocks) {effect : Effect}
    (hi : Inst.eff effect ∈ block.insts) :
    checkEffectTypes { m.tyEnv fn with vals := fn.valueTypes m } effect = .ok () :=
  validated_checkInstTypes h hf hb hi

theorem validated_term_types {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {block : Block} (hb : block ∈ fn.blocks) {term : Term}
    (hi : Inst.term term ∈ block.insts) :
    checkTermTypes fn { m.tyEnv fn with vals := fn.valueTypes m } term = .ok () :=
  validated_checkInstTypes h hf hb hi

theorem validated_entry_params {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs) :
    ∃ entry, fn.blocks[0]? = some entry ∧
      entry.params.map Prod.snd = fn.params.map VTy.data := by
  obtain ⟨label, checked⟩ := validated_checkTypes h hf
  exact (checkTypes_instructions checked).2

theorem forIn_unit_ok {ε α : Type} {xs : List α}
    {f : α → PUnit → Except ε (ForInStep PUnit)}
    (h : forIn xs PUnit.unit f = .ok ())
    (hy : ∀ x, ∀ u, ∀ step, f x u = .ok step → step = .yield PUnit.unit) :
    ∀ x ∈ xs, f x PUnit.unit = .ok (.yield PUnit.unit) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step, hs, hr⟩ := bind_ok h
    have he := hy a PUnit.unit step hs
    subst step
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs
    · exact ih hr x hx

theorem validated_ret_metadata {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {block : Block} (hb : block ∈ fn.blocks) {values : List ValueId} {org : Option OriginId}
    (hi : Inst.term (.ret values org) ∈ block.insts) :
    values.length = fn.results.length ∧
      ∀ pair ∈ values.zip fn.results,
        (fn.valueTypes m)[pair.1]? = some (some (.data pair.2)) := by
  have ht := validated_term_types h hf hb hi
  unfold checkTermTypes at ht
  dsimp only at ht
  have hlen : values.length = fn.results.length := by
    by_cases he : values.length = fn.results.length
    · exact he
    · simp [he, tyErr, bind, Except.bind] at ht
  rw [if_pos hlen] at ht
  obtain ⟨u, hloop, _⟩ := bind_ok ht
  cases u
  refine ⟨hlen, ?_⟩
  have hall := forIn_unit_ok hloop (by
    intro pair u step checked
    obtain ⟨ty, _, checked⟩ := bind_ok checked
    by_cases he : ty = pair.2
    · simpa [he, pure, Except.pure, bind, Except.bind] using checked.symm
    · simp [he, tyErr, bind, Except.bind] at checked)
  intro pair hp
  have checked := hall pair hp
  obtain ⟨ty, hd, checked⟩ := bind_ok checked
  have he : ty = pair.2 := by
    by_cases he : ty = pair.2
    · exact he
    · simp [he, tyErr, bind, Except.bind] at checked
  subst ty
  exact dataTy_of hd

end Goose.GIR
