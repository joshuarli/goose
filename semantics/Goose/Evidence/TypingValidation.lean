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

theorem validated_checkSymbols {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs) :
    ∃ label, checkSymbols m label fn = .ok () := by
  unfold validate at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨checked, hs, _⟩ := bind_ok h
  cases checked
  simp only [Module.allFuncs, List.mem_append, List.mem_map] at hf
  rcases hf with hf | ⟨g, hg, rfl⟩
  · refine ⟨s!"function {fn.name}", ?_⟩
    exact checkAll_mem (x := (s!"function {fn.name}", fn)) hs
      (by
        simp only [Module.labelled, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨fn, hf, rfl⟩))
  · refine ⟨s!"initializer of global {g.name}", ?_⟩
    exact checkAll_mem (x := (s!"initializer of global {g.name}", g.init)) hs
      (by
        simp only [Module.labelled, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨g, hg, rfl⟩))

theorem symbolDef_bounds {n : Nat} {xs : List Nat} {seen out : Array Bool}
    (h : forIn xs seen (symbolDefStep n) = .ok out) : ∀ v ∈ xs, v < n := by
  induction xs generalizing seen out with
  | nil => simp
  | cons d ds ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step, hs, hr⟩ := bind_ok h
    unfold symbolDefStep at hs
    have hd : d < n := by
      by_cases hd : d < n
      · exact hd
      · simp [hd, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hs
    rw [if_pos hd] at hs
    by_cases hseen : seen[d]! = true
    · simp [hseen, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hs
    · simp [hseen, pure, Except.pure, bind, Except.bind] at hs
      subst step
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hd
      · exact ih hr v hv

theorem symbolBlock_bounds {m : Module} {fn : Func} {bs : List Block}
    {seen out : Array Bool}
    (h : forIn bs seen (symbolBlockStep m fn) = .ok out) :
    ∀ v ∈ bs.flatMap Block.defs, v < fn.numValues := by
  induction bs generalizing seen out with
  | nil => simp
  | cons block bs ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step, hs, hr⟩ := bind_ok h
    unfold symbolBlockStep at hs
    obtain ⟨mid, hd, hs⟩ := bind_ok hs
    obtain ⟨_, _, hs⟩ := bind_ok hs
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    subst step
    intro v hv
    simp only [List.flatMap_cons, List.mem_append] at hv
    rcases hv with hv | hv
    · exact symbolDef_bounds hd v hv
    · exact ih hr v hv

theorem validated_definition_bounds {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs) :
    ∀ v ∈ fn.blocks.toList.flatMap Block.defs, v < fn.numValues := by
  obtain ⟨label, checked⟩ := validated_checkSymbols h hf
  obtain ⟨seen, hs⟩ := checkSymbols_definition_scan checked
  rw [← Array.forIn_toList] at hs
  exact symbolBlock_bounds hs

theorem parameter_ids_sublist (blocks : List Block) :
    (blocks.flatMap Block.params).map Prod.fst |>.Sublist (blocks.flatMap Block.defs) := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
    simp only [List.flatMap_cons, List.map_append]
    exact (List.sublist_append_left _ _).append ih

theorem parameter_eq_of_nodup_ids {params : List (ValueId × VTy)}
    (h : (params.map Prod.fst).Nodup) {a b : ValueId × VTy}
    (ha : a ∈ params) (hb : b ∈ params) (he : a.1 = b.1) : a = b := by
  induction params with
  | nil => simp at ha
  | cons param params ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb.symm
      · exact False.elim (h.1 (List.mem_map.mpr ⟨b, hb, he.symm⟩))
    · rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact False.elim (h.1 (List.mem_map.mpr ⟨a, ha, he⟩))
      · exact ih h.2 ha hb

theorem fold_params_preserves {params : List (ValueId × VTy)} {n value : Nat}
    {ty : VTy} {vals : Array (Option VTy)}
    (hv : vals[value]? = some (some ty))
    (hc : ∀ param ∈ params, param.1 = value → param.2 = ty) :
    (params.foldl (fun a (v, t) => if v < n then a.set! v (some t) else a) vals)[value]? =
      some (some ty) := by
  induction params generalizing vals with
  | nil => exact hv
  | cons param params ih =>
    simp only [List.foldl_cons]
    apply ih
    · by_cases hn : param.1 < n
      · simp only [hn, ↓reduceIte]
        by_cases he : param.1 = value
        · have ht := hc param List.mem_cons_self he
          rw [he, ht]
          have hsize : value < vals.size := by
            by_cases hsize : value < vals.size
            · exact hsize
            · simp [Array.getElem?_eq_none (Nat.le_of_not_lt hsize)] at hv
          simp [Array.set!, hsize]
        · simp [Array.set!, he, hv]
      · simpa [hn] using hv
    · intro p hp he
      exact hc p (List.mem_cons_of_mem _ hp) he

theorem fold_params_sets {params : List (ValueId × VTy)} {n value : Nat}
    {ty : VTy} {vals : Array (Option VTy)} (hsize : vals.size = n) (hbound : value < n)
    (hp : (value, ty) ∈ params)
    (hc : ∀ param ∈ params, param.1 = value → param.2 = ty) :
    (params.foldl (fun a (v, t) => if v < n then a.set! v (some t) else a) vals)[value]? =
      some (some ty) := by
  induction params generalizing vals with
  | nil => simp at hp
  | cons param params ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with hp | hp
    · subst param
      simp only [hbound, ↓reduceIte]
      apply fold_params_preserves
      · simp [Array.set!, hsize, hbound]
      · intro p hp he
        exact hc p (List.mem_cons_of_mem _ hp) he
    · apply ih
      · by_cases hn : param.1 < n <;> simp [hn, hsize]
      · exact hp
      · intro p hp he
        exact hc p (List.mem_cons_of_mem _ hp) he

theorem valueTypes_go_preserves {step : Array (Option VTy) → Array (Option VTy) × Bool}
    {value : ValueId} {ty : VTy}
    (hs : ∀ vals, vals[value]? = some (some ty) →
      (step vals).1[value]? = some (some ty))
    (fuel : Nat) (vals : Array (Option VTy))
    (hv : vals[value]? = some (some ty)) :
    (Func.valueTypes.go step fuel vals)[value]? = some (some ty) := by
  induction fuel generalizing vals with
  | zero => exact hv
  | succ fuel ih =>
    simp only [Func.valueTypes.go]
    split
    · exact ih _ (hs vals hv)
    · exact hs vals hv

theorem validated_block_param_metadata {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {block : Block} (hb : block ∈ fn.blocks) {value : ValueId} {ty : VTy}
    (hp : (value, ty) ∈ block.params) :
    (fn.valueTypes m)[value]? = some (some ty) := by
  let params := fn.blocks.toList.flatMap Block.params
  have hpm : (value, ty) ∈ params :=
    List.mem_flatMap.mpr ⟨block, Array.mem_toList_iff.mpr hb, hp⟩
  have hn : (params.map Prod.fst).Nodup :=
    (parameter_ids_sublist fn.blocks.toList).nodup (validated_definitions_nodup h hf)
  have hbound : value < fn.numValues :=
    validated_definition_bounds h hf value
      ((parameter_ids_sublist fn.blocks.toList).subset (List.mem_map.mpr ⟨_, hpm, rfl⟩))
  have coherent : ∀ param ∈ params, param.1 = value → param.2 = ty := by
    intro param hm he
    have eq := parameter_eq_of_nodup_ids hn hm hpm he
    exact congrArg Prod.snd eq
  have hdef : ∀ b ∈ fn.blocks, ∀ result op, Inst.def result op ∈ b.insts → result ≠ value := by
    intro b hb' result op hi he
    have nodup := validated_definitions_nodup h hf
    rw [← definitionEntries_ids_func] at nodup
    have eq := entry_eq_of_nodup_ids nodup (definitionEntry_mem hb' hi)
      (parameterEntry_mem hb (List.mem_map.mpr ⟨_, hp, rfl⟩)) he
    cases eq
  unfold Func.valueTypes
  apply valueTypes_go_preserves
  · intro vals hv
    dsimp only
    rw [← Array.foldl_toList]
    apply List.foldlRecOn (motive := fun acc : Array (Option VTy) × Bool =>
      acc.1[value]? = some (some ty))
    · exact hv
    · intro acc ha b hbm
      apply List.foldlRecOn (motive := fun acc : Array (Option VTy) × Bool =>
        acc.1[value]? = some (some ty))
      · exact ha
      · intro acc ha inst hi
        rcases acc with ⟨arr, changed⟩
        cases inst with
        | eff effect => exact ha
        | term term => exact ha
        | «def» result op =>
          have hne := hdef b (Array.mem_toList_iff.mp hbm) result op hi
          dsimp only
          split
          · split
            · simpa [Array.set!, hne] using ha
            · exact ha
          · exact ha
  · rw [← Array.foldl_toList, ← List.foldl_flatMap]
    exact fold_params_sets (by simp) hbound hpm coherent

end Goose.GIR
