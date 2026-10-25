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

private theorem checkTypes_instructions {m : Module} {fn : Func} {label : String}
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

private theorem forIn_unit_ok {ε α : Type} {xs : List α}
    {f : α → PUnit.{1} → Except ε (ForInStep PUnit.{1})}
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
  rw [ite_eq_left hlen] at ht
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

private theorem validated_checkSymbols {m : Module} {fn : Func}
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

private theorem symbolDef_bounds {n : Nat} {xs : List Nat} {seen out : Array Bool}
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
    rw [ite_eq_left hd] at hs
    by_cases hseen : seen[d]! = true
    · simp [hseen, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hs
    · simp [hseen, pure, Except.pure] at hs
      subst step
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hd
      · exact ih hr v hv

private theorem symbolBlock_bounds {m : Module} {fn : Func} {bs : List Block}
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

private theorem parameter_ids_sublist (blocks : List Block) :
    (blocks.flatMap Block.params).map Prod.fst |>.Sublist (blocks.flatMap Block.defs) := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
    simp only [List.flatMap_cons, List.map_append]
    exact (List.sublist_append_left _ _).append ih

private theorem parameter_eq_of_nodup_ids {params : List (ValueId × VTy)}
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

private theorem fold_params_preserves {params : List (ValueId × VTy)} {n value : Nat}
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

private theorem fold_params_sets {params : List (ValueId × VTy)} {n value : Nat}
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

private theorem valueTypes_go_preserves {step : Array (Option VTy) → Array (Option VTy) × Bool}
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

private def checkedEdge (label : String) (fn : Func) (vt : Array (Option VTy))
    (source target : BlockId) (args : List ValueId) : Check Unit := do
  let some dest := fn.blocks[target]? |
    violation .v020 s!"{label}: block {source} branches outside the block table"
  unless dest.params.length = args.length do
    violation .v020 s!"{label}: the branch from block {source} to block {target} passes {args.length} arguments for {dest.params.length} parameters"
  for (param, arg) in dest.params.zip args do
    unless vt[arg]? == some (some param.2) do
      violation .v020 s!"{label}: argument %{arg} of the branch from block {source} to block {target} has another type than parameter %{param.1}"

private theorem forIn'_unit_ok {ε α : Type} {xs : List α}
    {f : (x : α) → x ∈ xs → PUnit.{1} → Except ε (ForInStep PUnit.{1})}
    (h : forIn' xs PUnit.unit f = .ok PUnit.unit)
    (hy : ∀ x hx u step, f x hx u = .ok step → step = .yield PUnit.unit) :
    ∀ x hx, f x hx PUnit.unit = .ok (.yield PUnit.unit) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.forIn'_cons] at h
    obtain ⟨step, hs, hr⟩ := bind_ok h
    have he := hy a List.mem_cons_self PUnit.unit step hs
    subst step
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs
    · exact ih hr (fun x hx u step => hy x (List.mem_cons_of_mem _ hx) u step) x hx

private theorem checkedEdge_metadata {label : String} {fn : Func}
    {vt : Array (Option VTy)} {source target : BlockId} {args : List ValueId}
    (h : checkedEdge label fn vt source target args = .ok ()) :
    ∃ dest, fn.blocks[target]? = some dest ∧ dest.params.length = args.length ∧
      ∀ pair ∈ dest.params.zip args, vt[pair.2]? = some (some pair.1.2) := by
  unfold checkedEdge at h
  cases hd : fn.blocks[target]? with
  | none => simp [hd, violation] at h
  | some dest =>
    rw [hd] at h
    dsimp only at h
    have hlen : dest.params.length = args.length := by
      by_cases he : dest.params.length = args.length
      · exact he
      · simp [he, violation, bind, Except.bind] at h
    rw [ite_eq_left hlen] at h
    obtain ⟨u, hloop, _⟩ := bind_ok h
    cases u
    have hall := forIn_unit_ok hloop (by
      intro pair u step checked
      by_cases he : vt[pair.2]? = some (some pair.1.2)
      · simpa [he, pure, Except.pure] using checked.symm
      · simp [he, violation, bind, Except.bind] at checked)
    refine ⟨dest, rfl, hlen, ?_⟩
    intro pair hp
    have checked := hall pair hp
    by_cases he : vt[pair.2]? = some (some pair.1.2)
    · exact he
    · simp [he, violation, bind, Except.bind] at checked

private theorem cfg_branch_checks {label : String} {fn : Func} {vt : Array (Option VTy)}
    (h : checkCfg label fn vt = .ok ()) :
    ∀ source (hs : source < fn.blocks.size),
      match fn.blocks[source].lastTerm? with
      | some (.br target args) => checkedEdge label fn vt source target args = .ok ()
      | some (.condbr _ target args other otherArgs) =>
        checkedEdge label fn vt source target args = .ok () ∧
          checkedEdge label fn vt source other otherArgs = .ok ()
      | _ => True := by
  unfold checkCfg at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨u, hloop, _⟩ := bind_ok h
  cases u
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at hloop
  have hall := forIn'_unit_ok hloop (by
    intro source hs u step checked
    have sourceLt : source < fn.blocks.size := by
      have hm := List.mem_range'.mp hs
      simp only [Std.Legacy.Range.size] at hm
      omega
    cases ht : fn.blocks[source].lastTerm? with
    | none => simpa [ht, pure, Except.pure] using checked.symm
    | some term =>
      cases term <;> simp only [ht] at checked
      all_goals
        repeat' first
          | exact (Except.ok.inj checked).symm
          | obtain ⟨_, _, checked⟩ := bind_ok checked
          | dsimp only at checked)
  intro source hs
  have hm : source ∈ List.range' 0 fn.blocks.size 1 := by
    exact List.mem_range'.mpr ⟨source, hs, by omega⟩
  have checked := hall source (by simpa [Std.Legacy.Range.size] using hm)
  cases ht : fn.blocks[source].lastTerm? with
  | none => trivial
  | some term =>
    simp only [ht] at checked
    cases term <;> dsimp only
    all_goals
      first
      | trivial
      | dsimp only at checked
        obtain ⟨_, hc, checked⟩ := bind_ok checked
        exact hc
      | dsimp only at checked
        obtain ⟨_, hc, checked⟩ := bind_ok checked
        obtain ⟨_, he, _⟩ := bind_ok checked
        exact ⟨hc, he⟩

private theorem map_eq_of_zip {α β γ : Type} {xs : List α} {ys : List β}
    {f : α → γ} {g : β → γ} (hl : xs.length = ys.length)
    (hz : ∀ pair ∈ xs.zip ys, f pair.1 = g pair.2) : xs.map f = ys.map g := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have he := hz (x, y) (by simp)
      have ht := ih hl (fun pair hp => hz pair (by simp [hp]))
      simp only [List.map_cons, he, ht]

theorem validated_branch_metadata {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {source : BlockId} (hs : source < fn.blocks.size)
    {target : BlockId} {args : List ValueId}
    (ht : fn.blocks[source].lastTerm? = some (.br target args)) :
    ∃ dest, fn.blocks[target]? = some dest ∧
      args.map (fun value => (fn.valueTypes m)[value]?) =
        dest.params.map (fun param => some (some param.2)) := by
  obtain ⟨info, hi, hfn, hvt⟩ := mem_infos hf
  have hc := checkAll_mem (validate_stages h).2.1 hi
  rw [hfn, hvt] at hc
  have checked := cfg_branch_checks hc source hs
  rw [ht] at checked
  obtain ⟨dest, hd, hl, hz⟩ := checkedEdge_metadata checked
  refine ⟨dest, hd, ?_⟩
  exact (map_eq_of_zip hl (fun pair hp => (hz pair hp).symm)).symm

theorem validated_condbranch_metadata {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {source : BlockId} (hs : source < fn.blocks.size)
    {condition : ValueId} {target other : BlockId} {args otherArgs : List ValueId}
    (ht : fn.blocks[source].lastTerm? = some (.condbr condition target args other otherArgs)) :
    (∃ dest, fn.blocks[target]? = some dest ∧
      args.map (fun value => (fn.valueTypes m)[value]?) =
        dest.params.map (fun param => some (some param.2))) ∧
    (∃ dest, fn.blocks[other]? = some dest ∧
      otherArgs.map (fun value => (fn.valueTypes m)[value]?) =
        dest.params.map (fun param => some (some param.2))) := by
  obtain ⟨info, hi, hfn, hvt⟩ := mem_infos hf
  have hc := checkAll_mem (validate_stages h).2.1 hi
  rw [hfn, hvt] at hc
  have checked := cfg_branch_checks hc source hs
  rw [ht] at checked
  constructor
  · obtain ⟨dest, hd, hl, hz⟩ := checkedEdge_metadata checked.1
    exact ⟨dest, hd, (map_eq_of_zip hl (fun pair hp => (hz pair hp).symm)).symm⟩
  · obtain ⟨dest, hd, hl, hz⟩ := checkedEdge_metadata checked.2
    exact ⟨dest, hd, (map_eq_of_zip hl (fun pair hp => (hz pair hp).symm)).symm⟩

theorem validated_term_last {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {block : Block} (hb : block ∈ fn.blocks) {term : Term}
    (hi : Inst.term term ∈ block.insts) : block.lastTerm? = some term := by
  obtain ⟨hl, hlast⟩ := (validate_sound m h).1 fn hf |>.1 block hb
  have hm : term ∈ block.terms := List.mem_filterMap.mpr ⟨.term term, hi, rfl⟩
  have unique : ∀ other ∈ block.terms, other = term := by
    intro other ho
    cases hs : block.terms with
    | nil => simp [hs] at hm
    | cons first rest =>
      have hr : rest = [] := by
        have hrlen : rest.length = 0 := by
          rw [hs] at hl
          simp only [List.length_cons] at hl
          omega
        exact List.eq_nil_of_length_eq_zero hrlen
      simp [hs, hr] at hm ho
      exact ho.trans hm.symm
  unfold Block.lastTerm? at hlast ⊢
  cases he : block.insts.getLast? with
  | none => simp [he] at hlast
  | some inst =>
    cases inst with
    | «def» result op => simp [he] at hlast
    | eff effect => simp [he] at hlast
    | term other =>
      have hmem : Inst.term other ∈ block.insts := by
        obtain ⟨front, hp⟩ := List.getLast?_eq_some_iff.mp he
        simp [hp]
      have ho : other ∈ block.terms := List.mem_filterMap.mpr ⟨.term other, hmem, rfl⟩
      simp [unique other ho]

theorem typing_env_slots (m : Module) (fn : Func) : (m.tyEnv fn).slots = fn.slots := rfl

theorem validated_instAt_term_last {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs) {pt : Pt} {term : Term}
    (hi : instAt fn pt = some (.term term)) :
    ∃ hs : pt.1 < fn.blocks.size, fn.blocks[pt.1].lastTerm? = some term := by
  unfold instAt at hi
  cases hb : fn.blocks[pt.1]? with
  | none => simp [hb] at hi
  | some block =>
    simp only [hb, Option.bind_some] at hi
    obtain ⟨hs, he⟩ := Array.getElem_of_getElem? hb
    refine ⟨hs, ?_⟩
    rw [he]
    exact validated_term_last h hf (Array.mem_of_getElem? hb) (List.mem_of_getElem? hi)

theorem typing_env_signature {m : Module} {fn callee : Func} {id : FnId}
    (h : m.funcs[id]? = some callee) :
    (m.tyEnv fn).sigs[id]? = some (callee.params, callee.results) := by
  change (m.funcs.map (fun f => (f.params, f.results)))[id]? = _
  simp [h]

private def checkedStructField (m : Core.Module) (desc : StructDef)
    (field : StructField) (endOffset : Nat) : Core.V (ForInStep Nat) := do
  Core.checkResolvedType m field.ty
  unless field.ty.flat do Core.reject .type "struct fields must be flat fixed values"
  let some bytes := m.fixedByteSize? field.ty |
    Core.reject .type "struct field has no fixed byte size"
  if bytes == 0 then Core.reject .type "zero-size struct field"
  if field.byteOffset < endOffset then Core.reject .type "struct fields overlap or are out of order"
  let fieldEnd := field.byteOffset + bytes
  if fieldEnd > desc.byteSize then Core.reject .type "struct field extends beyond its byte size"
  pure (.yield fieldEnd)

private def checkedStruct (m : Core.Module) (desc : StructDef) (_ : PUnit) :
    Core.V (ForInStep PUnit) := do
  if desc.byteSize == 0 then Core.reject .type "struct byte size must be positive"
  let _ ← forIn desc.fields 0 (checkedStructField m desc)
  pure (.yield PUnit.unit)

private theorem forIn_scan {ε α σ : Type} {xs : List α} {start finish : σ}
    {f : α → σ → Except ε (ForInStep σ)} {p : α → Prop}
    (h : forIn xs start f = .ok finish)
    (hs : ∀ x ∈ xs, ∀ st step, f x st = .ok step →
      ∃ st', step = .yield st' ∧ p x) : ∀ x ∈ xs, p x := by
  induction xs generalizing start finish with
  | nil => simp
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step, hc, hr⟩ := bind_ok h
    obtain ⟨mid, he, hp⟩ := hs x List.mem_cons_self start step hc
    subst step
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hp
    · exact ih hr (fun y hy st step => hs y (List.mem_cons_of_mem _ hy) st step) y hy

private theorem checkedStructField_flat {m : Core.Module} {desc : StructDef}
    {field : StructField} {endOffset : Nat} {step : ForInStep Nat}
    (h : checkedStructField m desc field endOffset = .ok step) :
    ∃ offset, step = .yield offset ∧ field.ty.flat = true := by
  unfold checkedStructField at h
  obtain ⟨_, _, h⟩ := bind_ok h
  have hf : field.ty.flat = true := by
    by_cases hf : field.ty.flat = true
    · exact hf
    · simp [hf, Core.reject, bind, Except.bind] at h
  repeat' first
    | exact ⟨_, (Except.ok.inj h).symm, hf⟩
    | obtain ⟨_, _, h⟩ := bind_ok h
    | dsimp only at h
    | split at h
    | simp only [Core.reject] at h
    | contradiction

private theorem checkedStruct_flat {m : Core.Module} {desc : StructDef}
    {u : PUnit} {step : ForInStep PUnit} (h : checkedStruct m desc u = .ok step) :
    ∃ out, step = .yield out ∧ ∀ field ∈ desc.fields, field.ty.flat = true := by
  unfold checkedStruct at h
  have hn : ¬desc.byteSize == 0 := by
    by_cases hn : desc.byteSize == 0
    · simp [hn, Core.reject, bind, Except.bind] at h
    · exact hn
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨offset, hf, h⟩ := bind_ok h
  refine ⟨PUnit.unit, (Except.ok.inj h).symm, ?_⟩
  rw [← Array.forIn_toList] at hf
  have hall := forIn_scan hf (fun _ _ _ _ checked => checkedStructField_flat checked)
  intro field hm
  exact hall field (Array.mem_toList_iff.mpr hm)

theorem validated_struct_fields_flat {m : Module} (h : validate m = .ok ()) :
    ∀ desc ∈ m.structs, ∀ field ∈ desc.fields, field.ty.flat = true := by
  unfold validate at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, hs, _⟩ := bind_ok h
  unfold checkStructTypes at hs
  obtain ⟨_, htables, _⟩ := bind_ok hs
  let cm : Core.Module :=
    { files := m.files, types := #[], globals := #[], impls := #[], contexts := #[],
      entry := 0, origins := m.origins, profile := m.profile, structs := m.structs }
  have hc : Core.checkStructTables cm = .ok () := by
    cases he : Core.checkStructTables cm with
    | ok u => cases u; rfl
    | error err => simp [cm, he, violation] at htables
  unfold Core.checkStructTables at hc
  dsimp only at hc
  have hn : ¬(cm.profile == .pilot && !cm.structs.isEmpty) = true := by
    intro hn
    simp [hn, Core.reject, bind, Except.bind] at hc
  rw [ite_eq_right hn] at hc
  obtain ⟨u, hloop, _⟩ := bind_ok hc
  cases u
  change forIn m.structs PUnit.unit (checkedStruct cm) = .ok PUnit.unit at hloop
  rw [← Array.forIn_toList] at hloop
  have hall := forIn_scan hloop (fun _ _ _ _ checked => checkedStruct_flat checked)
  intro desc hd
  exact hall desc (Array.mem_toList_iff.mpr hd)

private theorem structLit_metadata {env : TyEnv} {ty : Ty} {values : List ValueId}
    {result : VTy} (h : (Op.structLit ty values).resultTy env = .ok result) :
    ∃ (sid : StructId) (fields : TyList) (desc : StructDef),
      ty = .structT sid fields ∧ result = .data ty ∧ env.structs[sid]? = some desc ∧
      fields = TyList.ofList (desc.fields.toList.map (·.ty)) ∧
      values.map (fun value => env.vals[value]?) =
        desc.fields.toList.map (fun field => some (some (.data field.ty))) := by
  cases ty with
  | structT sid fields =>
    simp only [Op.resultTy] at h
    cases hd : env.structs[sid]? with
    | none => simp [hd, tyErr] at h
    | some desc =>
      rw [hd] at h
      dsimp only at h
      have hp : fields = TyList.ofList (desc.fields.toList.map (·.ty)) := by
        by_cases hp : fields = TyList.ofList (desc.fields.toList.map (·.ty))
        · exact hp
        · simp [hp, tyErr, bind, Except.bind] at h
      simp only [hp, beq_self_eq_true, ↓reduceIte] at h
      have hl : values.length = desc.fields.size := by
        by_cases hl : values.length = desc.fields.size
        · exact hl
        · simp [hl, tyErr, bind, Except.bind] at h
      simp only [hl, beq_self_eq_true, ↓reduceIte] at h
      obtain ⟨u, hloop, hresult⟩ := bind_ok h
      cases u
      have hall := forIn_unit_ok hloop (by
        intro pair u step checked
        obtain ⟨t, _, checked⟩ := bind_ok checked
        by_cases he : t = pair.2.ty
        · simpa [he, pure, Except.pure] using checked.symm
        · simp [he, tyErr, bind, Except.bind] at checked)
      refine ⟨sid, fields, desc, rfl, ?_, hd, hp, ?_⟩
      · simpa [hp, pure, Except.pure] using hresult.symm
      · apply map_eq_of_zip (by simpa using hl)
        intro pair hp
        have checked := hall pair hp
        obtain ⟨t, ht, checked⟩ := bind_ok checked
        have he : t = pair.2.ty := by
          by_cases he : t = pair.2.ty
          · exact he
          · simp [he, tyErr, bind, Except.bind] at checked
        subst t
        exact dataTy_of ht
  | _ => simp [Op.resultTy, tyErr] at h

theorem validated_structLit_operands {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {block : Block} (hb : block ∈ fn.blocks) {result : ValueId} {ty : Ty}
    {values : List ValueId} (hi : Inst.def result (.structLit ty values) ∈ block.insts) :
    ∀ value ∈ values, ∃ fieldTy,
      (fn.valueTypes m)[value]? = some (some (.data fieldTy)) ∧ fieldTy.flat = true := by
  obtain ⟨resultTy, checked, _⟩ := (validate_sound m h).1 fn hf |>.2.1 block hb result _ hi
  obtain ⟨sid, fields, desc, _, _, hd, _, hm⟩ := structLit_metadata checked
  change m.structs[sid]? = some desc at hd
  intro value hv
  have hmem : (fn.valueTypes m)[value]? ∈
      desc.fields.toList.map (fun field => some (some (.data field.ty))) := by
    rw [← hm]
    exact List.mem_map.mpr ⟨value, hv, rfl⟩
  obtain ⟨field, hfmem, he⟩ := List.mem_map.mp hmem
  exact ⟨field.ty, he.symm, validated_struct_fields_flat h desc
    (Array.mem_of_getElem? hd) field (Array.mem_toList_iff.mp hfmem)⟩

theorem call_resultTy_metadata {env : TyEnv} {id : FnId} {args : List ValueId}
    {org : Option OriginId} {result : VTy}
    (h : (Op.call id args org).resultTy env = .ok result) :
    ∃ params results, env.sigs[id]? = some (params, results) ∧
      params.length = args.length ∧
      (∀ pair ∈ params.zip args, ∃ argTy,
        env.vals[pair.2]? = some (some (.data argTy)) ∧ argTy.passableTo pair.1 = true) ∧
      ((results = [] ∧ result = .data .unit) ∨
        ∃ ty, results = [ty] ∧ result = .data ty) := by
  simp only [Op.resultTy] at h
  cases hs : env.sigs[id]? with
  | none => simp [hs, tyErr] at h
  | some sig =>
    rcases sig with ⟨params, results⟩
    rw [hs] at h
    dsimp only at h
    have hl : params.length = args.length := by
      by_cases hl : params.length = args.length
      · exact hl
      · simp [hl, tyErr, bind, Except.bind] at h
    rw [ite_eq_left hl] at h
    obtain ⟨u, hloop, hresult⟩ := bind_ok h
    cases u
    have hall := forIn_unit_ok hloop (by
      intro pair u step checked
      obtain ⟨ty, _, checked⟩ := bind_ok checked
      by_cases hp : ty.passableTo pair.1 = true
      · simpa [hp, pure, Except.pure] using checked.symm
      · simp [hp, tyErr, bind, Except.bind] at checked)
    refine ⟨params, results, rfl, hl, ?_, ?_⟩
    · intro pair hp
      have checked := hall pair hp
      obtain ⟨ty, ht, checked⟩ := bind_ok checked
      have hpass : ty.passableTo pair.1 = true := by
        by_cases hpass : ty.passableTo pair.1 = true
        · exact hpass
        · simp [hpass, tyErr, bind, Except.bind] at checked
      exact ⟨ty, dataTy_of ht, hpass⟩
    · cases results with
      | nil =>
        simp only [pure, Except.pure, Except.ok.injEq] at hresult
        exact Or.inl ⟨rfl, hresult.symm⟩
      | cons ty rest =>
        cases rest with
        | nil =>
          simp only [pure, Except.pure, Except.ok.injEq] at hresult
          exact Or.inr ⟨ty, rfl, hresult.symm⟩
        | cons next more => simp [tyErr] at hresult

theorem validated_call_operands {m : Module} {fn : Func}
    (h : validate m = .ok ()) (hf : fn ∈ m.allFuncs)
    {block : Block} (hb : block ∈ fn.blocks) {result : ValueId} {id : FnId}
    {args : List ValueId} {org : Option OriginId}
    (hi : Inst.def result (.call id args org) ∈ block.insts) :
    ∃ callee, m.funcs[id]? = some callee ∧ callee.params.length = args.length ∧
      (∀ pair ∈ callee.params.zip args, ∃ argTy,
        (fn.valueTypes m)[pair.2]? = some (some (.data argTy)) ∧
          argTy.passableTo pair.1 = true) ∧
      ((callee.results = [] ∧ (fn.valueTypes m)[result]? = some (some (.data .unit))) ∨
        ∃ ty, callee.results = [ty] ∧
          (fn.valueTypes m)[result]? = some (some (.data ty))) := by
  obtain ⟨resultTy, checked, hmeta⟩ := (validate_sound m h).1 fn hf |>.2.1 block hb result _ hi
  obtain ⟨params, results, hs, hl, ha, hr⟩ := call_resultTy_metadata checked
  change (m.funcs.map (fun f => (f.params, f.results)))[id]? = some (params, results) at hs
  cases hc : m.funcs[id]? with
  | none => simp [hc] at hs
  | some callee =>
    have he : (callee.params, callee.results) = (params, results) := by simpa [hc] using hs
    cases he
    refine ⟨callee, rfl, hl, ha, ?_⟩
    rcases hr with ⟨he, ht⟩ | ⟨ty, he, ht⟩
    · exact Or.inl ⟨he, ht ▸ hmeta⟩
    · exact Or.inr ⟨ty, he, ht ▸ hmeta⟩

theorem refTy_of {env : TyEnv} {value : ValueId} {permission : Mutability} {ty : Ty}
    (h : env.refTy value = .ok (permission, ty)) :
    env.vals[value]? = some (some (.data (.ref permission ty))) := by
  unfold TyEnv.refTy at h
  obtain ⟨data, hd, h⟩ := bind_ok h
  cases data with
  | ref m t =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact dataTy_of hd
  | _ => simp [tyErr] at h

theorem viewTy_of {env : TyEnv} {value : ValueId} {permission : Mutability} {ty : Ty}
    (h : env.viewTy value = .ok (permission, ty)) :
    env.vals[value]? = some (some (.view permission ty)) := by
  unfold TyEnv.viewTy at h
  obtain ⟨valueTy, hv, h⟩ := bind_ok h
  cases valueTy with
  | view m t =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact valTy_of hv
  | data ty => simp [tyErr] at h

theorem validated_entry_and_global_signatures {m : Module} (h : validate m = .ok ()) :
    (∃ entry, m.funcs[m.entry]? = some entry ∧ entry.params = [] ∧ entry.results = []) ∧
      (∀ global ∈ m.globals, global.init.params = [] ∧ global.init.results = [global.ty]) := by
  unfold validate at h
  obtain ⟨_, hc, _⟩ := bind_ok h
  unfold checkEntryAndGlobals at hc
  cases hl : m.funcs[m.entry]? with
  | none => simp [hl, violation, bind, Except.bind] at hc
  | some entry =>
    have hs : (entry.params.isEmpty && entry.results.isEmpty) = true := by
      by_cases hs : (entry.params.isEmpty && entry.results.isEmpty) = true
      · exact hs
      · simp [hl, hs, violation, bind, Except.bind] at hc
    simp only [hl, hs, ↓reduceIte] at hc
    refine ⟨⟨entry, rfl, by simpa using hs⟩, ?_⟩
    obtain ⟨u, hloop, _⟩ := bind_ok hc
    cases u
    rw [← Array.forIn_toList] at hloop
    have hall := forIn_unit_ok hloop (by
      intro global u step checked
      repeat' first
        | exact (Except.ok.inj checked).symm
        | obtain ⟨_, _, checked⟩ := bind_ok checked
        | dsimp only at checked
        | split at checked
        | simp only [violation, bind, Except.bind] at checked
        | contradiction)
    intro global hglobal
    have checked := hall global (Array.mem_toList_iff.mpr hglobal)
    have hs : (global.init.params.isEmpty && global.init.results == [global.ty]) = true := by
      by_cases hs : (global.init.params.isEmpty && global.init.results == [global.ty]) = true
      · exact hs
      · simp [hs, violation, bind, Except.bind] at checked
    simpa using hs

private theorem dataType_check_metadata {env : TyEnv} {value : ValueId} {expected : Ty}
    {message : String}
    (h : (env.dataTy value >>= fun actual =>
      if actual = expected then pure () else tyErr message) = .ok ()) :
    env.vals[value]? = some (some (.data expected)) := by
  obtain ⟨actual, ht, h⟩ := bind_ok h
  have he : actual = expected := by
    by_cases he : actual = expected
    · exact he
    · simp [he, tyErr] at h
  subst actual
  exact dataTy_of ht

theorem slotInit_types_of {env : TyEnv} {slot : SlotId} {value : ValueId}
    {org : Option OriginId} (h : checkEffectTypes env (.slotInit slot value org) = .ok ()) :
    ∃ desc, env.slots[slot]? = some desc ∧
      env.vals[value]? = some (some (.data desc.ty)) := by
  simp only [checkEffectTypes] at h
  cases hs : env.slots[slot]? with
  | none => simp [hs, tyErr] at h
  | some desc =>
    rw [hs] at h
    exact ⟨desc, rfl, dataType_check_metadata h⟩

theorem store_types_of {env : TyEnv} {reference value : ValueId} {org : Option OriginId}
    (h : checkEffectTypes env (.store reference value org) = .ok ()) :
    ∃ permission ty, env.vals[reference]? = some (some (.data (.ref permission ty))) ∧
      env.vals[value]? = some (some (.data ty)) := by
  simp only [checkEffectTypes] at h
  obtain ⟨⟨permission, ty⟩, hr, h⟩ := bind_ok h
  exact ⟨permission, ty, refTy_of hr, dataType_check_metadata h⟩

theorem append_types_of {env : TyEnv} {reference value : ValueId} {org : Option OriginId}
    (h : checkEffectTypes env (.append reference value org) = .ok ()) :
    ∃ permission owner elem viewPermission,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      owner.ownerElem? = some elem ∧
      env.vals[value]? = some (some (.view viewPermission elem)) := by
  simp only [checkEffectTypes] at h
  obtain ⟨⟨permission, owner⟩, hr, h⟩ := bind_ok h
  cases owner with
  | grow elem | growshrink elem | limited elem capacity =>
    obtain ⟨⟨viewPermission, actual⟩, hv, h⟩ := bind_ok h
    have he : actual = elem := by
      by_cases he : actual = elem
      · exact he
      · simp [he, tyErr] at h
    subst actual
    exact ⟨permission, _, elem, viewPermission, refTy_of hr, rfl, viewTy_of hv⟩
  | _ => simp [tyErr] at h

theorem popN_types_of {env : TyEnv} {reference count : ValueId} {org : Option OriginId}
    (h : checkEffectTypes env (.popN reference count org) = .ok ()) :
    ∃ permission owner elem countTy,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      owner.ownerElem? = some elem ∧
      env.vals[count]? = some (some (.data (.int countTy))) := by
  simp only [checkEffectTypes] at h
  obtain ⟨⟨permission, owner⟩, hr, h⟩ := bind_ok h
  have he : owner.ownerElem?.isSome = true := by
    by_cases he : owner.ownerElem?.isSome = true
    · exact he
    · simp [he, tyErr, bind, Except.bind] at h
  rw [ite_eq_left he] at h
  obtain ⟨countTy, hc, _⟩ := bind_ok h
  cases ho : owner.ownerElem? with
  | none => simp [ho] at he
  | some elem => exact ⟨permission, owner, elem, countTy, refTy_of hr, ho, intTy_of hc⟩

theorem resize_types_of {env : TyEnv} {reference size : ValueId} {fill : Option ValueId}
    {org : Option OriginId} (h : checkEffectTypes env (.resize reference size fill org) = .ok ()) :
    ∃ permission owner elem sizeTy,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      owner.ownerElem? = some elem ∧
      env.vals[size]? = some (some (.data (.int sizeTy))) ∧
      (∀ value, fill = some value → env.vals[value]? = some (some (.data elem))) := by
  simp only [checkEffectTypes] at h
  obtain ⟨⟨permission, owner⟩, hr, h⟩ := bind_ok h
  cases ho : owner.ownerElem? with
  | none => simp [ho, tyErr] at h
  | some elem =>
    rw [ho] at h
    obtain ⟨sizeTy, hs, h⟩ := bind_ok h
    refine ⟨permission, owner, elem, sizeTy, refTy_of hr, ho, intTy_of hs, ?_⟩
    intro value hv
    subst fill
    exact dataType_check_metadata h

theorem clear_types_of {env : TyEnv} {reference : ValueId} {org : Option OriginId}
    (h : checkEffectTypes env (.clear reference org) = .ok ()) :
    ∃ permission owner elem,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      owner.ownerElem? = some elem := by
  simp only [checkEffectTypes] at h
  obtain ⟨⟨permission, owner⟩, hr, h⟩ := bind_ok h
  have he : owner.ownerElem?.isSome = true := by
    by_cases he : owner.ownerElem?.isSome = true
    · exact he
    · simp [he, tyErr] at h
  cases ho : owner.ownerElem? with
  | none => simp [ho] at he
  | some elem => exact ⟨permission, owner, elem, refTy_of hr, ho⟩

theorem replace_types_of {env : TyEnv} {reference run : ValueId} {org : Option OriginId}
    (h : checkEffectTypes env (.replace reference run org) = .ok ()) :
    ∃ permission owner elem,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      (owner = .grow elem ∨ owner = .growshrink elem) ∧
      env.vals[run]? = some (some (.data owner)) := by
  simp only [checkEffectTypes] at h
  obtain ⟨⟨permission, owner⟩, hr, h⟩ := bind_ok h
  cases owner with
  | grow elem => exact ⟨permission, _, elem, refTy_of hr, Or.inl rfl, dataType_check_metadata h⟩
  | growshrink elem => exact ⟨permission, _, elem, refTy_of hr, Or.inr rfl, dataType_check_metadata h⟩
  | _ => simp [tyErr, bind, Except.bind] at h

theorem print_types_of {env : TyEnv} {parts : List PrintPart} {org : Option OriginId}
    (h : checkEffectTypes env (.print parts org) = .ok ()) :
    ∀ value, PrintPart.val value ∈ parts →
      (∃ intTy, env.vals[value]? = some (some (.data (.int intTy)))) ∨
        env.vals[value]? = some (some (.data .bool)) := by
  simp only [checkEffectTypes] at h
  obtain ⟨u, hloop, _⟩ := bind_ok h
  cases u
  have hall := forIn_unit_ok hloop (by
    intro part u step checked
    cases part with
    | text text => exact (Except.ok.inj checked).symm
    | val value =>
      obtain ⟨ty, _, checked⟩ := bind_ok checked
      cases ty <;> simp [pure, Except.pure, tyErr, bind, Except.bind] at checked
      all_goals exact checked.symm)
  intro value hv
  have checked := hall (.val value) hv
  obtain ⟨ty, ht, checked⟩ := bind_ok checked
  cases ty with
  | int t => exact Or.inl ⟨t, dataTy_of ht⟩
  | bool => exact Or.inr (dataTy_of ht)
  | _ => simp [tyErr, bind, Except.bind] at checked

private theorem tyList_toList_ofList (types : List Ty) :
    (TyList.ofList types).toList = types := by
  induction types with
  | nil => rfl
  | cons ty rest ih => simp [TyList.ofList, TyList.toList, ih]

theorem structLit_types_of {env : TyEnv} {ty : Ty} {values : List ValueId} {result : VTy}
    (h : (Op.structLit ty values).resultTy env = .ok result) :
    ∃ sid fields, ty = .structT sid fields ∧ result = .data ty ∧
      values.map (fun value => env.vals[value]?) =
        fields.toList.map (fun fieldTy => some (some (.data fieldTy))) := by
  obtain ⟨sid, fields, desc, hty, hr, _, hf, hm⟩ := structLit_metadata h
  refine ⟨sid, fields, hty, hr, ?_⟩
  rw [hf, tyList_toList_ofList, List.map_map]
  exact hm

end Goose.GIR
