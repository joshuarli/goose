import Goose.Evidence.SSA

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Goose.GIR

open Goose.Core

def cfgDefAt (fn : Func) : Array (Option (BlockId × Int)) :=
  fn.blocks.zipIdx.foldl (fun (acc : Array (Option (BlockId × Int))) (blk, b) =>
    let acc := blk.params.foldl (fun acc (v, _) => acc.set! v (some (b, -1))) acc
    blk.insts.zipIdx.foldl (fun acc (i, k) =>
      match i with
      | .def r _ => acc.set! r (some (b, (k : Int)))
      | _ => acc) acc) (Array.replicate fn.numValues none)

def cfgUseScan (label : String) (fn : Func) : Check Unit := do
  for h : u in [0:fn.blocks.size] do
    for (i, k) in fn.blocks[u].insts.zipIdx do
      for v in i.uses do
        match (cfgDefAt fn)[v]? with
        | some (some (db, dk)) =>
          let ok := if db = u then decide (dk < (k : Int))
            else ((dominators fn (predecessors fn))[u]?.getD 0).testBit db
          unless ok do
            violation .v020 s!"{label}: value %{v} is used in block {u} where its definition in block {db} does not dominate the use"
        | _ => violation .v020 s!"{label}: value %{v} has no definition"

theorem validated_checkCfg {m : Module} {fn : Func}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs) :
    ∃ label, checkCfg label fn (fn.valueTypes m) = .ok () := by
  obtain ⟨info, hi, hfn, hvt⟩ := mem_infos member
  refine ⟨info.label, ?_⟩
  have checked := checkAll_mem (validate_stages valid).2.1 hi
  simpa only [hfn, hvt] using checked

theorem checkCfg_entry_and_useScan {label : String} {fn : Func}
    {vt : Array (Option VTy)} (checked : checkCfg label fn vt = .ok ()) :
    (predecessors fn)[0]?.getD [] = [] ∧ cfgUseScan label fn = .ok () := by
  unfold checkCfg at checked
  obtain ⟨_, _, checked⟩ := bind_ok checked
  obtain ⟨_, _, checked⟩ := bind_ok checked
  dsimp only at checked
  have hempty : ((predecessors fn)[0]?.getD []).isEmpty = true := by
    by_cases he : ((predecessors fn)[0]?.getD []).isEmpty = true
    · exact he
    · simp [he, violation, bind, Except.bind] at checked
  simp only [hempty, ↓reduceIte, pure, Except.pure,
    bind, Except.bind] at checked
  obtain ⟨_, _, checked⟩ := bind_ok checked
  refine ⟨List.isEmpty_iff.mp hempty, ?_⟩
  exact checked

private theorem cfg_forIn_ok {ε α : Type} {xs : List α}
    {f : α → PUnit → Except ε (ForInStep PUnit)}
    (checked : forIn xs PUnit.unit f = .ok ())
    (yields : ∀ x u step, f x u = .ok step → step = .yield ()) :
    ∀ x ∈ xs, f x () = .ok (.yield ()) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, hs, hr⟩ := bind_ok checked
    have he := yields a () step hs
    subst step
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs
    · exact ih hr x hx

private theorem cfg_forIn'_ok {ε α : Type} {xs : List α}
    {f : (x : α) → x ∈ xs → PUnit → Except ε (ForInStep PUnit)}
    (checked : forIn' xs PUnit.unit f = .ok ())
    (yields : ∀ x hx u step, f x hx u = .ok step → step = .yield ()) :
    ∀ x hx, f x hx () = .ok (.yield ()) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.forIn'_cons] at checked
    obtain ⟨step, hs, hr⟩ := bind_ok checked
    have he := yields a (List.mem_cons_self) () step hs
    subst step
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs
    · exact ih hr (fun x hx => yields x (List.mem_cons_of_mem a hx)) x hx

theorem cfgUseScan_operands {label : String} {fn : Func}
    (checked : cfgUseScan label fn = .ok ()) {u k : Nat} {inst : Inst}
    (hu : u < fn.blocks.size) (hi : fn.blocks[u].insts[k]? = some inst)
    {value : ValueId} (hv : value ∈ inst.uses) :
    ∃ db dk, (cfgDefAt fn)[value]? = some (some (db, dk)) ∧
      (if db = u then dk < (k : Int)
       else ((dominators fn (predecessors fn))[u]?.getD 0).testBit db = true) := by
  unfold cfgUseScan at checked
  obtain ⟨out, checked, _⟩ := bind_ok checked
  cases out
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at checked
  have hall := cfg_forIn'_ok checked (by
    intro x hx state step hs
    obtain ⟨out, _, hs⟩ := bind_ok hs
    simpa only [pure, Except.pure, Except.ok.injEq] using hs.symm)
  have hurange : u ∈ List.range' 0 (Std.Legacy.Range.size [:fn.blocks.size]) 1 := by
    simpa [Std.Legacy.Range.size, List.mem_range'] using hu
  have hb := hall u hurange
  obtain ⟨out, hb, _⟩ := bind_ok hb
  cases out
  have hinsts := cfg_forIn_ok hb (by
    intro x state step hs
    obtain ⟨out, _, hs⟩ := bind_ok hs
    simpa only [pure, Except.pure, Except.ok.injEq] using hs.symm)
  have hi' : (inst, k) ∈ fn.blocks[u].insts.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr hi
  have hiChecked := hinsts (inst, k) hi'
  obtain ⟨out, hiChecked, _⟩ := bind_ok hiChecked
  cases out
  have huses := cfg_forIn_ok hiChecked (by
    intro v state step hs
    cases hr : (cfgDefAt fn)[v]? with
    | none => simp [hr, violation, bind, Except.bind] at hs
    | some row =>
      cases row with
      | none => simp [hr, violation, bind, Except.bind] at hs
      | some site =>
        simp only [hr] at hs
        repeat' first
          | split at hs
          | simp_all [violation, bind, Except.bind, pure, Except.pure])
  have hvalue := huses value hv
  cases hr : (cfgDefAt fn)[value]? with
  | none => simp [hr, violation, bind, Except.bind] at hvalue
  | some row =>
    cases row with
    | none => simp [hr, violation, bind, Except.bind] at hvalue
    | some site =>
      obtain ⟨db, dk⟩ := site
      refine ⟨db, dk, rfl, ?_⟩
      dsimp only at hvalue
      by_cases he : db = u
      · by_cases hlt : dk < (k : Int)
        · simpa [he] using hlt
        · simp [hr, he, hlt, violation, bind, Except.bind] at hvalue
      · by_cases hbit : ((dominators fn (predecessors fn))[u]?.getD 0).testBit db = true
        · simpa [he] using hbit
        · simp [hr, he, hbit, violation, bind, Except.bind] at hvalue

private theorem cfg_fold_preserves {α β : Type} (xs : List α) (step : β → α → β)
    (predicate : β → Prop) (initial : β) (start : predicate initial)
    (advance : ∀ x ∈ xs, ∀ acc, predicate acc → predicate (step acc x)) :
    predicate (xs.foldl step initial) := by
  induction xs generalizing initial with
  | nil => exact start
  | cons x xs ih =>
    exact ih (step initial x) (advance x (by simp) initial start)
      (fun y hy => advance y (List.mem_cons_of_mem x hy))

private theorem cfg_set_origin {fn : Func} {acc : Array (Option (BlockId × Int))}
    {value : ValueId} {site : BlockId × Int}
    (prior : ∀ v loc, acc[v]? = some (some loc) → (v, loc) ∈ fn.definitionLocations)
    (origin : (value, site) ∈ fn.definitionLocations) :
    ∀ v loc, (acc.set! value (some site))[v]? = some (some loc) →
      (v, loc) ∈ fn.definitionLocations := by
  intro v loc found
  by_cases he : value = v
  · subst v
    by_cases hb : value < acc.size
    · simp [Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hb] at found
      subst loc
      exact origin
    · simp [Array.set!_eq_setIfInBounds, hb] at found
  · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne he] at found
    exact prior v loc found

theorem cfgDefAt_origin {fn : Func} {value : ValueId} {site : BlockId × Int}
    (found : (cfgDefAt fn)[value]? = some (some site)) :
    (value, site) ∈ fn.definitionLocations := by
  have invariant : ∀ v loc, (cfgDefAt fn)[v]? = some (some loc) →
      (v, loc) ∈ fn.definitionLocations := by
    unfold cfgDefAt
    rw [← Array.foldl_toList, Array.toList_zipIdx]
    apply cfg_fold_preserves (predicate := fun acc => ∀ v loc,
      acc[v]? = some (some loc) → (v, loc) ∈ fn.definitionLocations)
    · intro v loc h
      simp [Array.getElem?_replicate] at h
    · intro pair hp acc prior
      obtain ⟨block, id⟩ := pair
      have blockFound : fn.blocks[id]? = some block := by
        simpa using List.mk_mem_zipIdx_iff_getElem?.mp hp
      dsimp only
      apply cfg_fold_preserves (predicate := fun acc => ∀ v loc,
        acc[v]? = some (some loc) → (v, loc) ∈ fn.definitionLocations)
      · apply cfg_fold_preserves (predicate := fun acc => ∀ v loc,
          acc[v]? = some (some loc) → (v, loc) ∈ fn.definitionLocations) (start := prior)
        intro param hparam acc previous
        apply cfg_set_origin previous
        exact parameterLocation_mem blockFound (List.mem_map.mpr ⟨param, hparam, rfl⟩)
      · intro pair hinst acc previous
        obtain ⟨inst, index⟩ := pair
        cases inst with
        | «def» result op =>
          apply cfg_set_origin previous
          apply definitionLocation_mem (pt := (id, index))
          simp only [instAt, blockFound, Option.bind_some]
          exact List.mk_mem_zipIdx_iff_getElem?.mp hinst
        | eff effect => exact previous
        | term term => exact previous
  exact invariant value site found

theorem validated_entry_predecessors {m : Module} {fn : Func}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs) :
    (predecessors fn)[0]?.getD [] = [] := by
  obtain ⟨label, checked⟩ := validated_checkCfg valid member
  exact (checkCfg_entry_and_useScan checked).1

theorem validated_operand_definition {m : Module} {fn : Func} {pt : Pt} {inst : Inst}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (instruction : instAt fn pt = some inst) {value : ValueId}
    (operand : value ∈ inst.uses) :
    ∃ db dk, (value, (db, dk)) ∈ fn.definitionLocations ∧
      (cfgDefAt fn)[value]? = some (some (db, dk)) ∧
      (if db = pt.1 then dk < (pt.2 : Int)
       else ((dominators fn (predecessors fn))[pt.1]?.getD 0).testBit db = true) := by
  obtain ⟨label, checked⟩ := validated_checkCfg valid member
  unfold instAt at instruction
  cases hb : fn.blocks[pt.1]? with
  | none => simp [hb] at instruction
  | some block =>
    have hu : pt.1 < fn.blocks.size := by
      exact Array.getElem?_eq_some_iff.mp hb |>.1
    have hi : fn.blocks[pt.1].insts[pt.2]? = some inst := by
      obtain ⟨_, he⟩ := Array.getElem_of_getElem? hb
      simpa [hb, he] using instruction
    obtain ⟨db, dk, row, order⟩ := cfgUseScan_operands
      (checkCfg_entry_and_useScan checked).2 hu hi operand
    exact ⟨db, dk, cfgDefAt_origin row, row, order⟩

end Goose.GIR
