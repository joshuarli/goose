import Goose.Evidence.Execution

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Goose.GIR

def symbolDefStep (n d : Nat) (seen : Array Bool) : Except String (ForInStep (Array Bool)) := do
  unless d < n do throw s!"value %{d} is outside the value table of {n}"
  if seen[d]! then throw s!"value %{d} is defined twice"
  pure (.yield (seen.set! d true))

def symbolBlockStep (m : Module) (f : Func) (b : Block) (seen : Array Bool) :
    Except String (ForInStep (Array Bool)) := do
  let seen ← forIn b.defs seen (symbolDefStep f.numValues)
  for i in b.insts do
    checkInstSymbols m f f.numValues i
  pure (.yield seen)

theorem checkSymbols_definition_scan {m : Module} {label : String} {f : Func}
    (h : checkSymbols m label f = .ok ()) :
    ∃ seen, forIn f.blocks (Array.replicate f.numValues false) (symbolBlockStep m f) = .ok seen := by
  unfold checkSymbols at h
  have h := asCheck_ok h
  repeat' first
    | exact ⟨_, by assumption⟩
    | obtain ⟨_, _, h⟩ := bind_ok h
    | dsimp only at h
    | split at h
    | contradiction
    | simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

theorem symbolDef_scan {n : Nat} {xs : List Nat} {seen out : Array Bool}
    (hsize : seen.size = n)
    (h : forIn xs seen (symbolDefStep n) = .ok out) :
    xs.Nodup ∧ (∀ v ∈ xs, seen[v]! ≠ true) ∧
      out.size = n ∧ (∀ v, out[v]! = true ↔ seen[v]! = true ∨ v ∈ xs) := by
  induction xs generalizing seen out with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst out
    simp [hsize]
  | cons d ds ih =>
    rw [List.forIn_cons] at h
    unfold symbolDefStep at h
    have hd : d < n := by
      by_cases hd : d < n
      · exact hd
      · simp [hd, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    rw [if_pos hd] at h
    have hs : seen[d]! ≠ true := by
      intro hs
      simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    rw [if_neg hs] at h
    simp only [pure, Except.pure, bind, Except.bind] at h
    have hdsize : d < seen.size := by omega
    have hset : (seen.set! d true).size = n := by simpa using hsize
    obtain ⟨hn, hnot, hout, hvals⟩ := ih hset h
    have hdnot : d ∉ ds := by
      intro hmem
      exact hnot d hmem (Array.getElem!_set!_self seen d true hdsize)
    refine ⟨List.nodup_cons.mpr ⟨hdnot, hn⟩, ?_, hout, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hs
      · by_cases hne : d = v
        · subst v; exact hs
        · have hvnot := hnot v hv
          rw [Array.getElem!_set!_ne seen d v true hne] at hvnot
          exact hvnot
    · intro v
      rw [hvals]
      by_cases hne : d = v
      · subst v
        rw [Array.getElem!_set!_self seen d true hdsize]
        simp
      · rw [Array.getElem!_set!_ne seen d v true hne]
        simp [List.mem_cons, Ne.symm hne]

theorem symbolBlock_scan {m : Module} {f : Func} {bs : List Block} {seen out : Array Bool}
    (hsize : seen.size = f.numValues)
    (h : forIn bs seen (symbolBlockStep m f) = .ok out) :
    (bs.flatMap Block.defs).Nodup ∧
      (∀ v ∈ bs.flatMap Block.defs, seen[v]! ≠ true) ∧
      out.size = f.numValues ∧
      (∀ v, out[v]! = true ↔ seen[v]! = true ∨ v ∈ bs.flatMap Block.defs) := by
  induction bs generalizing seen out with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    subst out
    simp [hsize]
  | cons b bs ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step, hstep, hrest⟩ := bind_ok h
    unfold symbolBlockStep at hstep
    obtain ⟨mid, hdefs, hstep⟩ := bind_ok hstep
    obtain ⟨_, _, hstep⟩ := bind_ok hstep
    simp only [pure, Except.pure, Except.ok.injEq] at hstep
    subst step
    obtain ⟨hn, hnot, hmid, hvals⟩ := symbolDef_scan hsize hdefs
    obtain ⟨htail, htno, hout, htvals⟩ := ih hmid hrest
    have hdisj : ∀ a ∈ b.defs, ∀ c ∈ bs.flatMap Block.defs, a ≠ c := by
      intro a ha c hc he
      subst c
      exact htno a hc ((hvals a).mpr (Or.inr ha))
    refine ⟨?_, ?_, hout, ?_⟩
    · simpa only [List.flatMap_cons] using List.nodup_append.mpr ⟨hn, htail, hdisj⟩
    · intro v hv
      simp only [List.flatMap_cons, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hnot v hv
      · intro hs
        exact htno v hv ((hvals v).mpr (Or.inl hs))
    · intro v
      simp only [List.flatMap_cons, List.mem_append]
      rw [htvals, hvals]
      exact or_assoc

theorem definitions_nodup_of_symbols {m : Module} {label : String} {f : Func}
    (h : checkSymbols m label f = .ok ()) : (f.blocks.toList.flatMap Block.defs).Nodup := by
  obtain ⟨out, hout⟩ := checkSymbols_definition_scan h
  rw [← Array.forIn_toList] at hout
  exact (symbolBlock_scan (by simp) hout).1

theorem validated_definitions_nodup {m : Module} {f : Func}
    (h : validate m = .ok ()) (hf : f ∈ m.allFuncs) :
    (f.blocks.toList.flatMap Block.defs).Nodup := by
  unfold validate at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨checked, hs, _⟩ := bind_ok h
  cases checked
  simp only [Module.allFuncs, List.mem_append, List.mem_map] at hf
  rcases hf with hf | ⟨g, hg, rfl⟩
  · apply definitions_nodup_of_symbols (label := s!"function {f.name}")
    exact checkAll_mem (x := (s!"function {f.name}", f)) hs
      (by
        simp only [Module.labelled, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨f, hf, rfl⟩))
  · apply definitions_nodup_of_symbols (label := s!"initializer of global {g.name}")
    exact checkAll_mem (x := (s!"initializer of global {g.name}", g.init)) hs
      (by
        simp only [Module.labelled, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨g, hg, rfl⟩))

def Inst.definitionEntry : Inst → Option (ValueId × Option Op)
  | .def result op => some (result, some op)
  | _ => none

def Block.definitionEntries (block : Block) : List (ValueId × Option Op) :=
  block.params.map (fun param => (param.1, none)) ++ block.insts.filterMap Inst.definitionEntry

def Func.definitionEntries (fn : Func) : List (ValueId × Option Op) :=
  fn.blocks.toList.flatMap Block.definitionEntries

theorem definitionEntries_ids (block : Block) : block.definitionEntries.map Prod.fst = block.defs := by
  simp only [Block.definitionEntries, Block.defs, List.map_append, List.map_map]
  congr 1
  induction block.insts with
  | nil => rfl
  | cons inst rest ih =>
    cases inst <;> simp_all [Inst.definitionEntry, List.filterMap_cons]

theorem definitionEntries_ids_func (fn : Func) :
    fn.definitionEntries.map Prod.fst = fn.blocks.toList.flatMap Block.defs := by
  simp only [Func.definitionEntries, List.map_flatMap]
  exact congrArg (List.flatMap · fn.blocks.toList) (funext definitionEntries_ids)

theorem entry_eq_of_nodup_ids {β : Type} {entries : List (ValueId × β)}
    (h : (entries.map Prod.fst).Nodup) {a b : ValueId × β}
    (ha : a ∈ entries) (hb : b ∈ entries) (he : a.1 = b.1) : a = b := by
  induction entries with
  | nil => simp at ha
  | cons entry entries ih =>
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

theorem definitionEntry_mem {fn : Func} {block : Block} {result : ValueId} {op : Op}
    (hb : block ∈ fn.blocks) (hi : Inst.def result op ∈ block.insts) :
    (result, some op) ∈ fn.definitionEntries := by
  apply List.mem_flatMap.mpr
  refine ⟨block, Array.mem_toList_iff.mpr hb, ?_⟩
  simp only [Block.definitionEntries, List.mem_append]
  exact Or.inr (List.mem_filterMap.mpr ⟨.def result op, hi, rfl⟩)

theorem parameterEntry_mem {fn : Func} {block : Block} {value : ValueId}
    (hb : block ∈ fn.blocks) (hp : value ∈ block.params.map Prod.fst) :
    (value, none) ∈ fn.definitionEntries := by
  obtain ⟨param, hparam, hvalue⟩ := List.mem_map.mp hp
  apply List.mem_flatMap.mpr
  refine ⟨block, Array.mem_toList_iff.mpr hb, ?_⟩
  simp only [Block.definitionEntries, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨param, hparam, by simp [hvalue]⟩)

theorem validated_defOp_not_param {m : Module} {fn : Func} {value : ValueId} {op : Op}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (found : fn.defOp? value = some op) :
    ∀ block ∈ fn.blocks, value ∉ block.params.map Prod.fst := by
  have nodup := validated_definitions_nodup valid member
  rw [← definitionEntries_ids_func] at nodup
  obtain ⟨block, hb, hi⟩ := Goose.Evidence.defOp_member found
  intro other ho hp
  have equal := entry_eq_of_nodup_ids nodup (definitionEntry_mem hb hi)
    (parameterEntry_mem ho hp) rfl
  cases equal

theorem validated_instAt_defOp_eq {m : Module} {fn : Func} {value : ValueId}
    {op sampledOp : Op} {samplePt : Pt}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (found : fn.defOp? value = some op)
    (sample : instAt fn samplePt = some (.def value sampledOp)) : sampledOp = op := by
  have nodup := validated_definitions_nodup valid member
  rw [← definitionEntries_ids_func] at nodup
  obtain ⟨block, hb, hi⟩ := Goose.Evidence.defOp_member found
  obtain ⟨other, ho, hs⟩ := Goose.Evidence.instAt_member sample
  have equal := entry_eq_of_nodup_ids nodup (definitionEntry_mem ho hs)
    (definitionEntry_mem hb hi) rfl
  exact Option.some.inj (congrArg Prod.snd equal)

def Block.definitionLocations (block : Block) (id : Nat) : List (ValueId × (Nat × Int)) :=
  block.params.map (fun param => (param.1, (id, -1))) ++
    block.insts.zipIdx.filterMap fun (inst, index) => match inst with
      | .def result _ => some (result, (id, (index : Int)))
      | _ => none

def Func.definitionLocations (fn : Func) : List (ValueId × (Nat × Int)) :=
  fn.blocks.toList.zipIdx.flatMap fun (block, id) => block.definitionLocations id

theorem definitionLocations_ids (block : Block) (id : Nat) :
    (block.definitionLocations id).map Prod.fst = block.defs := by
  simp only [Block.definitionLocations, Block.defs, List.map_append, List.map_map]
  congr 1
  have scan : ∀ (insts : List Inst) (start : Nat),
      (insts.zipIdx start |>.filterMap fun (inst, index) => match inst with
        | .def result _ => some (result, (id, (index : Int)))
        | _ => none).map Prod.fst = insts.filterMap (fun inst => match inst with
          | .def result _ => some result
          | _ => none) := by
    intro insts
    induction insts with
    | nil => intro start; rfl
    | cons inst rest ih =>
      intro start
      cases inst <;> simp [List.zipIdx_cons, List.filterMap_cons, ih]
  exact scan block.insts 0

theorem definitionLocations_ids_func (fn : Func) :
    fn.definitionLocations.map Prod.fst = fn.blocks.toList.flatMap Block.defs := by
  simp only [Func.definitionLocations, List.map_flatMap]
  have rows : (fun pair : Block × Nat => (pair.1.definitionLocations pair.2).map Prod.fst) =
      (fun pair : Block × Nat => pair.1.defs) := by
    funext pair
    exact definitionLocations_ids pair.1 pair.2
  rw [rows]
  have hmap := congrArg (List.flatMap Block.defs) (List.zipIdx_map_fst 0 fn.blocks.toList)
  simpa only [List.flatMap_map] using hmap

theorem definitionLocation_mem {fn : Func} {pt : Pt} {value : ValueId} {op : Op}
    (instruction : instAt fn pt = some (.def value op)) :
    (value, (pt.1, (pt.2 : Int))) ∈ fn.definitionLocations := by
  unfold instAt at instruction
  cases found : fn.blocks[pt.1]? with
  | none => simp [found] at instruction
  | some block =>
    simp only [found, Option.bind_some] at instruction
    apply List.mem_flatMap.mpr
    refine ⟨(block, pt.1), ?_, ?_⟩
    · apply List.mem_of_getElem? (i := pt.1)
      simp [List.getElem?_zipIdx, found]
    · simp only [Block.definitionLocations, List.mem_append]
      apply Or.inr
      apply List.mem_filterMap.mpr
      refine ⟨(.def value op, pt.2), ?_, rfl⟩
      apply List.mem_of_getElem? (i := pt.2)
      simp [List.getElem?_zipIdx, instruction]

theorem parameterLocation_mem {fn : Func} {block : Block} {id value : ValueId}
    (found : fn.blocks[id]? = some block) (parameter : value ∈ block.params.map Prod.fst) :
    (value, (id, (-1 : Int))) ∈ fn.definitionLocations := by
  obtain ⟨param, hparam, hvalue⟩ := List.mem_map.mp parameter
  apply List.mem_flatMap.mpr
  refine ⟨(block, id), ?_, ?_⟩
  · apply List.mem_of_getElem? (i := id)
    simp [List.getElem?_zipIdx, found]
  · simp only [Block.definitionLocations, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨param, hparam, by simp [hvalue]⟩)

theorem validated_definition_locations_unique {m : Module} {fn : Func}
    {value : ValueId} {left right : Nat × Int}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (leftMem : (value, left) ∈ fn.definitionLocations)
    (rightMem : (value, right) ∈ fn.definitionLocations) : left = right := by
  have nodup := validated_definitions_nodup valid member
  rw [← definitionLocations_ids_func] at nodup
  exact congrArg Prod.snd (entry_eq_of_nodup_ids nodup leftMem rightMem rfl)

theorem validated_instAt_def_unique {m : Module} {fn : Func} {value : ValueId}
    {op otherOp : Op} {left right : Pt}
    (valid : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (leftInst : instAt fn left = some (.def value op))
    (rightInst : instAt fn right = some (.def value otherOp)) : left = right := by
  have equal := validated_definition_locations_unique valid member
    (definitionLocation_mem leftInst) (definitionLocation_mem rightInst)
  apply Prod.ext
  · exact congrArg (fun row : Nat × Int => row.1) equal
  · have equalIndex := congrArg (fun row : Nat × Int => row.2) equal
    omega

end Goose.GIR
