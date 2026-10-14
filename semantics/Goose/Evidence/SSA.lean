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
    | exact ⟨_, h⟩
    | obtain ⟨_, _, h⟩ := bind_ok h
    | progress dsimp only at h
    | split at h
    | contradiction
    | progress simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

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
    by_cases hd : d < n
    · rw [if_pos hd] at h
    · simp [hd, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    by_cases hs : seen[d]! = true
    · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
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
        · simpa [Array.getElem!_set!_ne seen d v true hne] using hnot v hv
    · intro v
      rw [hvals]
      by_cases hne : d = v
      · subst v
        simp [Array.getElem!_set!_self seen d true hdsize]
      · simp [Array.getElem!_set!_ne seen d v true hne, hne, List.mem_cons]

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
  obtain ⟨_, hs, _⟩ := bind_ok h
  apply definitions_nodup_of_symbols
  simp only [Module.allFuncs, List.mem_append, List.mem_map] at hf
  rcases hf with hf | ⟨g, hg, rfl⟩
  · exact checkAll_mem hs (by simp [Module.labelled, hf])
  · exact checkAll_mem hs (by simp [Module.labelled, hg])

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
    cases inst <;> simp_all [Inst.definitionEntry]

theorem definitionEntries_ids_func (fn : Func) :
    fn.definitionEntries.map Prod.fst = fn.blocks.toList.flatMap Block.defs := by
  simp only [Func.definitionEntries, List.map_flatMap]
  exact congrArg (List.flatMap · fn.blocks.toList) (funext definitionEntries_ids)

theorem entry_eq_of_nodup_ids {entries : List (ValueId × Option Op)}
    (h : (entries.map Prod.fst).Nodup) {a b : ValueId × Option Op}
    (ha : a ∈ entries) (hb : b ∈ entries) (he : a.1 = b.1) : a = b := by
  induction entries with
  | nil => simp at ha
  | cons entry entries ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · rfl
      · exact False.elim (h.1 (List.mem_map.mpr ⟨b, hb, he.symm⟩))
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact False.elim (h.1 (List.mem_map.mpr ⟨a, ha, he⟩))
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

end Goose.GIR
