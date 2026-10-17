import Goose.Lower.Validation.ReplacementProvenance
import Goose.Lower.Validation.DenseDefinitions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem list_foldl_establishes_member {property known : σ → Prop} (items : List α) (start : σ)
    (step : σ → α → σ) (target : α) (member : target ∈ items) (initial : property start)
    (preserved : ∀ state item, item ∈ items → property state → property (step state item))
    (retained : ∀ state item, item ∈ items → property state → known state → known (step state item))
    (established : ∀ state, property state → known (step state target)) :
    known (items.foldl step start) := by
  induction items generalizing start with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with same | later
    · subst first
      have both : property (rest.foldl step (step start target)) ∧
          known (rest.foldl step (step start target)) := by
        apply List.foldlRecOn (motive := fun state => property state ∧ known state) rest step
          ⟨preserved start target (by simp) initial, established start initial⟩
        intro state checked item member
        exact ⟨preserved state item (by simp [member]) checked.1,
          retained state item (by simp [member]) checked.1 checked.2⟩
      exact both.2
    · apply ih (step start first) later (preserved start first (by simp) initial)
      · intro state item member checked
        exact preserved state item (by simp [member]) checked
      · intro state item member checked known
        exact retained state item (by simp [member]) checked known

theorem parameter_position_unique {params : List (ValueId × VTy)}
    (distinct : (params.map Prod.fst).Nodup) {position other : Nat} {value : ValueId} {ty otherTy : VTy}
    (first : params[position]? = some (value, ty)) (second : params[other]? = some (value, otherTy)) :
    position = other := by
  have left : (params.map Prod.fst)[position]? = some value := by simp [first]
  have right : (params.map Prod.fst)[other]? = some value := by simp [second]
  exact (distinct.getElem?_inj (by simpa using (List.getElem?_eq_some_iff.mp first).1)).mp
    (left.trans right.symm)

theorem provStart_ref_parameter (func : Func) (types : Array (Option VTy))
    {entry : GIR.Block} (entryAt : func.blocks[0]? = some entry)
    (distinct : (entry.params.map Prod.fst).Nodup)
    {position : Nat} {value : ValueId} {ty : VTy}
    (parameterAt : entry.params[position]? = some (value, ty))
    (reference : valRefLike types value = true) (bounded : value < func.numValues) :
    RootRef.param position ∈ rootsAt (provStart types func).vals value := by
  unfold provStart
  simp only [entryAt]
  refine list_foldl_establishes_member
    (property := fun roots : Array (List RootRef) => roots.size = func.numValues)
    (known := fun roots => RootRef.param position ∈ rootsAt roots value)
    _ _ _ ((value, ty), position) (List.mk_mem_zipIdx_iff_getElem?.mpr parameterAt) (by simp) ?_ ?_ ?_
  · intro roots pair member size
    try dsimp only
    split <;> simpa using size
  · intro roots pair member size known
    obtain ⟨⟨other, otherTy⟩, otherPosition⟩ := pair
    dsimp only
    split
    · by_cases same : other = value
      · subst other
        have pairAt := List.mk_mem_zipIdx_iff_getElem?.mp member
        have equal : otherPosition = position := parameter_position_unique distinct pairAt parameterAt
        simp [equal, rootsAt, size, bounded]
      · simpa [rootsAt, Array.getElem?_setIfInBounds, same] using known
    · exact known
  · intro roots size
    simp [reference, size, bounded, rootsAt]

theorem provenance_ref_parameter (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (rootCount : Nat) {entry : GIR.Block} (entryAt : func.blocks[0]? = some entry)
    (distinct : (entry.params.map Prod.fst).Nodup)
    {position : Nat} {value : ValueId} {ty : VTy}
    (parameterAt : entry.params[position]? = some (value, ty))
    (reference : valRefLike types value = true) (bounded : value < func.numValues) :
    RootRef.param position ∈ rootsAt (func.provenance results types rootCount).vals value :=
  (provFix_extends results types func _ _).2.2.2 value (.param position)
    (provStart_ref_parameter func types entryAt distinct parameterAt reference bounded)

theorem replacementQueries_ref_parameter (module : GIR.Module) (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (rootCount : Nat) {entry : GIR.Block} (entryAt : func.blocks[0]? = some entry)
    (distinct : (entry.params.map Prod.fst).Nodup)
    {position : Nat} {value : ValueId} {ty : VTy}
    (parameterAt : entry.params[position]? = some (value, ty))
    (reference : valRefLike types value = true) (bounded : value < func.numValues)
    {root : RootRef} (declared : root ∈ func.parameterRoots position) :
    root ∈ ((replacementQueries module func types (func.provenance results types rootCount)).value value).getD [] := by
  rw [replacementQueries_values]
  exact List.mem_flatMap.mpr ⟨.param position,
    provenance_ref_parameter results types func rootCount entryAt distinct parameterAt reference bounded,
    declared⟩

theorem provenance_ref_parameter_of_dense (results : Array (List RootRef))
    (types : Array (Option VTy)) (func : Func) (rootCount : Nat)
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    {entry : GIR.Block} (entryAt : func.blocks[0]? = some entry)
    {position : Nat} {value : ValueId} {ty : VTy}
    (parameterAt : entry.params[position]? = some (value, ty))
    (reference : valRefLike types value = true) :
    RootRef.param position ∈ rootsAt (func.provenance results types rootCount).vals value := by
  have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? entryAt)
  exact provenance_ref_parameter results types func rootCount entryAt
    (Func.parameter_ids_distinct_of_dense dense member) parameterAt reference
    (Func.parameter_ids_bounded_of_dense dense entry member (value, ty)
      (List.mem_of_getElem? parameterAt))

end Goose.Lower.Validation
