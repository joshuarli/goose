import Goose.Lower.Validation.ValueTypeReconstruction

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem value_lookup_congr {left right : TyEnv} {v : ValueId}
    (same : left.vals[v]? = right.vals[v]?) : left.valTy v = right.valTy v := by
  simp only [TyEnv.valTy, same]

private theorem data_lookup_congr {left right : TyEnv} {v : ValueId}
    (same : left.vals[v]? = right.vals[v]?) : left.dataTy v = right.dataTy v := by
  simp only [TyEnv.dataTy, value_lookup_congr same]

private theorem int_lookup_congr {left right : TyEnv} {v : ValueId}
    (same : left.vals[v]? = right.vals[v]?) : left.intTy v = right.intTy v := by
  simp only [TyEnv.intTy, data_lookup_congr same]

private theorem ref_lookup_congr {left right : TyEnv} {v : ValueId}
    (same : left.vals[v]? = right.vals[v]?) : left.refTy v = right.refTy v := by
  simp only [TyEnv.refTy, data_lookup_congr same]

private theorem view_lookup_congr {left right : TyEnv} {v : ValueId}
    (same : left.vals[v]? = right.vals[v]?) : left.viewTy v = right.viewTy v := by
  simp only [TyEnv.viewTy, value_lookup_congr same]

private theorem bound_lookup_congr {left right : TyEnv} {bound : Bnd}
    (same : ∀ v ∈ bound.uses, left.vals[v]? = right.vals[v]?) :
    left.boundTy bound = right.boundTy bound := by
  cases bound <;> simp only [TyEnv.boundTy]
  all_goals rw [int_lookup_congr (same _ (by simp [Bnd.uses]))]

private theorem forIn_body_congr {α β : Type} (items : List α)
    {left right : α → β → TyR (ForInStep β)}
    (same : ∀ a ∈ items, ∀ b, left a b = right a b) (initial : β) :
    forIn items initial left = forIn items initial right := by
  induction items generalizing initial with
  | nil => rfl
  | cons a items ih =>
    simp only [List.forIn_cons, same a (by simp)]
    congr 1
    funext step
    cases step with
    | done b => rfl
    | yield b => exact ih (fun a member => same a (by simp [member])) b

theorem resultTy_operand_congr (op : Op) {left right : TyEnv}
    (slots : left.slots = right.slots) (globals : left.globals = right.globals)
    (sigs : left.sigs = right.sigs) (structs : left.structs = right.structs)
    (profile : left.profile = right.profile)
    (same : ∀ v ∈ op.uses, left.vals[v]? = right.vals[v]?)
    (contents : ∀ mode owner, op = .snapshot mode owner →
      left.contentsWritable owner = right.contentsWritable owner) :
    op.resultTy left = op.resultTy right := by
  have ints : ∀ v ∈ op.uses, left.intTy v = right.intTy v :=
    fun v member => int_lookup_congr (same v member)
  have data : ∀ v ∈ op.uses, left.dataTy v = right.dataTy v :=
    fun v member => data_lookup_congr (same v member)
  have refs : ∀ v ∈ op.uses, left.refTy v = right.refTy v :=
    fun v member => ref_lookup_congr (same v member)
  have views : ∀ v ∈ op.uses, left.viewTy v = right.viewTy v :=
    fun v member => view_lookup_congr (same v member)
  cases op <;> simp only [Op.resultTy]
  all_goals simp only [Op.uses, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at ints data refs views same
  all_goals try simp only [slots, globals, sigs, structs, profile]
  case ownerBorrow owner =>
    rw [ref_lookup_congr same]
  all_goals try simp only [ints, data, refs, views]
  case snapshot mode owner => rw [contents mode owner rfl]
  case viewSlice mu v lo hi org =>
    rw [bound_lookup_congr (bound := lo) (fun w member => same.2 w (by simp [member])),
      bound_lookup_congr (bound := hi) (fun w member => same.2 w (by simp [member]))]
  case call f args org =>
    have loop : ∀ ps : List Ty,
        (forIn (ps.zip args) PUnit.unit fun (pair : Ty × ValueId) _ => do
          unless (← left.dataTy pair.2).passableTo pair.1 do
            tyErr s!"argument %{pair.2} is not accepted by its parameter"
          pure (.yield PUnit.unit)) =
        (forIn (ps.zip args) PUnit.unit fun (pair : Ty × ValueId) _ => do
          unless (← right.dataTy pair.2).passableTo pair.1 do
            tyErr s!"argument %{pair.2} is not accepted by its parameter"
          pure (.yield PUnit.unit)) := by
      intro ps
      apply forIn_body_congr
      intro pair member initial
      rw [data pair.2 (List.of_mem_zip member).2]
    simp only [loop]
  case arrLit t values =>
    have loop : ∀ elem : Ty,
        (forIn values PUnit.unit fun v _ => do
          unless (← left.dataTy v) = elem do
            tyErr "array element of another type than the array's"
          pure (.yield PUnit.unit)) =
        (forIn values PUnit.unit fun v _ => do
          unless (← right.dataTy v) = elem do
            tyErr "array element of another type than the array's"
          pure (.yield PUnit.unit)) := by
      intro elem
      apply forIn_body_congr
      intro v member initial
      rw [data v member]
    simp only [loop]
  case structLit t values =>
    have loop : ∀ fields : List StructField,
        (forIn (values.zip fields) PUnit.unit fun (pair : ValueId × StructField) _ => do
          unless (← left.dataTy pair.1) == pair.2.ty do
            tyErr "struct initializer has another field type"
          pure (.yield PUnit.unit)) =
        (forIn (values.zip fields) PUnit.unit fun (pair : ValueId × StructField) _ => do
          unless (← right.dataTy pair.1) == pair.2.ty do
            tyErr "struct initializer has another field type"
          pure (.yield PUnit.unit)) := by
      intro fields
      apply forIn_body_congr
      intro pair member initial
      rw [data pair.1 (List.of_mem_zip member).1]
    simp only [loop]

def ReconstructionReady (m : GIR.Module) (f : Func) (types : ValueId → VTy)
    (rank : ValueId → Nat) (value : ValueId) (op : Op) : Prop :=
  ∀ roundStart vals, roundStart.size = f.numValues → vals.size = f.numValues →
    ReconstructionRankPrefix f rank types roundStart (rank value) →
    ReconstructionRankPrefix f rank types vals (rank value) →
    op.resultTy (reconstructionEnv m f roundStart vals) = .ok (types value)

theorem reconstructionReady_of_emission
    {m : GIR.Module} {f : Func} {types : ValueId → VTy} {rank : ValueId → Nat}
    {value : ValueId} {op : Op} {emitted : TyEnv}
    (slots : f.slots = emitted.slots)
    (globals : (m.globals.map fun g => (g.ty, g.kind)) = emitted.globals)
    (sigs : (m.funcs.map fun h => (h.params, h.results)) = emitted.sigs)
    (structs : m.structs = emitted.structs) (profile : m.profile = emitted.profile)
    (typed : op.resultTy emitted = .ok (types value))
    (operands : ∀ operand ∈ op.uses,
      operand < f.numValues ∧ rank operand < rank value ∧
      emitted.vals[operand]? = some (some (types operand)))
    (contents : ∀ roundStart, roundStart.size = f.numValues →
      ReconstructionRankPrefix f rank types roundStart (rank value) →
      ∀ mode owner, op = .snapshot mode owner →
        (f.permissions m roundStart)[owner]?.map (·.2) = emitted.contentsWritable owner) :
    ReconstructionReady m f types rank value op := by
  intro roundStart vals roundSize size roundFront front
  rw [resultTy_operand_congr op slots globals sigs structs profile]
  · exact typed
  · intro operand member
    obtain ⟨bound, earlier, recorded⟩ := operands operand member
    exact (front operand bound earlier).trans recorded.symm
  · exact contents roundStart roundSize roundFront

theorem reconstructionReady_constBool
    {m : GIR.Module} {f : Func} {types : ValueId → VTy} {rank : ValueId → Nat}
    {value : ValueId} (literal : Bool) (expected : types value = .data .bool) :
    ReconstructionReady m f types rank value (.constBool literal) := by
  intro roundStart vals roundSize size roundFront front
  simp only [Op.resultTy, expected]
  rfl

theorem reconstructionReady_constUnit
    {m : GIR.Module} {f : Func} {types : ValueId → VTy} {rank : ValueId → Nat}
    {value : ValueId} (expected : types value = .data .unit) :
    ReconstructionReady m f types rank value .constUnit := by
  intro roundStart vals roundSize size roundFront front
  simp only [Op.resultTy, expected]
  rfl

theorem reconstructionReady_constInt
    {m : GIR.Module} {f : Func} {types : ValueId → VTy} {rank : ValueId → Nat}
    {value : ValueId} (intTy : IntTy) (number : Int) (range : intTy.inRange number)
    (expected : types value = .data (.int intTy)) :
    ReconstructionReady m f types rank value (.constInt intTy number) := by
  intro roundStart vals roundSize size roundFront front
  simp only [Op.resultTy, range, ite_true, expected]
  rfl

end Goose.Lower.Validation
