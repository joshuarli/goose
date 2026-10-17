import Goose.Lower.Validation.DenseDefinitions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem definition_scan {ids : List ValueId} (distinct : ids.Nodup)
    {seen : Array Bool} {count : Nat} (size : seen.size = count)
    (unseen : ∀ value ∈ ids, seen[value]? = some false) :
    ∃ after, (forIn ids seen fun value seen => do
      unless value < count do throw s!"value %{value} is outside the value table of {count}"
      if seen[value]! then throw s!"value %{value} is defined twice"
      pure (ForInStep.yield (seen.set! value true))) =
        (Except.ok after : Except String (Array Bool)) ∧
      after.size = count ∧
      ∀ value, value ∉ ids → after[value]? = seen[value]? := by
  induction ids generalizing seen with
  | nil => exact ⟨seen, rfl, size, fun _ _ => rfl⟩
  | cons value rest ih =>
    have row := unseen value (by simp)
    have bound : value < count := by
      rw [← size]
      exact (Array.getElem?_eq_some_iff.mp row).1
    have untouched : ∀ next ∈ rest, (seen.set! value true)[next]? = some false := by
      intro next member
      have different : value ≠ next := by
        intro equal
        subst next
        exact (List.nodup_cons.mp distinct).1 member
      simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using
        unseen next (by simp [member])
    obtain ⟨after, scan, afterSize, preserved⟩ := ih (List.nodup_cons.mp distinct).2
      (seen := seen.set! value true) (by simpa using size) untouched
    refine ⟨after, ?_, afterSize, ?_⟩
    · rw [List.forIn_cons]
      have flag : seen[value]! = false := by
        simp [Array.getElem!_eq_getD, row]
      simp only [bound, ite_true, flag, Bool.false_eq_true, ite_false,
        pure, Except.pure, bind, Except.bind]
      exact scan
    · intro next absent
      have different : value ≠ next := by intro equal; subst next; exact absent (by simp)
      rw [preserved next (by intro member; exact absent (by simp [member]))]
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]

theorem Func.definition_scan_of_dense {func : Func}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues)) :
    ∃ after, (forIn (func.blocks.toList.flatMap GIR.Block.defs)
      (Array.replicate func.numValues false) fun value seen => do
        unless value < func.numValues do
          throw s!"value %{value} is outside the value table of {func.numValues}"
        if seen[value]! then throw s!"value %{value} is defined twice"
        pure (ForInStep.yield (seen.set! value true))) =
          (Except.ok after : Except String (Array Bool)) := by
  have distinct := dense.nodup_iff.mpr List.nodup_range
  have unseen : ∀ value ∈ func.blocks.toList.flatMap GIR.Block.defs,
      (Array.replicate func.numValues false)[value]? = some false := by
    intro value member
    have bound := List.mem_range.mp (dense.mem_iff.mp member)
    simp [bound]
  obtain ⟨after, checked, _, _⟩ := definition_scan distinct (count := func.numValues) (by simp) unseen
  exact ⟨after, checked⟩

theorem lowerImpl_definition_scan (module : Core.Module) (impl : Core.Impl) :
    ∃ after, (forIn ((lowerImpl module impl).blocks.toList.flatMap GIR.Block.defs)
      (Array.replicate (lowerImpl module impl).numValues false) fun value seen => do
        unless value < (lowerImpl module impl).numValues do
          throw s!"value %{value} is outside the value table of {(lowerImpl module impl).numValues}"
        if seen[value]! then throw s!"value %{value} is defined twice"
        pure (ForInStep.yield (seen.set! value true))) =
          (Except.ok after : Except String (Array Bool)) :=
  Func.definition_scan_of_dense (lowerImpl_dense_definitions module impl)

theorem block_definition_scan {blocks : List GIR.Block}
    (distinct : (blocks.flatMap GIR.Block.defs).Nodup)
    {seen : Array Bool} {count : Nat} (size : seen.size = count)
    (unseen : ∀ value ∈ blocks.flatMap GIR.Block.defs, seen[value]? = some false)
    {check : GIR.Block → Except String Unit}
    (checked : ∀ block ∈ blocks, check block = .ok ()) :
    ∃ after, (forIn blocks seen fun block seen => do
      let seen ← forIn block.defs seen fun value seen => do
        unless value < count do throw s!"value %{value} is outside the value table of {count}"
        if seen[value]! then throw s!"value %{value} is defined twice"
        pure (ForInStep.yield (seen.set! value true))
      check block
      pure (ForInStep.yield seen)) = (Except.ok after : Except String (Array Bool)) ∧
      after.size = count ∧
      ∀ value, value ∉ blocks.flatMap GIR.Block.defs → after[value]? = seen[value]? := by
  induction blocks generalizing seen with
  | nil => exact ⟨seen, rfl, size, fun _ _ => rfl⟩
  | cons block rest ih =>
    have distinctParts := List.nodup_append.mp distinct
    obtain ⟨middle, first, middleSize, firstPreserved⟩ :=
      definition_scan distinctParts.1 size (fun value member => unseen value (by simp [member]))
    have remaining : ∀ value ∈ rest.flatMap GIR.Block.defs, middle[value]? = some false := by
      intro value member
      have absent : value ∉ block.defs := by
        intro previous
        exact distinctParts.2.2 value previous value member rfl
      rw [firstPreserved value absent]
      exact unseen value (by simp [member])
    obtain ⟨after, tail, afterSize, tailPreserved⟩ := ih distinctParts.2.1 middleSize remaining
      (fun next member => checked next (by simp [member]))
    refine ⟨after, ?_, afterSize, ?_⟩
    · rw [List.forIn_cons]
      rw [first]
      simp only [bind, Except.bind]
      rw [checked block (by simp)]
      simp only [pure, Except.pure]
      exact tail
    · intro value absent
      rw [tailPreserved value (by intro member; exact absent (by simp [member]))]
      exact firstPreserved value (by intro member; exact absent (by simp [member]))

private theorem forIn_checks {items : List α} {check : α → Except String Unit}
    (checked : ∀ item ∈ items, check item = .ok ()) :
    forIn items PUnit.unit (fun item _ => do
      check item
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, checked item (by simp)]
    simp only [bind, Except.bind]
    exact ih (fun next member => checked next (by simp [member]))

theorem Func.symbol_definition_scan_of_dense {module : GIR.Module} {func : Func}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (instructions : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      checkInstSymbols module func func.numValues inst = .ok ()) :
    ∃ after, (forIn func.blocks (Array.replicate func.numValues false) fun block seen => do
      let seen ← forIn block.defs seen fun value seen => do
        unless value < func.numValues do
          throw s!"value %{value} is outside the value table of {func.numValues}"
        if seen[value]! then throw s!"value %{value} is defined twice"
        pure (ForInStep.yield (seen.set! value true))
      for inst in block.insts do checkInstSymbols module func func.numValues inst
      pure (ForInStep.yield seen)) = (Except.ok after : Except String (Array Bool)) := by
  have unseen : ∀ value ∈ func.blocks.toList.flatMap GIR.Block.defs,
      (Array.replicate func.numValues false)[value]? = some false := by
    intro value member
    have bound := List.mem_range.mp (dense.mem_iff.mp member)
    simp [bound]
  have checked : ∀ block ∈ func.blocks.toList,
      (do for inst in block.insts do checkInstSymbols module func func.numValues inst) =
        (Except.ok () : Except String Unit) := by
    intro block member
    have all := forIn_checks (instructions block member)
    change (_ >>= fun _ => pure ()) = (Except.ok () : Except String Unit)
    rw [all]
    rfl
  obtain ⟨after, scan, _, _⟩ := block_definition_scan (count := func.numValues)
    (dense.nodup_iff.mpr List.nodup_range) (by simp) unseen checked
  refine ⟨after, ?_⟩
  rw [← Array.forIn_toList]
  simpa only [bind_assoc, pure_bind] using scan

private theorem forIn_yields {items : List α}
    {body : α → Except String (ForInStep PUnit.{1})}
    (checked : ∀ item ∈ items, body item = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit (fun item _ => body item) = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, checked item (by simp)]
    simp only [bind, Except.bind]
    exact ih (fun next member => checked next (by simp [member]))

theorem checkInstSymbols_of_within {module : GIR.Module} {func : Func} {env : LEnv}
    {count : Nat} {inst : Inst}
    (within : Inst.SymbolsWithin env func.scopes.size count func.blocks.size inst)
    (origins : env.mod.origins.size = module.origins.size)
    (slots : env.slots.size = func.slots.size)
    (globals : env.globals.size = module.globals.size)
    (functions : env.sigs.size = module.funcs.size) :
    checkInstSymbols module func count inst = .ok () := by
  have uses : (forIn inst.uses PUnit.unit fun value _ =>
      if value < count then pure (.yield PUnit.unit)
      else do
        throw s!"value %{value} is outside the value table of {count}"
        pure (.yield PUnit.unit)) = (Except.ok PUnit.unit : Except String PUnit) :=
    forIn_yields (by intro value member; simp [within.uses value member, pure, Except.pure])
  have originBound : ∀ value, inst.origin = some value → value < module.origins.size := by
    intro value present
    rw [← origins]
    exact within.origin value present
  obtain ⟨_, _, slotBounds, globalBounds, functionBounds, scopeBounds, targetBounds⟩ := within
  rw [slots] at slotBounds
  rw [globals] at globalBounds
  rw [functions] at functionBounds
  unfold checkInstSymbols
  rw [uses]
  simp only [bind, Except.bind]
  cases present : inst.origin
  all_goals try simp only [originBound _ present, ite_true]
  all_goals
    cases inst with
    | «def» value op =>
      cases op <;> simp_all [instSlotRefs, instGlobalRefs, instFunctionRefs,
        pure, Except.pure]
    | eff effect =>
      cases effect <;> simp_all [instSlotRefs, instScopeRefs, pure, Except.pure]
    | term term =>
      simp only []
      have all : (forIn term.successors PUnit.unit fun target _ =>
          if target < func.blocks.size then pure (.yield PUnit.unit)
          else do
            throw s!"block {target} is outside the block table"
            pure (.yield PUnit.unit)) = (Except.ok PUnit.unit : Except String PUnit) :=
        forIn_yields (by intro target member; simp [targetBounds target member, pure, Except.pure])
      simp only [bind, Except.bind] at all
      rw [all]
      rfl

end Goose.Lower.Validation
