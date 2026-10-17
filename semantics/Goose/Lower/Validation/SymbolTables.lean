import Goose.Lower.Validation.SymbolDefinitions
import Goose.Lower.Validation.TableBounds
import Init.Data.Range.Lemmas

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def RootRef.ExternalWithin (module : GIR.Module) (func : Func) : RootRef → Prop
  | .local _ => False
  | .global index => index < module.globals.size
  | .param index => index < func.params.length

def RootRef.ParameterWithin (module : GIR.Module) (parameter : Nat) : RootRef → Prop
  | .local _ => False
  | .global index => index < module.globals.size
  | .param index => index = parameter

structure SymbolTableFacts (module : GIR.Module) (func : Func) : Prop where
  blocks : func.blocks.isEmpty = false
  scopes : ∀ (index parent : Nat), func.scopes[index]? = some (some parent) → parent < index
  slots : ∀ slot ∈ func.slots.toList, slot.scope < func.scopes.size
  origin : ∀ index, func.org = some index → index < module.origins.size
  summary : ∀ summary, func.summary = .known summary →
    ∀ target ∈ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds,
      match target with
      | .param index => index < func.params.length
      | .global index => index < module.globals.size
  resultRows : func.roots.results.size = func.results.length
  parameters : ∀ index roots, (index, roots) ∈ func.roots.params.toList →
    index < func.params.length ∧ func.params[index]!.isRefLike = true ∧
      ∀ root ∈ roots, RootRef.ParameterWithin module index root
  contents : ∀ index roots, (index, roots) ∈ func.roots.contents.toList →
    index < func.params.length ∧ func.params[index]!.isRefSlice = true ∧
      ∀ root ∈ roots, RootRef.ExternalWithin module func root
  results : ∀ roots ∈ func.roots.results.toList, ∀ root ∈ roots, RootRef.ExternalWithin module func root

private theorem forIn'_yields {items : List α}
    {body : (item : α) → item ∈ items → Except String (ForInStep PUnit.{1})}
    (checked : ∀ item member, body item member = .ok (.yield PUnit.unit)) :
    forIn' items PUnit.unit (fun item member _ => body item member) = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn'_cons, checked item (by simp)]
    simp only [bind, Except.bind]
    exact ih (fun next member => checked next (by simp [member]))

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

private theorem asCheck_accept {code : Code} {label : String} {action : Except String Unit}
    (checked : action = .ok ()) : asCheck code label action = .ok () := by
  rw [checked]
  rfl

theorem SymbolTableFacts.scope_scan {module : GIR.Module} {func : Func}
    (facts : SymbolTableFacts module func) :
    (do
      for h : index in [0:func.scopes.size] do
        match func.scopes[index] with
        | some parent => unless parent < index do
            throw s!"scope {index}: parent {parent} is not an earlier scope"
        | none => pure ()) = (Except.ok () : Except String Unit) := by
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  have checked : ∀ index (member : index ∈ List.range' 0
      (Std.Legacy.Range.size {start := 0, stop := func.scopes.size, step := 1, step_pos := by decide}) 1),
      (do
        match func.scopes[index]'(Std.Legacy.Range.mem_of_mem_range' (r := {start := 0, stop := func.scopes.size, step := 1, step_pos := by decide}) member).2.1 with
        | some parent => unless parent < index do
            throw s!"scope {index}: parent {parent} is not an earlier scope"
        | none => pure ()
        pure (.yield PUnit.unit)) =
          (Except.ok (.yield PUnit.unit) : Except String (ForInStep PUnit)) := by
    intro index member
    have bound := (Std.Legacy.Range.mem_of_mem_range' (r := {start := 0, stop := func.scopes.size, step := 1, step_pos := by decide}) member).2.1
    have row : func.scopes[index]? = some func.scopes[index] := Array.getElem?_eq_getElem bound
    cases parentRow : func.scopes[index] with
    | none => simp [pure, Except.pure]
    | some parent =>
      have earlier := facts.scopes index parent (by simpa [parentRow] using row)
      simp [earlier, pure, Except.pure]
  have all := forIn'_yields checked
  change (_ >>= fun _ => pure ()) = (Except.ok () : Except String Unit)
  rw [all]
  rfl

theorem SymbolTableFacts.parameter_scan {module : GIR.Module} {func : Func}
    (facts : SymbolTableFacts module func) :
    (do
      for (index, roots) in func.roots.params do
        unless index < func.params.length do
          throw s!"root info names parameter {index}, which does not exist"
        unless func.params[index]!.isRefLike do
          throw s!"root info annotates non-reference parameter {index}"
        for root in roots do
          match root with
          | .local _ => throw s!"root info for parameter {index} names a local slot"
          | .global global => unless global < module.globals.size do
              throw s!"root info names global {global}, outside the global table"
          | .param parameter => unless parameter == index do
              throw s!"root info for parameter {index} names parameter {parameter}") =
        (Except.ok () : Except String Unit) := by
  rw [← Array.forIn_toList]
  have checked : ∀ pair ∈ func.roots.params.toList,
      (do
        unless pair.1 < func.params.length do
          throw s!"root info names parameter {pair.1}, which does not exist"
        unless func.params[pair.1]!.isRefLike do
          throw s!"root info annotates non-reference parameter {pair.1}"
        for root in pair.2 do
          match root with
          | .local _ => throw s!"root info for parameter {pair.1} names a local slot"
          | .global global => unless global < module.globals.size do
              throw s!"root info names global {global}, outside the global table"
          | .param parameter => unless parameter == pair.1 do
              throw s!"root info for parameter {pair.1} names parameter {parameter}"
        pure (.yield PUnit.unit)) =
        (Except.ok (.yield PUnit.unit) : Except String (ForInStep PUnit)) := by
    intro pair member
    obtain ⟨index, roots⟩ := pair
    have info := facts.parameters index roots member
    simp only [info.1, info.2.1, ite_true, pure, Except.pure, bind, Except.bind]
    have checkedRoots : (forIn roots PUnit.unit fun root _ => do
        match root with
        | .local _ => throw s!"root info for parameter {index} names a local slot"
        | .global global => unless global < module.globals.size do
            throw s!"root info names global {global}, outside the global table"
        | .param parameter => unless parameter == index do
            throw s!"root info for parameter {index} names parameter {parameter}"
        pure (.yield PUnit.unit)) =
        (Except.ok PUnit.unit : Except String PUnit) := by
      apply forIn_yields
      intro root rootMember
      have allowed := info.2.2 root rootMember
      cases root <;> simp_all [RootRef.ParameterWithin, pure, Except.pure]
    simp only [pure, Except.pure, bind, Except.bind] at checkedRoots
    rw [checkedRoots]
  have all := forIn_yields checked
  change (_ >>= fun _ => pure ()) = (Except.ok () : Except String Unit)
  rw [all]
  rfl

theorem SymbolTableFacts.content_scan {module : GIR.Module} {func : Func}
    (facts : SymbolTableFacts module func) :
    (do
      for (index, roots) in func.roots.contents do
        unless index < func.params.length do
          throw s!"content root info names parameter {index}, which does not exist"
        unless func.params[index]!.isRefSlice do
          throw s!"content root info annotates a parameter that is not a reference to a slice"
        for root in roots do
          match root with
          | .local _ => throw s!"content root info for parameter {index} names a local slot"
          | .global global => unless global < module.globals.size do
              throw s!"content root info names global {global}, outside the global table"
          | .param parameter => unless parameter < func.params.length do
              throw s!"content root info names parameter {parameter}, which does not exist") =
        (Except.ok () : Except String Unit) := by
  rw [← Array.forIn_toList]
  have checked : ∀ pair ∈ func.roots.contents.toList,
      (do
        unless pair.1 < func.params.length do
          throw s!"content root info names parameter {pair.1}, which does not exist"
        unless func.params[pair.1]!.isRefSlice do
          throw s!"content root info annotates a parameter that is not a reference to a slice"
        for root in pair.2 do
          match root with
          | .local _ => throw s!"content root info for parameter {pair.1} names a local slot"
          | .global global => unless global < module.globals.size do
              throw s!"content root info names global {global}, outside the global table"
          | .param parameter => unless parameter < func.params.length do
              throw s!"content root info names parameter {parameter}, which does not exist"
        pure (.yield PUnit.unit)) =
        (Except.ok (.yield PUnit.unit) : Except String (ForInStep PUnit)) := by
    intro pair member
    obtain ⟨index, roots⟩ := pair
    have info := facts.contents index roots member
    simp only [info.1, info.2.1, ite_true, pure, Except.pure, bind, Except.bind]
    have checkedRoots : (forIn roots PUnit.unit fun root _ => do
        match root with
        | .local _ => throw s!"content root info for parameter {index} names a local slot"
        | .global global => unless global < module.globals.size do
            throw s!"content root info names global {global}, outside the global table"
        | .param parameter => unless parameter < func.params.length do
            throw s!"content root info names parameter {parameter}, which does not exist"
        pure (.yield PUnit.unit)) =
        (Except.ok PUnit.unit : Except String PUnit) := by
      apply forIn_yields
      intro root rootMember
      have allowed := info.2.2 root rootMember
      cases root <;> simp_all [RootRef.ExternalWithin, pure, Except.pure]
    simp only [pure, Except.pure, bind, Except.bind] at checkedRoots
    rw [checkedRoots]
  have all := forIn_yields checked
  change (_ >>= fun _ => pure ()) = (Except.ok () : Except String Unit)
  rw [all]
  rfl

theorem SymbolTableFacts.result_scan {module : GIR.Module} {func : Func}
    (facts : SymbolTableFacts module func) :
    (do
      for roots in func.roots.results do
        for root in roots do
          match root with
          | .local index => throw s!"result root info names local slot {index}"
          | .global global => unless global < module.globals.size do
              throw s!"result root info names global {global}, outside the global table"
          | .param parameter => unless parameter < func.params.length do
              throw s!"result root info names parameter {parameter}, which does not exist") =
        (Except.ok () : Except String Unit) := by
  rw [← Array.forIn_toList]
  have checked : ∀ roots ∈ func.roots.results.toList,
      (do
        for root in roots do
          match root with
          | .local index => throw s!"result root info names local slot {index}"
          | .global global => unless global < module.globals.size do
              throw s!"result root info names global {global}, outside the global table"
          | .param parameter => unless parameter < func.params.length do
              throw s!"result root info names parameter {parameter}, which does not exist"
        pure (.yield PUnit.unit)) =
        (Except.ok (.yield PUnit.unit) : Except String (ForInStep PUnit)) := by
    intro roots member
    have checkedRoots : (forIn roots PUnit.unit fun root _ => do
        match root with
        | .local index => throw s!"result root info names local slot {index}"
        | .global global => unless global < module.globals.size do
            throw s!"result root info names global {global}, outside the global table"
        | .param parameter => unless parameter < func.params.length do
            throw s!"result root info names parameter {parameter}, which does not exist"
        pure (.yield PUnit.unit)) =
        (Except.ok PUnit.unit : Except String PUnit) := by
      apply forIn_yields
      intro root rootMember
      have allowed := facts.results roots member root rootMember
      cases root <;> simp_all [RootRef.ExternalWithin, pure, Except.pure]
    rw [checkedRoots]
    rfl
  have all := forIn_yields checked
  change (_ >>= fun _ => pure ()) = (Except.ok () : Except String Unit)
  rw [all]
  rfl

theorem SymbolTableFacts.slot_scan {module : GIR.Module} {func : Func}
    (facts : SymbolTableFacts module func) :
    (do
      for slot in func.slots do
        unless slot.scope < func.scopes.size do
          throw s!"slot of variable {slot.var}: scope {slot.scope} is outside the scope table") =
        (Except.ok () : Except String Unit) := by
  rw [← Array.forIn_toList]
  have all := forIn_yields (items := func.slots.toList) (body := fun slot => do
    unless slot.scope < func.scopes.size do
      throw s!"slot of variable {slot.var}: scope {slot.scope} is outside the scope table"
    pure (.yield PUnit.unit)) (by intro slot member; simp [facts.slots slot member, pure, Except.pure])
  change (_ >>= fun _ => pure ()) = (Except.ok () : Except String Unit)
  rw [all]
  rfl

theorem SymbolTableFacts.summary_scan {module : GIR.Module} {func : Func}
    (facts : SymbolTableFacts module func) :
    (match func.summary with
    | .unknown => pure ()
    | .known summary => do
      for target in summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds do
        match target with
        | .param index => unless index < func.params.length do
            throw s!"summary names parameter {index}, which does not exist"
        | .global index => unless index < module.globals.size do
            throw s!"summary names global {index}, outside the global table") =
      (Except.ok () : Except String Unit) := by
  cases shape : func.summary with
  | unknown => rfl
  | known summary =>
    have all := forIn_yields
      (items := summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds)
      (body := fun target => do
        match target with
        | .param index => unless index < func.params.length do
            throw s!"summary names parameter {index}, which does not exist"
        | .global index => unless index < module.globals.size do
            throw s!"summary names global {index}, outside the global table"
        pure (.yield PUnit.unit)) (by
          intro target member
          have bound := facts.summary summary shape target member
          cases target <;> simp_all [pure, Except.pure])
    change (_ >>= fun _ => pure ()) = (Except.ok () : Except String Unit)
    rw [all]
    rfl

private theorem accept_bind {action : Except String α} {next : α → Except String β} {value : α} {result : β}
    (first : action = .ok value) (second : next value = .ok result) :
    (action >>= next) = .ok result := by
  rw [first]
  exact second

theorem checkSymbols_of_tables {module : GIR.Module} {func : Func} {env : LEnv}
    (facts : SymbolTableFacts module func)
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (references : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      Inst.SymbolsWithin env func.scopes.size func.numValues func.blocks.size inst)
    (origins : env.mod.origins.size = module.origins.size)
    (slots : env.slots.size = func.slots.size)
    (globals : env.globals.size = module.globals.size)
    (functions : env.sigs.size = module.funcs.size) (label : String) :
    checkSymbols module label func = .ok () := by
  obtain ⟨scopeUnit, scopeRaw, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp facts.scope_scan
  cases scopeUnit
  obtain ⟨slotUnit, slotRaw, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp facts.slot_scan
  cases slotUnit
  obtain ⟨parameterUnit, parameterRaw, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp facts.parameter_scan
  cases parameterUnit
  obtain ⟨contentUnit, contentRaw, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp facts.content_scan
  cases contentUnit
  obtain ⟨resultUnit, resultRaw, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp facts.result_scan
  cases resultUnit
  have instructionChecks : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      checkInstSymbols module func func.numValues inst = .ok () := by
    intro block blockMember inst instMember
    exact checkInstSymbols_of_within (references block blockMember inst instMember)
      origins slots globals functions
  obtain ⟨seen, scanned⟩ := Func.symbol_definition_scan_of_dense dense instructionChecks
  unfold checkSymbols
  apply asCheck_accept
  simp only [facts.blocks, Bool.false_eq_true, ite_false]
  apply accept_bind scopeRaw
  apply accept_bind slotRaw
  cases present : func.org
  all_goals try simp only [facts.origin _ present, ite_true]
  all_goals
    cases summary : func.summary
    all_goals
      try
        have scannedSummary := facts.summary_scan
        rw [summary] at scannedSummary
        obtain ⟨summaryUnit, summaryRaw, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp scannedSummary
        cases summaryUnit
        apply accept_bind summaryRaw
      simp only [facts.resultRows, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false]
      apply accept_bind parameterRaw
      apply accept_bind contentRaw
      apply accept_bind resultRaw
      apply accept_bind scanned
      rfl

end Goose.Lower.Validation
