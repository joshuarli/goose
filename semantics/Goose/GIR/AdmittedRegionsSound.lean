import Goose.GIR.AdmittedRegions

namespace Goose.GIR

open Goose.Core

private theorem except_bind_ok {α β : Type} {action : Except String α}
    {next : α → Except String β} {result : β}
    (checked : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => simp [bind, Except.bind] at checked
  | ok value => exact ⟨value,rfl,checked⟩

private theorem checked_list_members {α β : Type} {items : List α}
    {body : α → β → Except String (ForInStep β)} {property : α → Prop}
    (yielded : ∀ item state step, body item state = .ok step → ∃ next, step = .yield next)
    (checkedItem : ∀ item state step, body item state = .ok step → property item)
    {initial final : β} (checked : forIn items initial body = .ok final) :
    ∀ item ∈ items, property item := by
  induction items generalizing initial final with
  | nil => simp
  | cons item rest inductionHypothesis =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, first, remaining⟩ := except_bind_ok checked
    obtain ⟨next,rfl⟩ := yielded item initial step first
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact checkedItem selected initial _ first
    · exact inductionHypothesis remaining selected member

theorem Func.checkRegionClosure_admitted {m : Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {f : Func} {p : Prov} {returned : Option (List RootRef)}
    (checked : f.checkRegionClosure m results vt p returned = .ok ()) :
    f.checkAdmittedRegions m vt p = .ok () := by
  cases stable : (provRound results vt f p).2 <;>
    cases returned with
    | none => simp_all [Func.checkRegionClosure, bind, Except.bind, throw]
    | some roots =>
      cases bounded : (f.returnedRoots p).all roots.contains <;>
        simp_all [Func.checkRegionClosure, bind, Except.bind, throw]

theorem Func.checkRegionClosure_stable {m : Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {f : Func} {p : Prov} {returned : Option (List RootRef)}
    (checked : f.checkRegionClosure m results vt p returned = .ok ()) :
    (provRound results vt f p).2 = false := by
  cases stable : (provRound results vt f p).2 <;>
    simp_all [Func.checkRegionClosure, bind, Except.bind, throw]

theorem Func.checkRegionClosure_result {m : Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {f : Func} {p : Prov} {roots : List RootRef}
    (checked : f.checkRegionClosure m results vt p (some roots) = .ok ()) :
    ∀ root ∈ f.returnedRoots p, root ∈ roots := by
  have bounded : (f.returnedRoots p).all roots.contains = true := by
    cases stable : (provRound results vt f p).2 <;>
      cases bounded : (f.returnedRoots p).all roots.contains <;>
      simp_all [Func.checkRegionClosure, bind, Except.bind, throw]
  simpa only [List.contains_iff_mem] using List.all_eq_true.mp bounded

theorem Module.checkAdmittedRegions_globalTypes {m : Module}
    {types : Array (Array (Option VTy))} {results : Array (List RootRef)} {nRoots : Nat}
    (checked : m.checkAdmittedRegions types results nRoots = .ok ()) :
    m.checkRegionGlobalTypes = .ok () := by
  unfold Module.checkAdmittedRegions at checked
  obtain ⟨checkedUnit, first, _⟩ := except_bind_ok checked
  cases checkedUnit
  exact first

theorem Module.checkAdmittedRegions_function_closure {m : Module}
    {types : Array (Array (Option VTy))} {results : Array (List RootRef)} {nRoots : Nat}
    (checked : m.checkAdmittedRegions types results nRoots = .ok ())
    {index : Nat} {f : Func} (atIndex : m.funcs[index]? = some f) :
    f.checkRegionClosure m results (types[index]?.getD #[])
      (f.provenance results (types[index]?.getD #[]) nRoots) (some (rootsAt results index)) = .ok () := by
  unfold Module.checkAdmittedRegions at checked
  obtain ⟨_, _, remaining⟩ := except_bind_ok checked
  obtain ⟨_, functions, _⟩ := except_bind_ok remaining
  have member : (f,index) ∈ m.funcs.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using atIndex)
  refine checked_list_members (property := fun pair : Func × Nat =>
    pair.1.checkRegionClosure m results (types[pair.2]?.getD #[])
      (pair.1.provenance results (types[pair.2]?.getD #[]) nRoots) (some (rootsAt results pair.2)) = .ok ()) ?_ ?_ functions
    (f,index) member
  · intro pair state step one
    obtain ⟨_, _, done⟩ := except_bind_ok one
    exact ⟨_, by simpa [pure, Except.pure] using done.symm⟩
  · intro pair state step one
    obtain ⟨checkedUnit, first, _⟩ := except_bind_ok one
    cases checkedUnit
    exact first

theorem Module.checkAdmittedRegions_initializer_closure {m : Module}
    {types : Array (Array (Option VTy))} {results : Array (List RootRef)} {nRoots : Nat}
    (checked : m.checkAdmittedRegions types results nRoots = .ok ())
    {global : Global} (member : global ∈ m.globals.toList) :
    global.init.checkRegionClosure m results (global.init.valueTypes m)
      (global.init.provenance results (global.init.valueTypes m) nRoots) none = .ok () := by
  unfold Module.checkAdmittedRegions at checked
  obtain ⟨_, _, remaining⟩ := except_bind_ok checked
  obtain ⟨_, _, remaining⟩ := except_bind_ok remaining
  obtain ⟨_, initializers, _⟩ := except_bind_ok remaining
  rw [← Array.forIn_toList] at initializers
  refine checked_list_members (property := fun global : Global =>
    global.init.checkRegionClosure m results (global.init.valueTypes m)
      (global.init.provenance results (global.init.valueTypes m) nRoots) none = .ok ()) ?_ ?_ initializers
    global member
  · intro selected state step one
    obtain ⟨_, _, done⟩ := except_bind_ok one
    exact ⟨_, by simpa [pure, Except.pure] using done.symm⟩
  · intro selected state step one
    obtain ⟨checkedUnit, first, _⟩ := except_bind_ok one
    cases checkedUnit
    exact first

theorem Module.checkAdmittedRegions_function {m : Module}
    {types : Array (Array (Option VTy))} {results : Array (List RootRef)} {nRoots : Nat}
    (checked : m.checkAdmittedRegions types results nRoots = .ok ())
    {index : Nat} {f : Func} (atIndex : m.funcs[index]? = some f) :
    f.checkAdmittedRegions m (types[index]?.getD #[])
      (f.provenance results (types[index]?.getD #[]) nRoots) = .ok () :=
  Func.checkRegionClosure_admitted (m.checkAdmittedRegions_function_closure checked atIndex)

theorem Module.checkAdmittedRegions_initializer {m : Module}
    {types : Array (Array (Option VTy))} {results : Array (List RootRef)} {nRoots : Nat}
    (checked : m.checkAdmittedRegions types results nRoots = .ok ())
    {global : Global} (member : global ∈ m.globals.toList) :
    global.init.checkAdmittedRegions m (global.init.valueTypes m)
      (global.init.provenance results (global.init.valueTypes m) nRoots) = .ok () :=
  Func.checkRegionClosure_admitted (m.checkAdmittedRegions_initializer_closure checked member)

theorem Func.checkAdmittedRegions_return {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ())
    {block : Block} (blockMember : block ∈ f.blocks.toList)
    {values : List ValueId} {org : Option OriginId}
    (returned : Inst.term (.ret values org) ∈ block.insts)
    {value index : Nat} (operand : (value,index) ∈ values.zipIdx)
    (reference : valRefLike vt value = true) :
    ∀ root ∈ rootsAt p.vals value, root ∈ f.roots.results[index]?.getD [] := by
  have instruction := f.checkAdmittedRegions_instruction checked blockMember returned
  change values.zipIdx.all _ = true at instruction
  have bound := List.all_eq_true.mp instruction (value,index) operand
  simp only [reference, Bool.not_true, Bool.false_or] at bound
  simpa only [List.contains_iff_mem] using List.all_eq_true.mp bound

theorem Func.checkAdmittedRegions_call {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ())
    {block : Block} (blockMember : block ∈ f.blocks.toList)
    {value fn : Nat} {args : List ValueId} {org : Option OriginId}
    (called : Inst.def value (.call fn args org) ∈ block.insts)
    {callee : Func} (calleeAt : m.funcs[fn]? = some callee)
    {parameter : Nat} {ceiling : List RootRef} (row : (parameter,ceiling) ∈ callee.roots.contents.toList)
    (reference : (callee.params[parameter]?).any Ty.isRefSlice = true) :
    (∀ root ∈ argumentContents f p args[parameter]!, root ∈ mapContentRoots f p args ceiling) ∧
    (∀ root ∈ mapContentRoots f p args ceiling, root ∈ argumentContents f p args[parameter]!) := by
  have instruction := f.checkAdmittedRegions_instruction checked blockMember called
  simp only [Func.admittedInstruction, calleeAt] at instruction
  have bound := List.all_eq_true.mp instruction (parameter,ceiling) row
  simp only [reference, Bool.not_true, Bool.false_or, Bool.and_eq_true] at bound
  constructor
  · simpa only [List.contains_iff_mem] using List.all_eq_true.mp bound.1.1
  · simpa only [List.contains_iff_mem] using List.all_eq_true.mp bound.1.2

theorem Func.checkAdmittedRegions_call_receiver {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ())
    {block : Block} (blockMember : block ∈ f.blocks.toList)
    {value fn : Nat} {args : List ValueId} {org : Option OriginId}
    (called : Inst.def value (.call fn args org) ∈ block.insts)
    {callee : Func} (calleeAt : m.funcs[fn]? = some callee)
    {parameter : Nat} {ceiling : List RootRef} (row : (parameter,ceiling) ∈ callee.roots.contents.toList)
    (reference : (callee.params[parameter]?).any Ty.isRefSlice = true)
    {receiver : RootRef} (receiverMember : receiver ∈ rootsAt p.vals args[parameter]!) :
    RootsRefine f (mapRawContentRoots p args ceiling) (f.receiverContentCeiling p receiver) := by
  have instruction := f.checkAdmittedRegions_instruction checked blockMember called
  simp only [Func.admittedInstruction, calleeAt] at instruction
  have bound := List.all_eq_true.mp instruction (parameter,ceiling) row
  simp only [reference, Bool.not_true, Bool.false_or, Bool.and_eq_true] at bound
  have receiverBound := List.all_eq_true.mp bound.2 receiver receiverMember
  exact (Func.rootsWithin_eq_true f _ _).mp receiverBound

theorem Func.checkAdmittedRegions_store {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ())
    {block : Block} (blockMember : block ∈ f.blocks.toList)
    {address value : Nat} {org : Option OriginId}
    (stored : Inst.eff (.store address value org) ∈ block.insts)
    (reference : valRefLike vt value = true) {parameter : Nat}
    (target : RootRef.param parameter ∈ rootsAt p.vals address)
    (sliceReference : (f.params[parameter]?).any Ty.isRefSlice = true) :
    ∃ ceiling, f.roots.contents.find? (·.1 == parameter) = some (parameter,ceiling) ∧
      RootsRefine f (rootsAt p.vals value) ceiling := by
  have instruction := f.checkAdmittedRegions_instruction checked blockMember stored
  simp only [Func.admittedInstruction, reference, Bool.not_true, Bool.false_or] at instruction
  have bound := List.all_eq_true.mp instruction (.param parameter) target
  simp only [sliceReference, Bool.not_true, Bool.false_or] at bound
  cases found : f.roots.contents.find? (·.1 == parameter) with
  | none => simp [found] at bound
  | some row =>
    simp only [found, Option.any_some] at bound
    have identity := Array.find?_some found
    have same : row.1 = parameter := by simpa only [beq_iff_eq] using identity
    rcases row with ⟨selected, ceiling⟩
    change selected = parameter at same
    subst selected
    refine ⟨ceiling, rfl, ?_⟩
    exact (Func.rootsWithin_eq_true f _ _).mp bound

end Goose.GIR
