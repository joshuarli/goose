import Goose.Lower.Validation.ProvenanceConvergenceFixedPoint

namespace Goose.Lower.Validation.ProvenanceConvergence

open Goose.Core Goose.GIR

def finiteRootUniverse (globalCount : Nat) (func : Func) : List RootRef :=
  (List.range func.slots.size).map RootRef.local ++
    (List.range func.params.length).map RootRef.param ++
    (List.range globalCount).map RootRef.global

def ValidRoot (globalCount : Nat) (func : Func) : RootRef → Prop
  | .local slot => slot < func.slots.size
  | .param param => param < func.params.length
  | .global global => global < globalCount

theorem mem_finiteRootUniverse {globalCount : Nat} {func : Func} {root : RootRef} :
    root ∈ finiteRootUniverse globalCount func ↔ ValidRoot globalCount func root := by
  cases root <;> simp [finiteRootUniverse, ValidRoot, List.mem_map]

theorem finiteRootUniverse_length (globalCount : Nat) (func : Func) :
    (finiteRootUniverse globalCount func).length = globalCount + func.params.length + func.slots.size := by
  simp only [finiteRootUniverse, List.length_append, List.length_map, List.length_range]
  omega

structure RootBounds (results : Array (List RootRef)) (func : Func) (globalCount : Nat) : Prop where
  entry : ∀ block, func.blocks[0]? = some block → block.params.length ≤ func.params.length
  slots : ∀ block ∈ func.blocks.toList, ∀ value slot,
    Inst.def value (.slotAddr slot) ∈ block.insts → slot < func.slots.size
  globals : ∀ block ∈ func.blocks.toList, ∀ value global,
    Inst.def value (.globalAddr global) ∈ block.insts → global < globalCount
  contents : ∀ row ∈ func.roots.contents, ∀ root ∈ row.2, ValidRoot globalCount func root
  results : ∀ callee global, RootRef.global global ∈ rootsAt results callee → global < globalCount

theorem RootBounds.finite {results : Array (List RootRef)} {func : Func} {globalCount : Nat}
    (bound : RootBounds results func globalCount) :
    RootUniverse results func (finiteRootUniverse globalCount func) := by
  constructor
  · intro block entry param member
    apply mem_finiteRootUniverse.mpr
    have index := List.mem_zipIdx member
    have length := bound.entry block entry
    change param.2 < func.params.length
    omega
  · intro block blockMember value op member
    cases op <;> try trivial
    case slotAddr slot =>
      apply mem_finiteRootUniverse.mpr
      exact bound.slots block blockMember value slot member
    case globalAddr global =>
      apply mem_finiteRootUniverse.mpr
      exact bound.globals block blockMember value global member
  · intro row rowMember root member
    exact mem_finiteRootUniverse.mpr (bound.contents row rowMember root member)
  · intro callee global member
    exact mem_finiteRootUniverse.mpr (bound.results callee global member)

def moduleRootCount (module : GIR.Module) : Nat :=
  module.globals.size + module.funcs.foldl (fun n f => n + f.params.length + f.slots.size) 0

private theorem functionFold_lower (funcs : List Func) (start : Nat) :
    start ≤ funcs.foldl (fun n f => n + f.params.length + f.slots.size) start := by
  apply List.foldlRecOn (motive := fun n => start ≤ n) funcs _ (Nat.le_refl _)
  intro n prior func _
  omega

private theorem functionFold_member {funcs : List Func} {func : Func} (member : func ∈ funcs)
    (start : Nat) :
    func.params.length + func.slots.size ≤
      funcs.foldl (fun n f => n + f.params.length + f.slots.size) start := by
  induction funcs generalizing start with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      have lower := functionFold_lower rest (start + func.params.length + func.slots.size)
      exact Nat.le_trans (by omega) lower
    · exact ih member _

theorem finiteRootUniverse_le_module {module : GIR.Module} {func : Func}
    (member : func ∈ module.funcs.toList) :
    (finiteRootUniverse module.globals.size func).length ≤ moduleRootCount module := by
  have lower := functionFold_member member 0
  rw [Array.foldl_toList] at lower
  rw [finiteRootUniverse_length]
  unfold moduleRootCount
  omega

theorem provenance_bounded {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    (rootCount : Nat) : Bounded roots (func.provenance results types rootCount) :=
  provFix_bounded universeBound _ (provStart_bounded universeBound)

theorem provenance_sizes (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (rootCount : Nat) :
    (func.provenance results types rootCount).slots.size = func.slots.size ∧
      (func.provenance results types rootCount).vals.size = func.numValues := by
  have extension := provFix_extends results types func
    ((func.numValues + func.slots.size + 1) * (rootCount + 1)) (provStart types func)
  constructor
  · change (provFix results types func _ _).slots.size = func.slots.size
    rw [extension.1]
    simp [provStart]
  · exact extension.2.1.trans (provStart_values_size func types)

theorem provenance_weight_le {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {roots : List RootRef} (universeBound : RootUniverse results func roots)
    (rootCount : Nat) :
    weight (func.provenance results types rootCount) ≤
      (func.slots.size + func.numValues) * roots.length := by
  have bound := (provenance_bounded (types := types) universeBound rootCount).weight_le
  have sizes := provenance_sizes results types func rootCount
  simpa only [sizes.1, sizes.2] using bound

theorem provenance_module_fixed {module : GIR.Module} {func : Func}
    {results : Array (List RootRef)} {types : Array (Option VTy)}
    (member : func ∈ module.funcs.toList) (bound : RootBounds results func module.globals.size) :
    provRound results types func (func.provenance results types (moduleRootCount module)) =
      (func.provenance results types (moduleRootCount module), false) :=
  provenance_fixed bound.finite _ (finiteRootUniverse_le_module member)

theorem provenance_module_instructionRootsClosed {module : GIR.Module} {func : Func}
    {results : Array (List RootRef)} {types : Array (Option VTy)}
    (member : func ∈ module.funcs.toList) (bound : RootBounds results func module.globals.size) :
    InstructionRootsClosed results types func (func.provenance results types (moduleRootCount module)) :=
  provenance_instructionRootsClosed bound.finite _ (finiteRootUniverse_le_module member)

end Goose.Lower.Validation.ProvenanceConvergence
