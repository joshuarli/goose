import Goose.Lower.Validation.ReplacementContentFlowSourceSymbolic
import Goose.Lower.Validation.SummaryPreservationRootRefinement

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open SummaryPreservation

def SymbolicRootsRefine (func : Func) (roots : Roots) (source : List RootRef) : Prop :=
  roots = .pending ∨ ∃ actual, symbolicRoots func roots = some actual ∧
    SummaryPreservation.RootsRefine func actual source

theorem SymbolicRootsRefine.pending (func : Func) (source : List RootRef) :
    SymbolicRootsRefine func .pending source := Or.inl rfl

theorem SymbolicRootsRefine.source_mono {func : Func} {roots : Roots} {source larger : List RootRef}
    (bounded : SymbolicRootsRefine func roots source) (within : source ⊆ larger) :
    SymbolicRootsRefine func roots larger := by
  rcases bounded with pending | ⟨actual, known, refined⟩
  · exact Or.inl pending
  · exact Or.inr ⟨actual, known, refined.source_mono (fun _ member => within member)⟩

theorem SymbolicRootsRefine.join {func : Func} {left right : Roots} {source : List RootRef}
    (leftBound : SymbolicRootsRefine func left source)
    (rightBound : SymbolicRootsRefine func right source) :
    SymbolicRootsRefine func (left.join right) source := by
  rcases leftBound with pending | ⟨leftRoots, leftKnown, leftRefined⟩
  · subst left
    have same : Roots.pending.join right = right := by cases right <;> rfl
    rwa [same]
  · rcases rightBound with pending | ⟨rightRoots, rightKnown, rightRefined⟩
    · subst right
      have same : left.join Roots.pending = left := by cases left <;> rfl
      rw [same]
      exact Or.inr ⟨leftRoots, leftKnown, leftRefined⟩
    · obtain ⟨actual, known, within⟩ := normalize_join_known
        { func with roots := { func.roots with params := #[] } } left right
        leftRoots rightRoots leftKnown rightKnown
      refine Or.inr ⟨actual, known, ?_⟩
      intro root member
      exact (within root member).elim (leftRefined root) (rightRefined root)

theorem SymbolicRootsRefine.actual {func : Func} {roots : Roots} {source : List RootRef}
    (closed : ParameterRootsClosed func) (bounded : SymbolicRootsRefine func roots source)
    (ready : roots ≠ .pending) :
    ∃ actual, normalize func roots = some actual ∧
      actual ⊆ source.flatMap func.expandParameterRoot := by
  obtain ⟨symbolic, known, refined⟩ := bounded.resolve_left ready
  obtain ⟨actual, actualKnown, within⟩ := symbolicRoots_actual_within known
  refine ⟨actual, actualKnown, ?_⟩
  intro root member
  obtain ⟨symbol, symbolMember, expanded⟩ := List.mem_flatMap.mp (within root member)
  exact refined.expanded closed symbol symbolMember root expanded

theorem SymbolicRootsRefine.global_iff (func : Func) (global : GlobalId) (source : List RootRef) :
    SymbolicRootsRefine func (.known [.global global]) source ↔ RootRef.global global ∈ source := by
  have known : symbolicRoots func (.known [.global global]) = some [.global global] := rfl
  simp [SymbolicRootsRefine, known, Goose.GIR.RootsRefine, Func.expandParameterRoot]

theorem SymbolicRootsRefine.parameter_iff (func : Func) (index : Nat) (source : List RootRef) :
    SymbolicRootsRefine func (.known [.param index]) source ↔
      RootRef.param index ∈ source ∨ func.parameterRoots index ⊆ source := by
  simp [SymbolicRootsRefine, symbolicRoots_parameter, Goose.GIR.RootsRefine, Func.expandParameterRoot,
    List.subset_def]

theorem SymbolicRootsRefine.contents {func : Func} {index : Nat} {source : List RootRef}
    (row : func.roots.contents.find? (·.1 == index) = some (index, source)) :
    SymbolicRootsRefine func (.known [.contents index]) source := by
  refine Or.inr ⟨unionRoots [] source, symbolicRoots_contents row, ?_⟩
  intro root member
  exact Or.inl (((unionRoots_mem_iff _ _ _).mp member).resolve_left (by simp))

theorem SymbolicRootsRefine.rootMap (func : Func) (source : List RootRef) :
    SymbolicRootsRefine func (.known (source.eraseDups.map Atom.ofRootRef)) source := by
  let observer : Func := { func with roots := { func.roots with params := #[] } }
  have expansion : observer.expandParameterRoot = fun root => [root] := by
    funext root
    cases root <;> simp [observer, Func.expandParameterRoot, Func.parameterRoots]
  obtain ⟨actual, known, members⟩ := normalize_rootMap_dedup_known observer source
  refine Or.inr ⟨actual, known, ?_⟩
  intro root member
  apply Or.inl
  have literal := (members root).mp member
  simpa [expansion] using literal

theorem checkStore_symbolic_join {env : PEnv} {varId : VarId} {localVar : LocalVar}
    {storedRoots bound : List RootRef} {current value : Roots}
    (variableRow : env.impl.vars[varId]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (contentRow : env.cont varId = some bound)
    (checked : checkStore env (.deref (.read (.var varId))) storedRoots = .ok ())
    (currentBound : SymbolicRootsRefine (lowerContextAt env.mod env.ctx env.impl) current bound)
    (valueBound : SymbolicRootsRefine (lowerContextAt env.mod env.ctx env.impl) value storedRoots) :
    SymbolicRootsRefine (lowerContextAt env.mod env.ctx env.impl) (current.join value) bound := by
  have sliceVariable : env.isRefSliceVar varId = true := by
    simp [PEnv.isRefSliceVar, variableRow, reference]
  obtain ⟨actualBound, actualRow, within⟩ :=
    checkStore_ok env _ storedRoots checked varId rfl sliceVariable
  have same : actualBound = bound := Option.some.inj (actualRow.symm.trans contentRow)
  subst actualBound
  exact currentBound.join (SymbolicRootsRefine.source_mono valueBound (by intro root member; exact within root member))

#print axioms SymbolicRootsRefine.global_iff
#print axioms SymbolicRootsRefine.parameter_iff
#print axioms SymbolicRootsRefine.contents
#print axioms SymbolicRootsRefine.rootMap
#print axioms checkStore_symbolic_join
#print axioms SymbolicRootsRefine.join
#print axioms SymbolicRootsRefine.actual

end Goose.Lower.Validation.ReplacementContentFlowSource
