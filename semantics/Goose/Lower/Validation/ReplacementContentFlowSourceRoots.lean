import Goose.GIR.ReplacementContentFlowProofs
import Goose.Lower.Validation.SummaryPreservationParameters

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open SummaryPreservation

theorem normalize_empty (func : Func) : normalize func (.known []) = some [] := rfl

theorem normalize_local (func : Func) (slot : SlotId) :
    normalize func (.known [.local slot]) = some [.local slot] := by
  simp [normalize, normalizeAtom, unionRoots]

theorem normalize_global (func : Func) (global : GlobalId) :
    normalize func (.known [.global global]) = some [.global global] := by
  simp [normalize, normalizeAtom, unionRoots]

theorem normalize_parameter (func : Func) (index : Nat) :
    normalize func (.known [.param index]) = some (unionRoots [] (func.parameterRoots index)) := by
  simp [normalize, normalizeAtom]

theorem normalize_contents {func : Func} {index : Nat} {roots : List RootRef}
    (annotation : func.roots.contents.find? (·.1 == index) = some (index, roots)) :
    normalize func (.known [.contents index]) =
      some (unionRoots [] (roots.flatMap func.expandParameterRoot)) := by
  simp [normalize, normalizeAtom, annotation]

theorem lowerContextAt_parameter_normalized {module : Core.Module} {ctx : Context} {impl : Impl}
    {index : Nat} {param : Param} {roots : List RootRef}
    (parameter : impl.params[index]? = some param)
    (annotation : (ctx.varRoots.find? (·.1 == param.var)).map (·.2) = some roots) :
    ∃ actual, normalize (lowerContextAt module ctx impl) (.known [.param index]) = some actual ∧
      ∀ root ∈ actual, root ∈ roots := by
  refine ⟨unionRoots [] roots, ?_, ?_⟩
  · rw [normalize_parameter, lowerContextAt_parameterRoots_eq parameter annotation]
  · intro root member
    exact (mem_unionRoots_iff.mp member).elim (fun impossible => nomatch impossible) id

theorem lowerContextAt_contents_normalized {module : Core.Module} {ctx : Context} {impl : Impl}
    {index : Nat} {param : Param} {roots : List RootRef}
    (parameter : impl.params[index]? = some param)
    (annotation : (ctx.contentRoots.find? (·.1 == param.var)).map (·.2) = some roots) :
    ∃ actual, normalize (lowerContextAt module ctx impl) (.known [.contents index]) = some actual ∧
      ∀ root ∈ actual, root ∈ roots.flatMap (lowerContextAt module ctx impl).expandParameterRoot := by
  refine ⟨unionRoots [] (roots.flatMap (lowerContextAt module ctx impl).expandParameterRoot), ?_, ?_⟩
  · apply normalize_contents
    exact lowerContextRootInfo_contents_eq parameter annotation
  · intro root member
    exact (mem_unionRoots_iff.mp member).elim (fun impossible => nomatch impossible) id

theorem accepted_storageClosed {module : Core.Module}
    (accepted : Core.validate module = .ok ()) : storageClosed (lower module) = true := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro lowered member
  obtain ⟨global, globalMember, identity⟩ := Array.mem_map.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp globalMember
  have checked := (Core.Sound.validate_modOk module accepted).glob index global row
  subst lowered
  simp only [lowerGlobal, checked.ty.1, checked.ty.2, Bool.not_false, Bool.and_self]

#print axioms accepted_storageClosed
#print axioms lowerContextAt_parameter_normalized
#print axioms lowerContextAt_contents_normalized

end Goose.Lower.Validation.ReplacementContentFlowSource
