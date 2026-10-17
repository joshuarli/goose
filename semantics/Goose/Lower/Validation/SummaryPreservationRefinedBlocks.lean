import Goose.Lower.Validation.SummaryPreservationRefinedBuilder

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem newBlock_empty_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {ls : LS} {le : LEnv} {scopeCount : Nat}
    (symbols : ls.SymbolWF le scopeCount) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls) :
    BuilderRootWitness results vt func upper (newBlock [] le ls).2 ∧
      BuilderEffectRefinement module vt func upper source (newBlock [] le ls).2 := by
  rw [newBlock0_run]
  have sameInstructions : ({ ls with blocks := ls.blocks.push ⟨[], #[]⟩ } : LS).insts = ls.insts := by
    simp [LS.insts, Array.toList_push]
  refine ⟨⟨witness.valueSize, ?_⟩, ?_⟩
  · intro inst member
    rw [sameInstructions] at member
    exact builder_instruction_roots_after_newBlock symbols ⟨[], #[]⟩ witness.instructions inst member
  · intro inst member
    rw [sameInstructions] at member
    exact prior inst member


theorem newBlock_parameter_refined_frame {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} (parameterRoots : List RootRef)
    {ls : LS} {le : LEnv} {scopeCount : Nat} (ty : VTy)
    (symbols : ls.SymbolWF le scopeCount) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls) :
    ∃ next : Prov, BuilderRootWitness results vt func next (newBlock [ty] le ls).2 ∧
      BuilderEffectRefinement module vt func next source (newBlock [ty] le ls).2 ∧
      rootsAt next.vals ls.vals.size = parameterRoots ∧ next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  let next : Prov := { upper with vals := upper.vals.push parameterRoots }
  rw [newBlock1_run]
  have sameInstructions : ({ ls with
      blocks := ls.blocks.push ⟨[(ls.vals.size, ty)], #[]⟩,
      vals := ls.vals.push (some ty) } : LS).insts = ls.insts := by
    simp [LS.insts, Array.toList_push]
  have grown := builder_instruction_roots_after_push (newRoots := parameterRoots)
    symbols witness.valueSize (func := { func with blocks := finishBlocks ls.blocks })
    rfl witness.instructions
  refine ⟨next, ⟨?_, ?_⟩, ?_, ?_, rfl, ?_⟩
  · simp [next, witness.valueSize]
  · intro inst member
    rw [sameInstructions] at member
    exact builder_instruction_roots_after_newBlock symbols ⟨[(ls.vals.size, ty)], #[]⟩ grown inst member
  · intro inst member
    rw [sameInstructions] at member
    have stable : func.effectStep module vt next {} inst = func.effectStep module vt upper {} inst := by
      apply effectStep_push_fresh
      intro value used
      rw [witness.valueSize]
      exact (symbols.instructions inst member).uses value used
    rw [stable]
    exact prior inst member
  · change rootsAt (upper.vals.push parameterRoots) ls.vals.size = parameterRoots
    rw [← witness.valueSize, rootsAt_push_new]
  · intro index bound
    exact rootsAt_push_old bound

theorem newBlock_parameter_refined_witness {module : GIR.Module}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    {source : Core.Eff} {sourceRoots parameterRoots : List RootRef}
    {ls : LS} {le : LEnv} {scopeCount : Nat} (ty : VTy)
    (symbols : ls.SymbolWF le scopeCount) (witness : BuilderRootWitness results vt func upper ls)
    (prior : BuilderEffectRefinement module vt func upper source ls)
    (parameter : RootsRefine func parameterRoots sourceRoots) :
    ∃ next : Prov, BuilderRootWitness results vt func next (newBlock [ty] le ls).2 ∧
      BuilderEffectRefinement module vt func next source (newBlock [ty] le ls).2 ∧
      RootsRefine func (rootsAt next.vals ls.vals.size) sourceRoots ∧ next.slots = upper.slots ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, roots, effects, exactRoots, slots, growth⟩ :=
    newBlock_parameter_refined_frame parameterRoots ty symbols witness prior
  exact ⟨next, roots, effects, by simpa [exactRoots] using parameter, slots, growth⟩

end Goose.Lower.Validation.SummaryPreservation
