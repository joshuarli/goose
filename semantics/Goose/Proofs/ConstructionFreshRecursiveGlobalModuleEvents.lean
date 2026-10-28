import Goose.Proofs.ConstructionFreshRecursiveGlobalSequenceEvents
import Goose.Proofs.ConstructionFreshMixedModuleEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem runModule_recursiveGlobalMixed_fresh_events (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globalDeclarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveGlobalInitializer descriptor)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedAssignStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localTargets : ∀ id expression origin, .assign (.var id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (globalTargets : ∀ id expression origin, .assign (.global id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = none) :
    ∃ events,
      (Goose.Proofs.Exit.stepState (runModule fuel config .initial)).construction.events = events ∧
      ∀ event ∈ events, ByteOwnerSequenceEvent event := by
  obtain ⟨globalEvents, globalTrace, globalValid⟩ := initGlobals_recursive_initial_fresh_events fuel config accepted globalDeclarations
  cases globals : initGlobals fuel config (List.range config.module.globals.size) .initial with
  | stop reason after =>
    simp only [globals, Goose.Proofs.Exit.stepState] at globalTrace
    refine ⟨globalEvents, ?_, globalValid⟩
    simpa only [runModule, bind, globals, Goose.Proofs.Exit.stepState] using globalTrace
  | escape target carriers after =>
    simp only [globals, Goose.Proofs.Exit.stepState] at globalTrace
    refine ⟨globalEvents, ?_, globalValid⟩
    simpa only [runModule, bind, globals, Goose.Proofs.Exit.stepState] using globalTrace
  | jump target kind after =>
    simp only [globals, Goose.Proofs.Exit.stepState] at globalTrace
    refine ⟨globalEvents, ?_, globalValid⟩
    simpa only [runModule, bind, globals, Goose.Proofs.Exit.stepState] using globalTrace
  | ok result initialized =>
    cases result
    simp only [globals, Goose.Proofs.Exit.stepState] at globalTrace
    obtain ⟨original', implementation', originalFound, implementationFound, parametersEmpty, resultsEmpty⟩ :=
      validated_entry config.module accepted.accepted
    have originalEq : original' = original := Option.some.inj (originalFound.symm.trans originalAt)
    subst original'
    have implementationEq : implementation' = implementation := Option.some.inj (implementationFound.symm.trans implementationAt)
    subst implementation'
    have run : runModule fuel config .initial =
        (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized := by
      simp only [runModule, bind, globals, getImplementation, originalAt, implementationAt, resultsEmpty,
        Array.toList_empty, channelsFor, List.mapM_nil, pure]
    by_cases small : fuel < 3
    · have trace := entry_low_events fuel config initialized original implementation originalAt implementationAt parametersEmpty resultsEmpty small
      refine ⟨globalEvents, ?_, globalValid⟩
      rw [run, trace, globalTrace]
    · let remaining := fuel - 3
      have fuelEq : fuel = remaining + 3 := by dsimp [remaining]; omega
      obtain ⟨completed, globalLive, regions, bound, globalWorld, globalFlow⟩ :=
        initGlobals_recursive_initial_complete fuel config accepted globalDeclarations
      simp only [globals, Goose.Proofs.Exit.stepState] at globalWorld globalFlow
      obtain ⟨completedEq, regionsEq, clear⟩ := globalFlow
      subst completed regions
      obtain ⟨localEvents, localTrace, localValid⟩ := mixedEntry_world_events remaining config accepted initialized original implementation
        globalLive globalWorld originalAt implementationAt form owners scalarOwners localTargets globalTargets tail
      have localTrace' : (Goose.Proofs.Exit.stepState ((invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
          fun carriers => publishCarriers 0 carriers) initialized)).construction.events = initialized.construction.events ++ localEvents := by
        rw [fuelEq]; exact localTrace
      refine ⟨globalEvents ++ localEvents, ?_, ?_⟩
      · rw [run, localTrace', globalTrace]
      · intro event member
        simp only [List.mem_append] at member
        rcases member with member | member
        · exact globalValid event member
        · exact localValid event member


#print axioms runModule_recursiveGlobalMixed_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
