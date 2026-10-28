import Goose.Proofs.ConstructionAcceptedMixedAssignModule
import Goose.Proofs.ConstructionFreshByteModuleEvents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private theorem mixedEntry_high_events (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : ExecutionState) (original : Context) (implementation : Impl)
    (globalDeclarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (globals : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized)
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
    ∃ suffix,
      (Goose.Proofs.Exit.stepState ((invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
        fun carriers => publishCarriers 0 carriers) initialized)).construction.events = initialized.construction.events ++ suffix ∧
      ∀ event ∈ suffix, ByteOwnerSequenceEvent event := by
  have globals' : initGlobals ((fuel + 2) + 1) config (List.range config.module.globals.size) .initial = .ok () initialized := by
    simpa only [Nat.add_assoc] using globals
  obtain ⟨globalLive, globalWorld, clear⟩ := initGlobals_byteOwners_initial (fuel + 2) config accepted initialized globalDeclarations globals'
  obtain ⟨frame, next, activation, types, nextLive, regions, channels, implementationEq, call,
    ⟨suffix, trace, valid⟩, bodyResult⟩ :=
      acceptedMixedAssignEntry_normal_scope_events fuel config accepted initialized globalLive original implementation globalWorld
        originalAt implementationAt form owners scalarOwners localTargets globalTargets tail
  let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  have bodyFrame : (Goose.Proofs.Exit.stepState (execActivationBody (fuel + 1) config activation [] frame.source.impl.body activated)).construction.events =
      (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before)).construction.events := by
    change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
      | .ok (.normal .unit) after => _ | .stop reason after => _ | _ => False) at bodyResult
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | stop reason after =>
      simp only [outcome] at bodyResult
      obtain ⟨stopped, _⟩ := bodyResult
      change execActivationBody (fuel + 1) config activation [] frame.source.impl.body activated = .stop reason after at stopped
      simp only [outcome, stopped, Goose.Proofs.Exit.stepState]
    | escape target carriers after | jump target kind after => simp only [outcome] at bodyResult
    | ok flow after =>
      simp only [outcome] at bodyResult
      cases flow with
      | breaking value | continuing => cases bodyResult
      | normal value =>
        cases value with
        | unit =>
          obtain ⟨done, _⟩ := bodyResult
          change execActivationBody (fuel + 1) config activation [] frame.source.impl.body activated =
            .ok [] (releaseScopeState activation frame.source.impl.body.scope activated.nextScope after) at done
          simp only [outcome, done, Goose.Proofs.Exit.stepState, releaseScopeState]
        | _ => cases bodyResult
  have frameTrace : (Goose.Proofs.Exit.stepState ((invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
      fun carriers => publishCarriers 0 carriers) initialized)).construction.events =
      (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before)).construction.events := by
    simp only [bind]
    rw [call]
    change (Goose.Proofs.Exit.stepState (((finishActivation config.layout activation [] 0
      (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
        deliverCarriers (fuel + 2) config.layout [] carriers 0) >>= fun carriers => publishCarriers 0 carriers) activated)).construction.events = _
    rw [eval_bind_assoc]
    rw [bind_events_frame]
    · rw [finishActivation_empty_events config.layout activation channels]
      exact bodyFrame
    · intro carriers current
      exact deliverPublish_empty_events (fuel + 2) config.layout 0 carriers current
  refine ⟨suffix, ?_, valid⟩
  rw [frameTrace, trace]
  rfl

theorem runModule_mixedByteScalar_fresh_events (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globalDeclarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
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
  obtain ⟨globalEvents, globalTrace, globalValid⟩ := initGlobals_acceptedByteOwners_fresh_events fuel config accepted globalDeclarations
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
      have globals' : initGlobals (remaining + 3) config (List.range config.module.globals.size) .initial = .ok () initialized := by
        rw [← fuelEq]; exact globals
      obtain ⟨localEvents, localTrace, localValid⟩ := mixedEntry_high_events remaining config accepted initialized original implementation
        globalDeclarations globals' originalAt implementationAt form owners scalarOwners localTargets globalTargets tail
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

#print axioms runModule_mixedByteScalar_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
