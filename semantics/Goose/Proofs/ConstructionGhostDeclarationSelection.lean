import Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents

namespace Goose.Proofs.ConstructionGhostDeclarationSelection
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostDeclarationFallback
open Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents Goose.Proofs.ConstructionGhostNonfixedDeclaration
open Goose.Proofs.ConstructionGhostMaterialization Goose.Proofs.ConstructionGhostDeclarationOnce

inductive Selection (environment : RuntimeActivation) (implementation : Impl)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) (before : ExecutionState) : Prop
  | fallback (ready : ExecutionState) (selection : DeclarationFallback environment implementation localVar origin before ready)
  | named (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId)
      (selectedReady : ExecutionState) (pending : PendingDestination) (ready : ExecutionState)
      (found : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
      (channel : environment.channels[index]? = some (.construct incoming))
      (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok selected selectedReady)
      (queried : getDestination selected selectedReady = .ok pending ready) (valueRequest : pending.capability.request = .value)
  | badChannel (result : ResultDescriptor) (index : Nat)
      (found : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
      (bad : ∀ incoming, environment.channels[index]? ≠ some (.construct incoming))
  | renewalTerminal (result : ResultDescriptor) (index : Nat) (incoming : Goose.Core.DestinationId) (terminal : DeclarationTerminal)
      (found : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
      (channel : environment.channels[index]? = some (.construct incoming))
      (renewed : liftConstruction origin (renewReceivingDestination incoming) before = terminal.step)
  | queryTerminal (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId)
      (selectedReady : ExecutionState) (terminal : DeclarationTerminal)
      (found : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
      (channel : environment.channels[index]? = some (.construct incoming))
      (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok selected selectedReady)
      (queried : getDestination selected selectedReady = terminal.step)

theorem selection_exists (environment : RuntimeActivation) (implementation : Impl)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    Selection environment implementation localVar origin before := by
  cases found : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) with
  | none => exact .fallback before (.absent before found)
  | some pair =>
      obtain ⟨result, index⟩ := pair
      cases channel : environment.channels[index]? with
      | none => exact .badChannel result index found (by intro incoming; simp [channel])
      | some value =>
          cases value with
          | register ty => exact .badChannel result index found (by intro incoming; simp [channel])
          | completion ticket => exact .badChannel result index found (by intro incoming; simp [channel])
          | construct incoming =>
              cases renewed : liftConstruction origin (renewReceivingDestination incoming) before with
              | stop reason state => exact .renewalTerminal result index incoming (.stopped reason state) found channel renewed
              | escape address carriers state => exact .renewalTerminal result index incoming (.escaped address carriers state) found channel renewed
              | jump target kind state => exact .renewalTerminal result index incoming (.jumped target kind state) found channel renewed
              | ok selected selectedReady =>
                  cases queried : getDestination selected selectedReady with
                  | stop reason state => exact .queryTerminal result index incoming selected selectedReady (.stopped reason state) found channel renewed queried
                  | escape address carriers state => exact .queryTerminal result index incoming selected selectedReady (.escaped address carriers state) found channel renewed queried
                  | jump target kind state => exact .queryTerminal result index incoming selected selectedReady (.jumped target kind state) found channel renewed queried
                  | ok pending ready =>
                      by_cases valueRequest : pending.capability.request = .value
                      · exact .named result index incoming selected selectedReady pending ready found channel renewed queried valueRequest
                      · exact .fallback ready (.selected before selectedReady ready result index incoming selected pending found channel renewed queried valueRequest)

theorem selection_source_or_terminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implemented : config.module.impls[environment.implementation]? = some implementation) :
    (∃ ready, DeclarationFallback environment implementation localVar origin rootReady ready) ∨
    (∃ result index incoming selected selectedReady pending ready,
      (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index) ∧
      environment.channels[index]? = some (.construct incoming) ∧
      liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady ∧
      getDestination selected selectedReady = .ok pending ready ∧ pending.capability.request = .value) ∨
    (∃ terminal : DeclarationTerminal, execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step) := by
  cases selection_exists environment implementation localVar origin rootReady with
  | fallback ready selection => exact Or.inl ⟨ready, selection⟩
  | named result index incoming selected selectedReady pending ready named channel renewed queried valueRequest =>
      exact Or.inr (Or.inl ⟨result, index, incoming, selected, selectedReady, pending, ready, named, channel, renewed, queried, valueRequest⟩)
  | badChannel result index named bad =>
      exact Or.inr (Or.inr ⟨.stopped (.fault .flow) rootReady,
        nonfixedDeclaration_badNamedChannel fuel config environment localVar expression origin before rootReady descriptor root implementation
          result index found nonfixed rootResult implemented named bad⟩)
  | renewalTerminal result index incoming terminal named channel renewed =>
      exact Or.inr (Or.inr ⟨terminal, nonfixedDeclaration_renewalTerminal fuel config environment localVar expression origin before rootReady
        descriptor root implementation result index incoming terminal found nonfixed rootResult implemented named channel renewed⟩)
  | queryTerminal result index incoming selected selectedReady terminal named channel renewed queried =>
      exact Or.inr (Or.inr ⟨terminal, nonfixedDeclaration_lookupTerminal fuel config environment localVar expression origin before rootReady
        selectedReady descriptor root implementation result index incoming selected terminal found nonfixed rootResult implemented named channel renewed queried⟩)

theorem fallback_allocationTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady ready : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (terminal : DeclarationTerminal)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implemented : config.module.impls[environment.implementation]? = some implementation)
    (fallback : DeclarationFallback environment implementation localVar origin rootReady ready)
    (direct : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = none)
    (allocated : newDestination config.layout environment.act descriptor.ty .value origin none
      (producerCount? ⟨config.module, environment.vars⟩ expression) ready = terminal.step) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step := by
  rw [fallback_execution fuel config environment localVar expression origin before rootReady ready descriptor root implementation
    found nonfixed rootResult implemented fallback]
  rw [materializeProducer_none fuel ⟨config.module, environment.vars⟩ expression (evalValue fuel config environment expression) ready direct]
  cases terminal <;> simp_all [declarationAfterMaterialization, declarationContinuation, DeclarationTerminal.step, bind, pure]

theorem named_renewalTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady selectedReady ready : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId) (pending : PendingDestination)
    (terminal : DeclarationTerminal)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implemented : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
    (channel : environment.channels[index]? = some (.construct incoming))
    (selectedResult : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
    (queried : getDestination selected selectedReady = .ok pending ready) (valueRequest : pending.capability.request = .value)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) ready = terminal.step) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step := by
  cases terminal <;> simp_all [DeclarationTerminal.step, execStmt, bind, pure]

theorem named_prepareTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady selectedReady ready renewedReady : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming selected destination : Goose.Core.DestinationId) (pending : PendingDestination)
    (terminal : DeclarationTerminal)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implemented : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
    (channel : environment.channels[index]? = some (.construct incoming))
    (selectedResult : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
    (queried : getDestination selected selectedReady = .ok pending ready) (valueRequest : pending.capability.request = .value)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) ready = .ok destination renewedReady)
    (prepared : liftConstruction origin (prepareNamedBinding destination descriptor.ty) renewedReady = terminal.step) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step := by
  cases terminal <;> simp_all [DeclarationTerminal.step, execStmt, bind, pure]

theorem nonfixed_occurrence_or_terminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implemented : config.module.impls[environment.implementation]? = some implementation) :
    (∃ destination ready, DeclarationOccurrence fuel config environment localVar expression origin before destination ready) ∨
    (∃ terminal : DeclarationTerminal, execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step) := by
  rcases selection_source_or_terminal fuel config environment localVar expression origin before rootReady descriptor root implementation
      found nonfixed rootResult implemented with ⟨ready, fallback⟩ | ⟨result, index, incoming, selected, selectedReady, pending, ready,
        named, channel, selectedResult, queried, valueRequest⟩ | terminal
  · cases counted : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression with
    | some count => exact Or.inl ⟨none, ready, .materialized descriptor root rootReady implementation ready count found nonfixed rootResult implemented fallback counted⟩
    | none =>
        cases allocated : newDestination config.layout environment.act descriptor.ty .value origin none
            (producerCount? ⟨config.module, environment.vars⟩ expression) ready with
        | ok destination buildReady => exact Or.inl ⟨some destination, buildReady,
            .direct descriptor root rootReady implementation ready destination buildReady found nonfixed rootResult implemented fallback counted allocated⟩
        | stop reason state => exact Or.inr ⟨.stopped reason state,
            fallback_allocationTerminal fuel config environment localVar expression origin before rootReady ready descriptor root implementation
              (.stopped reason state) found nonfixed rootResult implemented fallback counted allocated⟩
        | escape address carriers state => exact Or.inr ⟨.escaped address carriers state,
            fallback_allocationTerminal fuel config environment localVar expression origin before rootReady ready descriptor root implementation
              (.escaped address carriers state) found nonfixed rootResult implemented fallback counted allocated⟩
        | jump target kind state => exact Or.inr ⟨.jumped target kind state,
            fallback_allocationTerminal fuel config environment localVar expression origin before rootReady ready descriptor root implementation
              (.jumped target kind state) found nonfixed rootResult implemented fallback counted allocated⟩
  · cases renewed : liftConstruction origin (renewReceivingDestination incoming) ready with
    | stop reason state => exact Or.inr ⟨.stopped reason state,
        named_renewalTerminal fuel config environment localVar expression origin before rootReady selectedReady ready descriptor root implementation
          result index incoming selected pending (.stopped reason state) found nonfixed rootResult implemented named channel selectedResult queried valueRequest renewed⟩
    | escape address carriers state => exact Or.inr ⟨.escaped address carriers state,
        named_renewalTerminal fuel config environment localVar expression origin before rootReady selectedReady ready descriptor root implementation
          result index incoming selected pending (.escaped address carriers state) found nonfixed rootResult implemented named channel selectedResult queried valueRequest renewed⟩
    | jump target kind state => exact Or.inr ⟨.jumped target kind state,
        named_renewalTerminal fuel config environment localVar expression origin before rootReady selectedReady ready descriptor root implementation
          result index incoming selected pending (.jumped target kind state) found nonfixed rootResult implemented named channel selectedResult queried valueRequest renewed⟩
    | ok destination renewedReady =>
        cases prepared : liftConstruction origin (prepareNamedBinding destination descriptor.ty) renewedReady with
        | ok unit buildReady =>
            cases unit
            exact Or.inl ⟨some destination, buildReady, .named descriptor root rootReady implementation result index incoming selected selectedReady
              pending ready destination renewedReady buildReady found nonfixed rootResult implemented named channel selectedResult queried valueRequest renewed prepared⟩
        | stop reason state => exact Or.inr ⟨.stopped reason state,
            named_prepareTerminal fuel config environment localVar expression origin before rootReady selectedReady ready renewedReady descriptor root implementation
              result index incoming selected destination pending (.stopped reason state) found nonfixed rootResult implemented named channel selectedResult queried valueRequest renewed prepared⟩
        | escape address carriers state => exact Or.inr ⟨.escaped address carriers state,
            named_prepareTerminal fuel config environment localVar expression origin before rootReady selectedReady ready renewedReady descriptor root implementation
              result index incoming selected destination pending (.escaped address carriers state) found nonfixed rootResult implemented named channel selectedResult queried valueRequest renewed prepared⟩
        | jump target kind state => exact Or.inr ⟨.jumped target kind state,
            named_prepareTerminal fuel config environment localVar expression origin before rootReady selectedReady ready renewedReady descriptor root implementation
              result index incoming selected destination pending (.jumped target kind state) found nonfixed rootResult implemented named channel selectedResult queried valueRequest renewed prepared⟩
  · exact Or.inr terminal

theorem declaration_occurrence_or_terminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    (∃ destination ready, DeclarationOccurrence fuel config environment localVar expression origin before destination ready) ∨
    (∃ terminal : DeclarationTerminal, execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step) := by
  cases found : environment.vars[localVar]? with
  | none =>
      right
      refine ⟨.stopped (.fault .unbound) before, ?_⟩
      simp [execStmt, found, fault, EvalM.stop, DeclarationTerminal.step]
  | some descriptor =>
      cases rootResult : rootOf environment localVar before with
      | stop reason state =>
          right
          refine ⟨.stopped reason state, ?_⟩
          simp [execStmt, found, bind, rootResult, DeclarationTerminal.step]
      | escape address carriers state =>
          right
          refine ⟨.escaped address carriers state, ?_⟩
          simp [execStmt, found, bind, rootResult, DeclarationTerminal.step]
      | jump target kind state =>
          right
          refine ⟨.jumped target kind state, ?_⟩
          simp [execStmt, found, bind, rootResult, DeclarationTerminal.step]
      | ok root rootReady =>
          cases fixed : descriptor.ty.nonfixed with
          | false => exact Or.inl ⟨none, rootReady, .fixed descriptor root rootReady found fixed rootResult⟩
          | true =>
              cases implemented : config.module.impls[environment.implementation]? with
              | none =>
                  right
                  refine ⟨.stopped (.fault .unbound) rootReady, ?_⟩
                  simp [execStmt, found, bind, rootResult, fixed, implemented, fault, EvalM.stop, DeclarationTerminal.step]
              | some implementation =>
                  exact nonfixed_occurrence_or_terminal fuel config environment localVar expression origin before rootReady descriptor root implementation
                    found fixed rootResult implemented

theorem declaration_history_or_terminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState) (path : List Nat)
    (history : SourceHistory config (fuel + 1) path (.statement environment (.letS localVar expression origin)) before
      (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)) :
    (∃ destination ready, DeclarationOccurrence fuel config environment localVar expression origin before destination ready ∧
      (∀ other otherReady, DeclarationOccurrence fuel config environment localVar expression origin before other otherReady →
        destination = other ∧ ready = otherReady) ∧
      match destination with
      | none => SourceHistory config fuel (path ++ [0]) (.value environment expression) ready
          (evalValue fuel config environment expression ready) ∧
          Goose.Proofs.ConstructionExecution.EventPrefix
            (Goose.Proofs.Exit.stepState (evalValue fuel config environment expression ready)).construction.events
            (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)).construction.events
      | some destination => SourceHistory config fuel (path ++ [0]) (.builder environment destination expression) ready
          (buildExpr fuel config environment destination expression ready) ∧
          Goose.Proofs.ConstructionExecution.EventPrefix
            (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination expression ready)).construction.events
            (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)).construction.events) ∨
    (∃ terminal : DeclarationTerminal, execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step) := by
  rcases declaration_occurrence_or_terminal fuel config environment localVar expression origin before with ⟨destination, ready, occurrence⟩ | terminal
  · left
    refine ⟨destination, ready, occurrence, ?_, ?_⟩
    · intro other otherReady otherOccurrence
      exact DeclarationOccurrence.unique occurrence otherOccurrence
    · exact Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents.DeclarationOccurrence.historyAndEvents occurrence history
  · exact Or.inr terminal

#print axioms declaration_history_or_terminal
#print axioms declaration_occurrence_or_terminal
#print axioms nonfixed_occurrence_or_terminal
#print axioms fallback_allocationTerminal
#print axioms named_renewalTerminal
#print axioms named_prepareTerminal
#print axioms selection_source_or_terminal
#print axioms selection_exists
end Goose.Proofs.ConstructionGhostDeclarationSelection
