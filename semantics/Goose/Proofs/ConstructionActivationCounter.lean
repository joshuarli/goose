import Goose.Proofs.ExitExecution

namespace Goose.Proofs.ConstructionActivationCounter
open Goose.Construct Goose.Proofs.ExitExecution

def PreservesActivationCounter (action : EvalM α) : Prop :=
  ∀ state, state.nextAct ≤ (Goose.Proofs.Exit.stepState (action state)).nextAct

theorem counter_pure (value : α) : PreservesActivationCounter (pure value) := by
  intro state
  exact Nat.le_refl _

theorem counter_stop (reason : Goose.Core.Stop) : PreservesActivationCounter (EvalM.stop (α := α) reason) := by
  intro state
  exact Nat.le_refl _

theorem counter_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesActivationCounter action) (remaining : ∀ value, PreservesActivationCounter (next value)) :
    PreservesActivationCounter (action >>= next) := by
  intro state
  have prior := first state
  cases result : action state with
  | ok value middle =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    have after := remaining value middle
    simp only [bind, result]
    exact Nat.le_trans prior after
  | stop reason after | escape address carriers after | jump target kind after =>
    simpa only [bind, result, Goose.Proofs.Exit.stepState] using prior

theorem counter_stateQuery (action : EvalM α) (query : StateQuery action) : PreservesActivationCounter action := by
  intro state
  rw [query state]
  exact Nat.le_refl _

theorem counter_freshAct : PreservesActivationCounter freshAct := by
  intro state
  simp [freshAct, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]

theorem counter_freshScope : PreservesActivationCounter freshScope := by
  intro state
  simp [freshScope, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]

theorem counter_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    PreservesActivationCounter (liftConstruction origin action) := by
  intro state
  cases result : action state.construction <;> simp [liftConstruction, result, Goose.Proofs.Exit.stepState]

theorem counter_get : PreservesActivationCounter EvalM.get := by
  intro state
  exact Nat.le_refl _

theorem counter_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    PreservesActivationCounter (setObjectOrdinal root ordinal) := by
  intro state
  simp [setObjectOrdinal, EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState]

theorem counter_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesActivationCounter (bindStaticRoot root value) := by
  intro state
  simp [bindStaticRoot, EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState]

theorem counter_reserveRootObject (root : Goose.Core.RootInst) :
    PreservesActivationCounter (reserveRootObject root) := by
  simp only [reserveRootObject]
  apply counter_bind
  · exact counter_get
  · intro state
    cases lookup : state.objectOrdinals.lookup root with
    | some ordinal => simp only [lookup]; exact counter_pure _
    | none =>
      simp only [lookup]
      apply counter_bind
      · exact counter_lift _ _
      · intro ordinal
        apply counter_bind
        · exact counter_setObjectOrdinal root ordinal
        · intro ignored
          exact counter_pure _

theorem counter_bindRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesActivationCounter (bindRoot root value) := by
  simp only [bindRoot]
  apply counter_bind
  · exact counter_get
  · intro state
    cases lookup : state.objectOrdinals.lookup root with
    | some ordinal => simp [lookup]; exact counter_bindStaticRoot root value
    | none =>
      simp only [lookup, Option.isNone_none, ↓reduceIte]
      cases value with
      | stored stored =>
        apply counter_bind
        · exact counter_setObjectOrdinal root _
        · intro ignored
          exact counter_bindStaticRoot root _
      | _ =>
        apply counter_bind
        · exact counter_reserveRootObject root
        · intro ignored
          exact counter_bindStaticRoot root _

#print axioms counter_bindRoot
theorem counter_listMapM (action : α → EvalM β) (items : List α)
    (preserved : ∀ item, PreservesActivationCounter (action item)) : PreservesActivationCounter (items.mapM action) := by
  induction items with
  | nil => exact counter_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply counter_bind
      · exact preserved item
      · intro value
        apply counter_bind
        · exact ih
        · intro values; exact counter_pure _

theorem counter_listForIn (action : α → β → EvalM (ForInStep β)) (items : List α)
    (initial : β) (preserved : ∀ item value, PreservesActivationCounter (action item value)) :
    PreservesActivationCounter (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact counter_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply counter_bind
      · exact preserved item initial
      · intro step
        cases step with
        | done value => exact counter_pure _
        | yield value => exact ih value

theorem counter_arrayForIn (action : α → β → EvalM (ForInStep β)) (items : Array α)
    (initial : β) (preserved : ∀ item value, PreservesActivationCounter (action item value)) :
    PreservesActivationCounter (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact counter_listForIn action items.toList initial preserved

theorem counter_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (preserved : ∀ index value, PreservesActivationCounter (action index value)) :
    PreservesActivationCounter (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact counter_listForIn action _ initial preserved

theorem counter_withScope (environment : RuntimeActivation) (scope scopeInst : Nat) (action : EvalM α)
    (preserved : PreservesActivationCounter action) : PreservesActivationCounter (withScope environment scope scopeInst action) := by
  intro state
  have after := preserved state
  cases result : action state with
  | ok value final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after
  | stop reason final => simpa [withScope, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after
  | jump target kind final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after

#print axioms counter_withScope
theorem counter_fault (reason : Goose.Core.FaultKind) : PreservesActivationCounter (fault (α := α) reason) :=
  counter_stop _

theorem counter_abortAt (reason : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (abortAt (α := α) reason origin) := counter_stop _

theorem counter_fixedWrites (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (element : Ty) (origin : Goose.Core.OriginId) (values : Array Value) :
    PreservesActivationCounter (forIn values PUnit.unit fun value _ => do
      let bytes ← liftExcept (fixedBytes fuel layout element value)
      liftConstruction origin (writeElement destination bytes)
      pure (.yield PUnit.unit)) := by
  apply counter_arrayForIn
  intro value _
  apply counter_bind
  · exact counter_stateQuery _ (stateQuery_liftExcept _)
  · intro bytes
    apply counter_bind
    · exact counter_lift _ _
    · intro _; exact counter_pure _

theorem counter_packedWrites (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (bytes : ByteArray) (run : SampledRun) (start count : Nat) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (forIn ([0:count] : Std.Legacy.Range) PUnit.unit fun index _ => do
      let (low, high) ← liftLayout (elementInterval fuel layout bytes run (start + index))
      liftConstruction origin (writeElement destination (bytes.extract low high))
      pure (.yield PUnit.unit)) := by
  apply counter_rangeForIn
  intro index _
  apply counter_bind
  · exact counter_stateQuery _ (stateQuery_liftLayout _)
  · intro interval
    rcases interval with ⟨low, high⟩
    simp only
    apply counter_bind
    · exact counter_lift _ _
    · intro _; exact counter_pure _

theorem counter_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    PreservesActivationCounter (copyValue fuel layout destination value origin source) := by
  cases fuel with
  | zero => exact counter_stop _
  | succ fuel =>
      unfold copyValue
      apply counter_bind
      · exact counter_lift _ _
      · intro current
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_getDestination current)
        · intro pending
          cases elementFound : elementType pending.capability.logicalType with
          | none => exact counter_stop _
          | some element =>
              cases value with
              | int _ _ | bool _ | unit | record _ _ | ref _ => exact counter_stop _
              | stored stored =>
                  apply counter_bind
                  · exact counter_stateQuery _ (stateQuery_sampledStored stored)
                  · intro sampled
                    rcases sampled with ⟨bytes, run⟩
                    simp only
                    split
                    · exact counter_stop _
                    · apply counter_bind
                      · exact counter_lift _ _
                      · intro _
                        apply counter_bind
                        · simpa only [Nat.zero_add] using counter_packedWrites fuel layout current bytes run 0 run.count origin
                        · intro _; exact counter_lift _ _
              | fixed values =>
                  cases source with
                  | none =>
                      apply counter_bind
                      · exact counter_fixedWrites fuel layout current element origin values
                      · intro _; exact counter_lift _ _
                  | some source =>
                      apply counter_bind
                      · exact counter_lift _ _
                      · intro _
                        apply counter_bind
                        · exact counter_fixedWrites fuel layout current element origin values
                        · intro _; exact counter_lift _ _
              | slice location start count =>
                  apply counter_bind
                  · exact counter_stateQuery _ (stateQuery_readLoc fuel layout location)
                  · intro backing
                    cases source with
                    | none => exact counter_stop _
                    | some source =>
                        cases backing with
                        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ => exact counter_stop _
                        | stored stored =>
                            apply counter_bind
                            · exact counter_stateQuery _ (stateQuery_storedPathRun stored)
                            · intro sampled
                              rcases sampled with ⟨bytes, run⟩
                              simp only
                              split
                              · exact counter_stop _
                              · split
                                · exact counter_stop _
                                · apply counter_bind
                                  · exact counter_lift _ _
                                  · intro _
                                    apply counter_bind
                                    · exact counter_packedWrites fuel layout current bytes run start count origin
                                    · intro _; exact counter_lift _ _
                        | fixed values =>
                            simp only
                            split
                            · exact counter_stop _
                            · apply counter_bind
                              · exact counter_lift _ _
                              · intro _
                                apply counter_bind
                                · exact counter_fixedWrites fuel layout current element origin (values.extract start (start + count))
                                · intro _; exact counter_lift _ _

theorem counter_newDestination (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    PreservesActivationCounter (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  cases storage with
  | none =>
      apply counter_bind
      · exact counter_lift _ _
      · intro storage
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_receivingLayout layout ty)
        · intro receiving; exact counter_lift _ _
  | some storage =>
      apply counter_bind
      · exact counter_pure _
      · intro storage
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_receivingLayout layout ty)
        · intro receiving; exact counter_lift _ _

theorem counter_channelsFor (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (channelsFor layout owner results origin) := by
  unfold channelsFor
  apply counter_listMapM
  intro descriptor
  cases descriptor.request with
  | register => exact counter_pure _
  | value | elementRun =>
      apply counter_bind
      · exact counter_newDestination _ _ _ _ _ _ _
      · intro destination; exact counter_pure _

theorem counter_completedReceivingDestination (id : Goose.Core.DestinationId) :
    PreservesActivationCounter (completedReceivingDestination id) := by
  unfold completedReceivingDestination
  apply counter_bind
  · exact counter_lift _ _
  · intro current
    exact counter_stateQuery _ (stateQuery_completedDestination current)

theorem counter_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesActivationCounter (publishCarriers origin carriers) := by
  unfold publishCarriers
  apply counter_bind
  · apply counter_stateQuery
    apply stateQuery_listMapM
    intro carrier
    cases carrier with
    | register value => exact stateQuery_pure _
    | completed id => exact stateQuery_pure _
    | pendingNamed token => exact stateQuery_stop _
  · intro ids
    exact counter_lift _ _

theorem counter_receivingDestination (id : Goose.Core.DestinationId) :
    PreservesActivationCounter (receivingDestination id) := by
  exact counter_lift _ _

private def completionLanding (origin : Goose.Core.OriginId) (token : ExitReservationId)
    (replacement : Goose.Core.DestinationId) : EvalM (ForInStep PUnit) := do
  let some (.active _ _ selected _) := (← EvalM.get).construction.exitReservations[token]? | fault .flow
  let receiving ← receivingDestination selected
  if receiving != replacement then
    liftConstruction origin (landExitReplacementInto receiving replacement)
  pure (.yield PUnit.unit)

private theorem counter_completionLanding (origin : Goose.Core.OriginId)
    (token : ExitReservationId) (replacement : Goose.Core.DestinationId) :
    PreservesActivationCounter (completionLanding origin token replacement) := by
  unfold completionLanding
  apply counter_bind
  · exact counter_get
  · intro state
    cases found : state.construction.exitReservations[token]? with
    | none => exact counter_fault .flow
    | some reservation =>
        cases reservation with
        | waiting incoming => exact counter_fault .flow
        | active role incoming selected snapshot =>
            apply counter_bind
            · exact counter_receivingDestination selected
            · intro receiving
              cases changed : (receiving != replacement) with
              | false => simp; exact counter_pure _
              | true =>
                  simp
                  apply counter_bind
                  · exact counter_lift _ _
                  · intro _; exact counter_pure _
        | restored | released => exact counter_fault .flow

theorem counter_landCarriersInto (origin : Goose.Core.OriginId) (channels : List Channel)
    (carriers : List Carrier) : PreservesActivationCounter (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  split
  · exact counter_stop _
  · simp only [bind]
    apply counter_bind
    · apply counter_listForIn
      intro item _
      cases item with
      | mk channel carrier =>
          simp only
          cases channel with
          | register ty =>
              cases carrier with
              | register value => exact counter_pure _
              | completed id | pendingNamed _ => exact counter_stop _
          | construct incoming =>
              cases carrier with
              | register value | pendingNamed _ => exact counter_stop _
              | completed replacement =>
                  simp only
                  apply counter_bind
                  · exact counter_receivingDestination incoming
                  · intro current
                    cases changed : (current != replacement) with
                    | false =>
                        simp
                        exact counter_pure _
                    | true =>
                        simp
                        apply counter_bind
                        · exact counter_lift _ _
                        · intro _; exact counter_pure _
          | completion token =>
              cases carrier with
              | register value => exact counter_stop _
              | pendingNamed pending =>
                  cases mismatch : (token != pending) with
                  | false => simp [mismatch]; exact counter_pure _
                  | true => simp [mismatch]; exact counter_stop _
              | completed replacement =>
                  change PreservesActivationCounter (completionLanding origin token replacement)
                  exact counter_completionLanding origin token replacement
    · intro _; exact counter_pure _

theorem counter_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : PreservesActivationCounter (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier with
  | register value => exact counter_pure _
  | pendingNamed token => exact counter_stop _
  | completed id =>
      apply counter_bind
      · exact counter_stateQuery _ (stateQuery_getDestination id)
      · intro destination
        simp only
        split
        · exact counter_lift _ _
        · split <;> split
          all_goals
            first
              | exact counter_lift _ _
              | (apply counter_bind
                 · exact counter_lift _ _
                 · intro _
                   apply counter_bind
                   · exact counter_stateQuery _ (stateQuery_receivingLayout layout destination.capability.layout)
                   · intro receiving
                     apply counter_bind
                     · exact counter_lift _ _
                     · intro _; exact counter_lift _ _)

theorem counter_finishChannels (layout : LayoutEnv) (channels : List Channel) (types : List Ty)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (finishChannels layout channels types carriers origin) := by
  unfold finishChannels
  apply counter_bind
  · exact counter_landCarriersInto origin channels carriers
  · intro _
    split
    · exact counter_stop _
    · apply counter_bind
      · apply counter_listForIn
        intro item _
        rcases item with ⟨carrier, result⟩
        apply counter_bind
        · exact counter_finishChannel layout origin carrier result
        · intro _; exact counter_pure _
      · intro _; exact counter_pure _

theorem counter_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation) (types : List Ty)
    (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (preserved : PreservesActivationCounter action) :
    PreservesActivationCounter (finishActivation layout activation types origin action) := by
  intro state
  have prior := preserved state
  cases result : action state with
  | ok carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    let trimmed : ExecutionState := { final with activations := final.activations.filter (fun current => current.act != activation.act) }
    have after := counter_finishChannels layout activation.channels types carriers origin trimmed
    cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
      simp only [finished, Goose.Proofs.Exit.stepState] at after <;>
      simpa [finishActivation, result, trimmed, finished, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
  | stop reason final => simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using prior
  | jump target kind final => simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using prior
  | escape target carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    by_cases caught : target.activation = activation.act
    · let trimmed : ExecutionState := { final with activations := final.activations.filter (fun current => current.act != activation.act) }
      have after := counter_finishChannels layout activation.channels types carriers origin trimmed
      cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
        simp only [finished, Goose.Proofs.Exit.stepState] at after <;>
        simpa [finishActivation, result, caught, trimmed, finished, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
    · simpa [finishActivation, result, caught, Goose.Proofs.Exit.stepState] using prior

#print axioms counter_finishActivation
theorem counter_cleanupDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesActivationCounter (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  apply counter_bind
  · exact counter_stateQuery _ (stateQuery_getDestination id)
  · intro destination
    split
    · exact counter_pure _
    · apply counter_bind
      · exact counter_get
      · intro state
        split
        · exact counter_lift _ _
        · split
          · exact counter_pure _
          · exact counter_lift _ _

theorem counter_cleanupReceivingDestination (origin : Goose.Core.OriginId)
    (incoming : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesActivationCounter (cleanupReceivingDestination origin incoming carriers) := by
  unfold cleanupReceivingDestination
  apply counter_bind
  · exact counter_lift _ _
  · intro current
    exact counter_cleanupDestination origin current carriers

#print axioms counter_cleanupReceivingDestination
theorem counter_protectDestination (origin : Goose.Core.OriginId) (destination : Goose.Core.DestinationId)
    (action : EvalM α) (preserved : PreservesActivationCounter action) :
    PreservesActivationCounter (protectDestination origin destination action) := by
  intro state
  have prior := preserved state
  cases result : action state with
  | ok value final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using prior
  | stop reason final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using prior
  | escape target carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    have after := counter_cleanupReceivingDestination origin destination carriers final
    cases cleaned : cleanupReceivingDestination origin destination carriers final <;>
      simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
      simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
  | jump target kind final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    cases kind with
    | breakValue carriers =>
      have after := counter_cleanupReceivingDestination origin destination carriers final
      cases cleaned : cleanupReceivingDestination origin destination carriers final <;>
        simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
        simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
    | continueLoop =>
      have after := counter_cleanupReceivingDestination origin destination [] final
      cases cleaned : cleanupReceivingDestination origin destination [] final <;>
        simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
        simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after

#print axioms counter_protectDestination
theorem counter_materializeProducer (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (preserved : PreservesActivationCounter evaluate) :
    PreservesActivationCounter (materializeProducer fuel declarations expression evaluate) := by
  unfold materializeProducer
  split
  · exact counter_pure _
  · apply counter_bind
    · exact preserved
    · intro value
      cases value <;> first | exact counter_pure _ | exact counter_stop _

theorem counter_materializedDestination (fuel : Nat) (layout : LayoutEnv)
    (owner : Goose.Core.ActId) (ty : Ty) (origin : Goose.Core.OriginId)
    (count : Nat) (value : Value) :
    PreservesActivationCounter (materializedDestination fuel layout owner ty origin count value) := by
  unfold materializedDestination
  apply counter_bind
  · exact counter_newDestination _ _ _ _ _ _ _
  · intro destination
    apply counter_bind
    · exact counter_copyValue _ _ _ _ _ _
    · intro ignored
      exact counter_completedReceivingDestination _

theorem counter_constructLocal (declarations : DeclarationEnv) (owner : Goose.Core.ActId) (ty : Ty)
    (origin : Goose.Core.OriginId) (expression : Expr) (construct : Goose.Core.DestinationId → EvalM Unit)
    (preserved : ∀ destination, PreservesActivationCounter (construct destination)) :
    PreservesActivationCounter (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply counter_bind
  · exact counter_newDestination _ _ _ _ _ _ _
  · intro destination
    apply counter_bind
    · exact preserved destination
    · intro _
      apply counter_bind
      · exact counter_completedReceivingDestination destination
      · intro completed
        apply counter_bind
        · exact counter_publishCarriers _ _
        · intro _; exact counter_pure _

structure EvaluationPreservesActivationCounter (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, PreservesActivationCounter (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, PreservesActivationCounter (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, PreservesActivationCounter (evalPlace fuel config environment operand)
  view : ∀ environment operand, PreservesActivationCounter (evalView fuel config environment operand)
  produce : ∀ environment channels operand, PreservesActivationCounter (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, PreservesActivationCounter (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, PreservesActivationCounter (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, PreservesActivationCounter (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, PreservesActivationCounter (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, PreservesActivationCounter (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, PreservesActivationCounter (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, PreservesActivationCounter (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, PreservesActivationCounter (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, PreservesActivationCounter (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, PreservesActivationCounter (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, PreservesActivationCounter (execStmts fuel config environment statements)
  statement : ∀ environment statement, PreservesActivationCounter (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, PreservesActivationCounter (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, PreservesActivationCounter (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, PreservesActivationCounter (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, PreservesActivationCounter (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, PreservesActivationCounter (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, PreservesActivationCounter (pushValue fuel config environment owner expression origin)


theorem evaluationCounter_zero (config : EvalConfig) : EvaluationPreservesActivationCounter 0 config := by
  constructor <;> intros <;>
    simp only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands, buildExpr, buildElement,
      evalArguments, invokeCall, enterActivation, execActivationBody, execResultBlock, execResultBlockWith,
      execBlock, execStmts, execStmt, evalPrintArg, execWhile, execRange, execEach, loopBody, pushValue,
      timeout, counter_stop]

theorem evalValue_not_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (expression : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.not expression)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment expression
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectBool value)
    · intro result
      exact counter_pure _

theorem evalValue_cmp_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.cmp operation first second)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment first
  · intro firstValue
    apply counter_bind
    · exact previous.value environment second
    · intro secondValue
      apply counter_bind
      · exact counter_stateQuery _ (stateQuery_comparable firstValue secondValue)
      · intro result
        exact counter_pure _

#print axioms evalValue_not_counter
#print axioms evalValue_cmp_counter
theorem evalValue_un_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.un operation expression origin)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment expression
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectInt value)
    · intro result
      cases result with
      | mk ty number =>
        cases Goose.Core.evalUn config.profile operation ty number with
        | ok value => exact counter_pure _
        | error reason => exact counter_abortAt (Goose.Core.AbortKind.ofNum reason) origin

theorem evalValue_bin_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.bin operation first second origin)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment first
  · intro firstValue
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectInt firstValue)
    · intro firstResult
      cases firstResult with
      | mk ty firstNumber =>
        apply counter_bind
        · exact previous.value environment second
        · intro secondValue
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_expectInt secondValue)
          · intro secondResult
            cases secondResult with
            | mk otherTy secondNumber =>
              apply counter_bind
              · exact counter_stateQuery _ (stateQuery_sameIntType ty otherTy)
              · intro ignored
                cases Goose.Core.evalBin config.profile operation ty firstNumber secondNumber with
                | ok value => exact counter_pure _
                | error reason => exact counter_abortAt (Goose.Core.AbortKind.ofNum reason) origin

theorem evalValue_conv_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.conv kind target expression origin)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment expression
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectInt value)
    · intro result
      cases result with
      | mk source number =>
        cases target with
        | int target =>
          simp only
          cases Goose.Core.evalConv config.profile kind source target number with
          | ok value => exact counter_pure _
          | error reason => exact counter_abortAt (Goose.Core.AbortKind.ofNum reason) origin
        | _ => exact counter_fault _

#print axioms evalValue_conv_counter
theorem evalValue_and_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.and first second)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment first
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectBool value)
    · intro condition
      cases condition with
      | false => exact counter_pure _
      | true =>
        apply counter_bind
        · exact previous.value environment second
        · intro value
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_expectBool value)
          · intro value
            exact counter_pure _

theorem evalValue_or_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.or first second)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment first
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectBool value)
    · intro condition
      cases condition with
      | true => exact counter_pure _
      | false =>
        apply counter_bind
        · exact previous.value environment second
        · intro value
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_expectBool value)
          · intro value
            exact counter_pure _

#print axioms evalValue_bin_counter
#print axioms evalValue_and_counter
theorem freshActs_distinct_across (action : EvalM α) (preserved : PreservesActivationCounter action)
    (before afterFirst afterAction afterSecond : ExecutionState) (first second : Goose.Core.ActId) (value : α)
    (firstStep : freshAct before = .ok first afterFirst)
    (actionStep : action afterFirst = .ok value afterAction)
    (secondStep : freshAct afterAction = .ok second afterSecond) : first < second := by
  have firstExact : freshAct before = .ok before.nextAct { before with nextAct := before.nextAct + 1 } := by rfl
  have secondExact : freshAct afterAction = .ok afterAction.nextAct { afterAction with nextAct := afterAction.nextAct + 1 } := by rfl
  have firstId : first = before.nextAct := (ExecutionStep.ok.inj (firstStep.symm.trans firstExact)).1
  have firstState : afterFirst = { before with nextAct := before.nextAct + 1 } :=
    (ExecutionStep.ok.inj (firstStep.symm.trans firstExact)).2
  have secondId : second = afterAction.nextAct := (ExecutionStep.ok.inj (secondStep.symm.trans secondExact)).1
  have monotone := preserved afterFirst
  simp only [actionStep, Goose.Proofs.Exit.stepState] at monotone
  rw [firstId, secondId]
  rw [firstState] at monotone
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) monotone

private def allocationWitness : EvalM (Goose.Core.ActId × Goose.Core.ActId) := do
  let first ← freshAct
  emitStdout ⟨#[65]⟩
  let second ← freshAct
  pure (first, second)

private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem allocationWitness_execution :
    ∃ state, allocationWitness .initial = .ok (0, 1) state ∧
      state.construction.stdout.data.toList = [65] := by
  refine ⟨witnessState (allocationWitness .initial), ?_, ?_⟩ <;>
    unfold allocationWitness witnessState <;> cbv

#print axioms allocationWitness_execution
#print axioms freshActs_distinct_across
#print axioms evaluationCounter_zero
#print axioms counter_bind
#print axioms counter_freshAct
#print axioms counter_lift
end Goose.Proofs.ConstructionActivationCounter
