import Goose.Construct.Eval
import Goose.Proofs.Exit
import Init.Data.List.Monadic
import Init.Data.Range.Lemmas

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

instance evalMLawfulMonad : LawfulMonad EvalM := LawfulMonad.mk'
  EvalM
  (id_map := fun action => by
    funext state
    change (match action state with
      | .ok value final => ExecutionStep.ok value final
      | .stop reason final => .stop reason final
      | .escape target carriers final => .escape target carriers final
      | .jump target kind final => .jump target kind final) = action state
    cases action state <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun action _ _ => by
    funext state
    simp only [bind]
    cases action state <;> rfl)

def FreshActivations (state : ExecutionState) : Prop :=
  (state.activations.map (·.act)).Nodup ∧
    ∀ activation ∈ state.activations, activation.act < state.nextAct

def PreservesFresh (action : EvalM α) : Prop :=
  ∀ state, FreshActivations state → FreshActivations (Goose.Proofs.Exit.stepState (action state))

def StateQuery (action : EvalM α) : Prop :=
  ∀ state, Goose.Proofs.Exit.stepState (action state) = state

private theorem preservesFresh_fault (kind : Goose.Core.FaultKind) :
    PreservesFresh (fault (α := α) kind) := by
  unfold fault EvalM.stop
  intro state fresh
  exact fresh

theorem stateQuery_preservesFresh (action : EvalM α) (query : StateQuery action) :
    PreservesFresh action := by
  intro state fresh
  rw [query state]
  exact fresh

theorem stateQuery_pure (value : α) : StateQuery (pure value) := by
  intro state
  rfl

theorem stateQuery_stop (reason : Goose.Core.Stop) : StateQuery (EvalM.stop (α := α) reason) := by
  intro state
  rfl

theorem stateQuery_get : StateQuery EvalM.get := by
  intro state
  rfl

theorem stateQuery_bind (action : EvalM α) (next : α → EvalM β)
    (first : StateQuery action) (remaining : ∀ value, StateQuery (next value)) :
    StateQuery (action >>= next) := by
  intro state
  have unchanged := first state
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at unchanged
      subst final
      simpa only [bind, result] using remaining value state
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using unchanged
  | escape target carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using unchanged
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using unchanged

theorem stateQuery_listMapM (action : α → EvalM β) (items : List α)
    (query : ∀ item, StateQuery (action item)) : StateQuery (items.mapM action) := by
  induction items with
  | nil => exact stateQuery_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply stateQuery_bind
      · exact query item
      · intro value
        apply stateQuery_bind
        · exact ih
        · intro values; exact stateQuery_pure _

theorem stateQuery_liftExcept (action : Except Goose.Core.Stop α) : StateQuery (liftExcept action) := by
  intro state
  cases action <;> rfl

theorem stateQuery_liftLayout (action : Except LayoutFault α) : StateQuery (liftLayout action) := by
  intro state
  cases action with
  | ok value => rfl
  | error kind => cases kind <;> rfl

theorem stateQuery_getDestination (destination : Goose.Core.DestinationId) :
    StateQuery (getDestination destination) := by
  intro state
  cases present : state.construction.destinations[destination]? <;>
    simp [getDestination, EvalM.get, bind, pure, fault, EvalM.stop, present, Goose.Proofs.Exit.stepState]

theorem stateQuery_getStorage (storage : Goose.Core.StorageId) : StateQuery (getStorage storage) := by
  intro state
  cases present : state.construction.storage[storage]? <;>
    simp [getStorage, EvalM.get, bind, pure, fault, EvalM.stop, present, Goose.Proofs.Exit.stepState]

theorem stateQuery_receivingDestination (incoming : Goose.Core.DestinationId) :
    StateQuery (receivingDestination incoming) := by
  intro state
  unfold receivingDestination liftConstruction
  cases current : destinationCurrent state.construction incoming <;>
    simp [current, Goose.Proofs.Exit.stepState]

theorem stateQuery_rootOf (activation : RuntimeActivation) (localVar : Goose.Core.VarId) :
    StateQuery (rootOf activation localVar) := by
  intro state
  cases present : activation.vars[localVar]? with
  | none => simp [rootOf, present, fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | some descriptor =>
      cases scopeFound : activation.scopes.find? (fun entry => entry.1 == descriptor.scope) <;>
        simp [rootOf, present, scopeFound, fault, EvalM.stop, pure, Goose.Proofs.Exit.stepState]

theorem stateQuery_exitSource (source : RuntimeActivation) (incoming : Goose.Core.DestinationId)
    (operand : Expr) : StateQuery (exitSource source incoming operand) := by
  unfold exitSource
  apply stateQuery_bind
  · exact stateQuery_receivingDestination incoming
  · intro selected
    cases operand with
    | resultLocal localVar _ =>
        apply stateQuery_bind
        · exact stateQuery_rootOf source localVar
        · intro root
          apply stateQuery_bind
          · exact stateQuery_get
          · intro state
            cases found : state.objects.lookup root with
            | none => simp [StateQuery, bind, pure, Goose.Proofs.Exit.stepState]
            | some value => cases value <;>
                simp [StateQuery, bind, pure, Goose.Proofs.Exit.stepState]
    | _ => exact stateQuery_pure _

theorem stateQuery_expectInt (value : Value) : StateQuery (expectInt value) := by
  intro state
  cases value <;> rfl

theorem stateQuery_expectBool (value : Value) : StateQuery (expectBool value) := by
  intro state
  cases value <;> rfl

theorem stateQuery_expectRef (value : Value) : StateQuery (expectRef value) := by
  intro state
  cases value <;> rfl

theorem stateQuery_receivingLayout (layout : LayoutEnv) (ty : Ty) : StateQuery (receivingLayout layout ty) := by
  cases ty with
  | limited element capacity =>
      simp only [receivingLayout]
      cases fixedByteSize? layout element <;> first | exact stateQuery_pure _ | exact stateQuery_stop _
  | int _ | bool | unit | ref _ _ | slice _ _ | tuple _ | structT _ _ => exact stateQuery_stop _
  | arr _ _ | varr _ | grow _ | growshrink _ => exact stateQuery_pure _

theorem stateQuery_storedDestination (id : Goose.Core.DestinationId) : StateQuery (storedDestination id) := by
  unfold storedDestination
  apply stateQuery_bind
  · exact stateQuery_getDestination id
  · intro destination
    cases progressCount destination.progress <;> first | exact stateQuery_pure _ | exact stateQuery_stop _

theorem stateQuery_sameIntType (first second : Goose.Core.IntTy) : StateQuery (sameIntType first second) := by
  unfold sameIntType
  split <;> first | exact stateQuery_pure _ | exact stateQuery_stop _

theorem stateQuery_comparable (first second : Value) : StateQuery (comparable first second) := by
  cases first <;> cases second <;> first
    | exact stateQuery_pure _
    | exact stateQuery_stop _
    | (apply stateQuery_bind
       · exact stateQuery_sameIntType _ _
       · intro _; exact stateQuery_pure _)

theorem stateQuery_sampledStored (stored : StoredValue) : StateQuery (sampledStored stored) := by
  unfold sampledStored
  apply stateQuery_bind
  · exact stateQuery_getStorage stored.storage
  · intro storage
    have finish : ∀ count : Nat, StateQuery (do
      let some element := elementType stored.ty | fault .shape
      let headerSize ← match stored.destination with
        | some id => do
            let destination ← getDestination id
            pure (if destination.layout == .packed && destination.capability.request == .value then 4 else 0)
        | none => pure (match stored.ty with | .varr _ => 4 | _ => 0)
      pure (storage.bytes, SampledRun.mk (stored.start + headerSize) count element)) := by
      intro count
      cases elementFound : elementType stored.ty with
      | none => exact stateQuery_stop _
      | some element =>
          cases stored.destination with
          | none =>
              apply stateQuery_bind
              · exact stateQuery_pure _
              · intro headerSize; exact stateQuery_pure _
          | some id =>
              apply stateQuery_bind
              · exact stateQuery_getDestination id
              · intro destination
                apply stateQuery_bind
                · exact stateQuery_pure _
                · intro headerSize; exact stateQuery_pure _
    dsimp only
    cases destinationFound : stored.destination with
    | none =>
        simp only [destinationFound] at finish
        apply stateQuery_bind
        · exact stateQuery_pure _
        · exact finish
    | some id =>
        simp only [destinationFound] at finish
        apply stateQuery_bind
        · exact stateQuery_getDestination id
        · intro destination
          cases destination.progress <;> simp only [progressCount]
          all_goals first
            | (apply stateQuery_bind
               · exact stateQuery_pure _
               · exact finish)
            | (apply stateQuery_bind
               · exact stateQuery_stop _
               · exact finish)
            | (apply stateQuery_bind
               · exact stateQuery_getStorage stored.storage
               · intro receiving
                 apply stateQuery_bind
                 · exact stateQuery_pure _
                 · exact finish)

theorem stateQuery_storedPathRun (stored : StoredValue) : StateQuery (storedPathRun stored) := by
  unfold storedPathRun
  apply stateQuery_bind
  · exact stateQuery_sampledStored stored
  · intro sampled
    exact stateQuery_pure _

theorem stateQuery_readStoredElement (fuel : Nat) (layout : LayoutEnv)
    (stored : StoredValue) (index : Nat) : StateQuery (readStoredElement fuel layout stored index) := by
  unfold readStoredElement
  apply stateQuery_bind
  · exact stateQuery_storedPathRun stored
  · intro sampled
    rcases sampled with ⟨bytes, run⟩
    simp only
    apply stateQuery_bind
    · exact stateQuery_liftLayout _
    · intro interval
      rcases interval with ⟨start, finish⟩
      simp only
      split
      · apply stateQuery_bind
        · exact stateQuery_liftLayout _
        · intro run; exact stateQuery_pure _
      · exact stateQuery_liftExcept _

theorem stateQuery_readValuePath (fuel : Nat) (layout : LayoutEnv)
    (value : Value) (path : List Nat) : StateQuery (readValuePath fuel layout value path) := by
  induction fuel generalizing value path with
  | zero => exact stateQuery_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact stateQuery_pure _
      | cons index rest =>
          cases value with
          | fixed elements | record id elements =>
              simp only [readValuePath]
              cases present : elements[index]? <;> apply stateQuery_bind
              all_goals first
                | exact stateQuery_pure _
                | exact stateQuery_stop _
                | (intro child; exact ih child rest)
          | stored stored =>
              unfold readValuePath
              apply stateQuery_bind
              · exact stateQuery_readStoredElement fuel layout stored index
              · intro child; exact ih child rest
          | int _ _ | bool _ | unit | ref _ | slice _ _ _ =>
              unfold readValuePath
              apply stateQuery_bind
              · exact stateQuery_stop _
              · intro child; exact ih child rest

theorem stateQuery_readLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc) :
    StateQuery (readLoc fuel layout location) := by
  unfold readLoc
  apply stateQuery_bind
  · exact stateQuery_get
  · intro state
    cases present : state.objects.lookup location.root with
    | none => exact stateQuery_stop _
    | some value => exact stateQuery_readValuePath fuel layout value location.path

theorem stateQuery_arrayLength (value : Value) : StateQuery (arrayLength value) := by
  cases value with
  | fixed values => exact stateQuery_pure _
  | stored stored =>
      unfold arrayLength
      apply stateQuery_bind
      · exact stateQuery_sampledStored stored
      · intro sampled
        rcases sampled with ⟨bytes, run⟩
        exact stateQuery_pure _
  | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ => exact stateQuery_stop _

theorem stateQuery_readRun (fuel : Nat) (layout : LayoutEnv) (view : RuntimeView) :
    StateQuery (readRun fuel layout view) := by
  unfold readRun
  apply stateQuery_listMapM
  intro index
  exact stateQuery_readLoc fuel layout _

theorem stateQuery_renderValue (value : Value) : StateQuery (renderValue value) := by
  cases value with
  | int _ _ => exact stateQuery_pure _
  | bool value => cases value <;> exact stateQuery_pure _
  | unit | fixed _ | record _ _ | ref _ | slice _ _ _ | stored _ => exact stateQuery_stop _

theorem rendering_stateQueries (fuel : Nat) (layout : LayoutEnv) :
    (∀ position value, StateQuery (renderAny fuel layout position value)) ∧
    (∀ values, StateQuery (renderElements fuel layout values)) ∧
    (∀ position stored, StateQuery (renderStored fuel layout position stored)) ∧
    (∀ position view, StateQuery (renderView fuel layout position view)) := by
  induction fuel with
  | zero => exact ⟨fun _ _ => stateQuery_stop _, fun _ => stateQuery_stop _,
      fun _ _ => stateQuery_stop _, fun _ _ => stateQuery_stop _⟩
  | succ fuel ih =>
      obtain ⟨anyQuery, elementsQuery, storedQuery, viewQuery⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro position value
        cases value with
        | int ty value => simpa only [renderAny] using stateQuery_renderValue (Value.int ty value)
        | bool value => simpa only [renderAny] using stateQuery_renderValue (Value.bool value)
        | unit => simpa only [renderAny] using stateQuery_pure "()".toUTF8
        | ref location =>
            simp only [renderAny]
            apply stateQuery_bind
            · exact stateQuery_readLoc fuel layout location
            · intro value; exact anyQuery position value
        | slice location start count => simpa only [renderAny] using viewQuery position ⟨location, start, count, false⟩
        | stored value => simpa only [renderAny] using storedQuery position value
        | fixed values =>
            simp only [renderAny]
            split
            · apply stateQuery_bind
              · apply stateQuery_listMapM
                intro value
                apply stateQuery_bind
                · exact stateQuery_expectInt value
                · intro scalar
                  rcases scalar with ⟨ty, byte⟩
                  exact stateQuery_pure _
              · intro bytes; exact stateQuery_pure _
            · exact elementsQuery values.toList
        | record id fields =>
            simp only [renderAny]
            cases present : layout.structs[id]? with
            | none => exact stateQuery_stop _
            | some descriptor =>
                simp only
                split
                · exact stateQuery_stop _
                · apply stateQuery_bind
                  · exact stateQuery_listMapM _ fields.toList (anyQuery .aggregatePart)
                  · intro parts; exact stateQuery_pure _
      · intro values
        unfold renderElements
        apply stateQuery_bind
        · exact stateQuery_listMapM _ values (anyQuery .aggregatePart)
        · intro parts; exact stateQuery_pure _
      · intro position stored
        unfold renderStored
        apply stateQuery_bind
        · exact stateQuery_sampledStored stored
        · intro sampled
          rcases sampled with ⟨bytes, run⟩
          simp only
          split
          · apply stateQuery_bind
            · exact stateQuery_liftLayout _
            · intro interval
              rcases interval with ⟨start, finish⟩
              exact stateQuery_pure _
          · apply stateQuery_bind
            · apply stateQuery_listMapM
              intro index
              exact stateQuery_readStoredElement fuel layout stored index
            · intro values; exact elementsQuery values
      · intro position view
        unfold renderView
        apply stateQuery_bind
        · exact stateQuery_readLoc fuel layout view.location
        · intro value
          have continued : ∀ rawBytes : Bool, StateQuery (do
            let values ← readRun fuel layout view
            if rawBytes then
              let bytes ← values.mapM fun value => do
                let (ty, byte) ← expectInt value
                if ty != .u8 then fault .shape
                pure (UInt8.ofNat byte.toNat)
              let bytes : ByteArray := ⟨bytes.toArray⟩
              pure (if position == .aggregatePart then quoteBytes bytes else bytes)
            else renderElements fuel layout values) := by
            intro rawBytes
            apply stateQuery_bind
            · exact stateQuery_readRun fuel layout view
            · intro values
              split
              · apply stateQuery_bind
                · apply stateQuery_listMapM
                  intro value
                  apply stateQuery_bind
                  · exact stateQuery_expectInt value
                  · intro scalar
                    rcases scalar with ⟨ty, byte⟩
                    simp only
                    split
                    · exact stateQuery_stop _
                    · exact stateQuery_pure _
                · intro bytes; exact stateQuery_pure _
              · exact elementsQuery values
          cases value with
          | stored stored =>
              apply stateQuery_bind
              · exact stateQuery_sampledStored stored
              · intro sampled
                apply stateQuery_bind
                · exact stateQuery_pure _
                · exact continued
          | fixed values =>
              apply stateQuery_bind
              · exact stateQuery_pure _
              · exact continued
          | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ =>
              apply stateQuery_bind
              · exact stateQuery_stop _
              · exact continued

theorem preservesFresh_pure (value : α) : PreservesFresh (pure value) := by
  intro state fresh
  exact fresh

theorem preservesFresh_stop (reason : Goose.Core.Stop) :
    PreservesFresh (EvalM.stop (α := α) reason) := by
  intro state fresh
  exact fresh

theorem preservesFresh_get : PreservesFresh EvalM.get := by
  intro state fresh
  exact fresh

theorem preservesFresh_get_bind (next : ExecutionState → EvalM α)
    (preserved : ∀ state, FreshActivations state →
      FreshActivations (Goose.Proofs.Exit.stepState (next state state))) :
    PreservesFresh (EvalM.get >>= next) := preserved

theorem preservesFresh_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesFresh action) (remaining : ∀ value, PreservesFresh (next value)) :
    PreservesFresh (action >>= next) := by
  intro state fresh
  have preserved := first state fresh
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at preserved
      simpa only [bind, result] using remaining value final preserved
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | escape target carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved

theorem preservesFresh_listMapM (action : α → EvalM β) (items : List α)
    (preserved : ∀ item, PreservesFresh (action item)) : PreservesFresh (items.mapM action) := by
  induction items with
  | nil => exact preservesFresh_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply preservesFresh_bind
      · exact preserved item
      · intro value
        apply preservesFresh_bind
        · exact ih
        · intro values; exact preservesFresh_pure _

theorem preservesFresh_listForIn (action : α → β → EvalM (ForInStep β)) (items : List α)
    (initial : β) (preserved : ∀ item value, PreservesFresh (action item value)) :
    PreservesFresh (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact preservesFresh_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply preservesFresh_bind
      · exact preserved item initial
      · intro step
        cases step with
        | done value => exact preservesFresh_pure _
        | yield value => exact ih value

theorem preservesFresh_arrayForIn (action : α → β → EvalM (ForInStep β)) (items : Array α)
    (initial : β) (preserved : ∀ item value, PreservesFresh (action item value)) :
    PreservesFresh (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact preservesFresh_listForIn action items.toList initial preserved

theorem preservesFresh_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (preserved : ∀ index value, PreservesFresh (action index value)) :
    PreservesFresh (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact preservesFresh_listForIn action _ initial preserved

theorem preservesFresh_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    PreservesFresh (liftConstruction origin action) := by
  intro state fresh
  unfold liftConstruction
  cases action state.construction <;> exact fresh

private theorem preservesFresh_activationFrame (action : EvalM α)
    (frame : ∀ state,
      (Goose.Proofs.Exit.stepState (action state)).activations = state.activations ∧
      (Goose.Proofs.Exit.stepState (action state)).nextAct = state.nextAct) :
    PreservesFresh action := by
  intro state fresh
  obtain ⟨activations, nextAct⟩ := frame state
  unfold FreshActivations at *
  rw [activations, nextAct]
  exact fresh

private theorem preservesFresh_constructionUpdate (update : ExecutionState → ConstructionState) :
    PreservesFresh (fun state => EvalM.set { state with construction := update state } state) := by
  intro state fresh
  change FreshActivations
    (Goose.Proofs.Exit.stepState (EvalM.set { state with construction := update state } state))
  simpa [EvalM.set, Goose.Proofs.Exit.stepState, FreshActivations] using fresh

theorem preservesFresh_restoreCompletedOwner (snapshot : PendingDestination) (incoming : Goose.Core.DestinationId)
    (carried : List Goose.Core.DestinationId) :
    PreservesFresh (restoreCompletedOwner snapshot incoming carried) := by
  unfold restoreCompletedOwner
  cases snapshot.progress with
  | built originalCount =>
      apply preservesFresh_bind
      · exact preservesFresh_lift 0 _
      · intro current
        apply preservesFresh_bind
        · exact preservesFresh_get
        · intro state
          cases retained : carried.any (fun id =>
              (state.construction.destinations[id]?).any fun row =>
                (match row.progress with | .built _ => true | _ => false) &&
                  descendsFrom state.construction id current) with
          | true =>
            dsimp only
            exact preservesFresh_pure _
          | false =>
            dsimp only
            apply preservesFresh_bind
            · exact stateQuery_preservesFresh _ (stateQuery_getDestination current)
            · intro child
              apply preservesFresh_bind
              · exact stateQuery_preservesFresh _ (stateQuery_getDestination snapshot.capability.id)
              · intro parent
                cases parent.progress with
                | suspended count expected =>
                    cases child.progress with
                    | abandoned | cancelled =>
                        cases countInvalid : (count != originalCount) with
                        | true => simp [countInvalid]; exact preservesFresh_fault .flow
                        | false =>
                          cases ownerInvalid : (expected != current) with
                          | true => simp [countInvalid, ownerInvalid]; exact preservesFresh_fault .flow
                          | false =>
                            cases childInvalid : (child.use != .child snapshot.capability.id) with
                            | true =>
                                simp [countInvalid, ownerInvalid]
                                exact preservesFresh_fault .flow
                            | false =>
                              cases parentInvalid :
                                  ({ parent with progress := .built originalCount } != snapshot) with
                              | true =>
                                  simp [countInvalid, ownerInvalid]
                                  exact preservesFresh_fault .flow
                              | false =>
                                simp [countInvalid, ownerInvalid]
                                intro currentState fresh
                                simpa [EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState,
                                  FreshActivations] using fresh
                    | _ => exact preservesFresh_pure _
                | _ => exact preservesFresh_pure _
  | _ => exact preservesFresh_stop _

private def completedCarrierIds (carriers : List Carrier) : List Goose.Core.DestinationId :=
  carriers.filterMap fun (carrier : Carrier) => match carrier with
    | .completed id => some id
    | _ => none

private theorem preservesFresh_ownerExtensionGuarded (snapshot : Option PendingDestination)
    (destination : Goose.Core.DestinationId) (action : Goose.Core.DestinationId → EvalM α)
    (actionFresh : PreservesFresh (action destination))
    (restoreFresh : ∀ parent carried,
      PreservesFresh (restoreCompletedOwner parent destination carried)) :
    PreservesFresh (fun state =>
      let finish := fun (carriers : List Carrier)
          (result : ExecutionState → ExecutionStep α) (state' : ExecutionState) =>
        match snapshot with
        | none => result state'
        | some parent =>
            match restoreCompletedOwner parent destination (completedCarrierIds carriers) state' with
            | .ok () final => result final
            | .stop reason final => .stop reason final
            | .escape target carriers final => .escape target carriers final
            | .jump target kind final => .jump target kind final
      match action destination state with
      | .escape target carriers state' => finish carriers (.escape target carriers) state'
      | .jump target kind state' =>
          finish (match kind with | .breakValue carriers => carriers | .continueLoop => [])
            (.jump target kind) state'
      | result => result) := by
  intro state fresh
  dsimp only
  cases result : action destination state with
  | ok value final =>
      have after := actionFresh state fresh
      simpa [result, Goose.Proofs.Exit.stepState] using after
  | stop reason final =>
      have after := actionFresh state fresh
      simpa [result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      have after := actionFresh state fresh
      have finalFresh : FreshActivations final := by
        simpa only [result, Goose.Proofs.Exit.stepState] using after
      cases snapshot with
      | none => exact finalFresh
      | some parent =>
          have restoredFresh := restoreFresh parent (completedCarrierIds carriers) final finalFresh
          cases restored : restoreCompletedOwner parent destination
              (carriers.filterMap fun (carrier : Carrier) => match carrier with | .completed id => some id | _ => none) final with
          | ok _ cleaned =>
              have cleanedFresh : FreshActivations cleaned := by
                simpa [completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using restoredFresh
              simpa [result, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using cleanedFresh
          | stop _ cleaned =>
              have cleanedFresh : FreshActivations cleaned := by
                simpa [completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using restoredFresh
              simpa [result, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using cleanedFresh
          | escape _ _ cleaned =>
              have cleanedFresh : FreshActivations cleaned := by
                simpa [completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using restoredFresh
              simpa [result, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using cleanedFresh
          | jump _ _ cleaned =>
              have cleanedFresh : FreshActivations cleaned := by
                simpa [completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using restoredFresh
              simpa [result, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using cleanedFresh
  | jump target kind final =>
      have after := actionFresh state fresh
      have finalFresh : FreshActivations final := by
        simpa only [result, Goose.Proofs.Exit.stepState] using after
      cases snapshot with
      | none => exact finalFresh
      | some parent =>
          let carriers := match kind with | .breakValue carriers => carriers | .continueLoop => []
          have restoredFresh := restoreFresh parent (completedCarrierIds carriers) final finalFresh
          cases restored : restoreCompletedOwner parent destination
              ((match kind with | .breakValue values => values | .continueLoop => []).filterMap
                fun (carrier : Carrier) => match carrier with | .completed id => some id | _ => none) final with
          | ok _ cleaned =>
              have cleanedFresh : FreshActivations cleaned := by
                simpa [carriers, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using restoredFresh
              simpa [result, carriers, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using cleanedFresh
          | stop _ cleaned =>
              have cleanedFresh : FreshActivations cleaned := by
                simpa [carriers, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using restoredFresh
              simpa [result, carriers, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using cleanedFresh
          | escape _ _ cleaned =>
              have cleanedFresh : FreshActivations cleaned := by
                simpa [carriers, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using restoredFresh
              simpa [result, carriers, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using cleanedFresh
          | jump _ _ cleaned =>
              have cleanedFresh : FreshActivations cleaned := by
                simpa [carriers, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using restoredFresh
              simpa [result, carriers, completedCarrierIds, restored, Goose.Proofs.Exit.stepState] using cleanedFresh

theorem preservesFresh_withOwnerExtension (stored : StoredValue) (allocate : EvalM Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → EvalM α) (allocateFresh : PreservesFresh allocate)
    (actionFresh : ∀ destination, PreservesFresh (action destination)) :
    PreservesFresh (withOwnerExtension stored allocate action) := by
  unfold withOwnerExtension
  cases stored.destination with
  | none =>
    simp only [bind, pure]
    apply preservesFresh_bind
    · exact allocateFresh
    · intro destination
      exact preservesFresh_ownerExtensionGuarded none destination action (actionFresh destination)
        (fun parent carried => preservesFresh_restoreCompletedOwner parent destination carried)
  | some id =>
    simp only [bind, pure]
    apply preservesFresh_bind
    · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
    · intro parent
      apply preservesFresh_bind
      · exact allocateFresh
      · intro destination
        exact preservesFresh_ownerExtensionGuarded
          (match parent.progress with | .built _ => some parent | _ => none)
          destination action (actionFresh destination)
          (fun parent carried => preservesFresh_restoreCompletedOwner parent destination carried)


theorem preservesFresh_receivingAction (origin : Goose.Core.OriginId)
    (incoming : Goose.Core.DestinationId) (action : Goose.Core.DestinationId → ConstructionM α) :
    PreservesFresh (receivingAction origin incoming action) := by
  unfold receivingAction
  exact preservesFresh_lift _ _

theorem preservesFresh_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    PreservesFresh (setObjectOrdinal root ordinal) := by
  intro state fresh
  exact fresh

theorem preservesFresh_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesFresh (bindStaticRoot root value) := by
  intro state fresh
  exact fresh

theorem preservesFresh_reserveRootObject (root : Goose.Core.RootInst) : PreservesFresh (reserveRootObject root) := by
  unfold reserveRootObject
  apply preservesFresh_bind
  · exact preservesFresh_get
  · intro state
    cases state.objectOrdinals.lookup root with
    | some ordinal => exact preservesFresh_pure _
    | none =>
        apply preservesFresh_bind
        · exact preservesFresh_lift _ _
        · intro ordinal
          apply preservesFresh_bind
          · exact preservesFresh_setObjectOrdinal root ordinal
          · intro _; exact preservesFresh_pure _

theorem preservesFresh_bindRoot (root : Goose.Core.RootInst) (value : Value) : PreservesFresh (bindRoot root value) := by
  unfold bindRoot
  apply preservesFresh_bind
  · exact preservesFresh_get
  · intro state
    split
    · cases value <;> apply preservesFresh_bind
      all_goals first
        | exact preservesFresh_setObjectOrdinal _ _
        | exact preservesFresh_reserveRootObject _
        | (intro _
           apply preservesFresh_bind
           · exact preservesFresh_pure _
           · intro _; exact preservesFresh_bindStaticRoot root _)
        | (intro _; exact preservesFresh_bindStaticRoot root _)
    · exact preservesFresh_bindStaticRoot root value

theorem preservesFresh_writeValuePath (fuel : Nat) (layout : LayoutEnv)
    (value : Value) (path : List Nat) (replacement : Value) :
    PreservesFresh (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path replacement with
  | zero => exact preservesFresh_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact preservesFresh_pure _
      | cons index rest =>
          cases value with
          | fixed elements | record id elements =>
              simp only [writeValuePath]
              cases present : elements[index]? with
              | none => exact preservesFresh_stop _
              | some child =>
                  apply preservesFresh_bind
                  · exact ih child rest replacement
                  · intro written; exact preservesFresh_pure _
          | int _ _ | bool _ | unit | ref _ | slice _ _ _ => exact preservesFresh_stop _
          | stored stored =>
              unfold writeValuePath
              apply preservesFresh_bind
              · exact stateQuery_preservesFresh _ (stateQuery_storedPathRun stored)
              · intro sampled
                rcases sampled with ⟨bytes, run⟩
                simp only
                apply preservesFresh_bind
                · exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
                · intro interval
                  rcases interval with ⟨start, finish⟩
                  simp only
                  apply preservesFresh_bind
                  · exact stateQuery_preservesFresh _ (stateQuery_readStoredElement fuel layout stored index)
                  · intro child
                    split
                    · split
                      · exact preservesFresh_stop _
                      · apply preservesFresh_bind
                        · exact ih child rest replacement
                        · intro _; exact preservesFresh_pure _
                    · apply preservesFresh_bind
                      · exact ih child rest replacement
                      · intro written
                        apply preservesFresh_bind
                        · exact stateQuery_preservesFresh _ (stateQuery_liftExcept _)
                        · intro part
                          split
                          · exact preservesFresh_stop _
                          · apply preservesFresh_get_bind
                            intro state fresh
                            cases present : state.construction.storage[stored.storage]? with
                            | none => exact fresh
                            | some receiving => exact fresh

theorem preservesFresh_writeLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (replacement : Value) : PreservesFresh (writeLoc fuel layout location replacement) := by
  unfold writeLoc
  apply preservesFresh_bind
  · exact preservesFresh_get
  · intro state
    cases present : state.objects.lookup location.root with
    | none => exact preservesFresh_stop _
    | some value =>
        apply preservesFresh_bind
        · exact preservesFresh_writeValuePath fuel layout value location.path replacement
        · intro written; exact preservesFresh_bindRoot location.root written

theorem preservesFresh_bindAll (act : Goose.Core.ActId) (scopeInst : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : PreservesFresh (bindAll act scopeInst values) := by
  unfold bindAll
  apply preservesFresh_bind
  · apply preservesFresh_listForIn
    intro item _
    rcases item with ⟨localVar, value⟩
    apply preservesFresh_bind
    · exact preservesFresh_bindRoot _ value
    · intro _; exact preservesFresh_pure _
  · intro _; exact preservesFresh_pure _

theorem preservesFresh_newDestination (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    PreservesFresh (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  cases storage with
  | none =>
      apply preservesFresh_bind
      · exact preservesFresh_lift _ _
      · intro storage
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_receivingLayout layout ty)
        · intro receiving; exact preservesFresh_lift _ _
  | some storage =>
      apply preservesFresh_bind
      · exact preservesFresh_pure _
      · intro storage
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_receivingLayout layout ty)
        · intro receiving; exact preservesFresh_lift _ _

theorem preservesFresh_channelsFor (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    PreservesFresh (channelsFor layout owner results origin) := by
  unfold channelsFor
  apply preservesFresh_listMapM
  intro descriptor
  cases descriptor.request with
  | register => exact preservesFresh_pure _
  | value | elementRun =>
      apply preservesFresh_bind
      · exact preservesFresh_newDestination _ _ _ _ _ _ _
      · intro destination; exact preservesFresh_pure _

theorem stateQuery_completedDestination (id : Goose.Core.DestinationId) : StateQuery (completedDestination id) := by
  unfold completedDestination
  apply stateQuery_bind
  · exact stateQuery_getDestination id
  · intro destination
    cases destination.progress <;> first
      | exact stateQuery_pure _
      | exact stateQuery_stop _

theorem preservesFresh_completedReceivingDestination (id : Goose.Core.DestinationId) :
    PreservesFresh (completedReceivingDestination id) := by
  unfold completedReceivingDestination
  apply preservesFresh_bind
  · exact preservesFresh_lift _ _
  · intro current
    exact stateQuery_preservesFresh _ (stateQuery_completedDestination current)

theorem stateQuery_carrierValue (carrier : Carrier) : StateQuery (carrierValue carrier) := by
  cases carrier with
  | register value => exact stateQuery_pure _
  | completed id =>
      unfold carrierValue
      apply stateQuery_bind
      · exact stateQuery_storedDestination id
      · intro stored; exact stateQuery_pure _
  | pendingNamed token => exact stateQuery_stop _

theorem stateQuery_singleCarrier (carriers : List Carrier) : StateQuery (singleCarrier carriers) := by
  unfold singleCarrier
  split <;> first | exact stateQuery_pure _ | exact stateQuery_stop _

theorem preservesFresh_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesFresh (publishCarriers origin carriers) := by
  unfold publishCarriers
  apply preservesFresh_bind
  · apply stateQuery_preservesFresh
    apply stateQuery_listMapM
    intro carrier
    cases carrier with
    | register value => exact stateQuery_pure _
    | completed id => exact stateQuery_pure _
    | pendingNamed token => exact stateQuery_stop _
  · intro ids
    exact preservesFresh_lift _ _

theorem preservesFresh_materializeNamedCarriers (origin : Goose.Core.OriginId)
    (carriers : List Carrier) :
    PreservesFresh (materializeNamedCarriers origin carriers) := by
  unfold materializeNamedCarriers
  apply preservesFresh_listMapM
  intro carrier
  cases carrier with
  | register value => exact preservesFresh_pure _
  | completed id => exact preservesFresh_pure _
  | pendingNamed token =>
      apply preservesFresh_bind
      · exact preservesFresh_lift _ _
      · intro id; exact preservesFresh_pure _

theorem preservesFresh_materializeOwnedCarriers (origin : Goose.Core.OriginId)
    (tokens : List ExitReservationId) (carriers : List Carrier) :
    PreservesFresh (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  apply preservesFresh_listMapM
  intro carrier
  cases carrier with
  | register value => exact preservesFresh_pure _
  | completed id => exact preservesFresh_pure _
  | pendingNamed token =>
      by_cases owns : tokens.contains token = true
      · simp only [owns]
        apply preservesFresh_bind
        · exact preservesFresh_lift _ _
        · intro id; exact preservesFresh_pure _
      · simp only [owns]
        exact preservesFresh_pure _

theorem preservesFresh_ownerDestination (layout : LayoutEnv) (stored : StoredValue)
    (request : Goose.Core.ConstructionRequest) (count : Option Nat) (origin : Goose.Core.OriginId) :
    PreservesFresh (ownerDestination layout stored request count origin) := by
  unfold ownerDestination
  cases stored.destination with
  | none => exact preservesFresh_newDestination _ _ _ _ _ _ _
  | some id =>
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
      · intro destination
        cases destination.progress <;> first
          | exact preservesFresh_lift _ _
          | exact preservesFresh_newDestination _ _ _ _ _ _ _
          | exact preservesFresh_stop _

theorem preservesFresh_publishOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    PreservesFresh (publishOwner fuel layout location stored id origin) := by
  cases fuel with
  | zero => exact preservesFresh_stop _
  | succ fuel =>
      unfold publishOwner
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => exact preservesFresh_stop _
        | child parent =>
            apply preservesFresh_bind
            · exact preservesFresh_lift _ _
            · intro _
              apply preservesFresh_bind
              · exact stateQuery_preservesFresh _ (stateQuery_storedDestination parent)
              · intro value; exact preservesFresh_writeLoc fuel layout location _
        | receiver =>
            apply preservesFresh_bind
            · exact preservesFresh_publishCarriers _ _
            · intro _
              apply preservesFresh_bind
              · exact stateQuery_preservesFresh _ (stateQuery_getStorage stored.storage)
              · intro receiving; exact preservesFresh_writeLoc fuel layout location _

theorem preservesFresh_repeatElement (fuel : Nat) (layout : LayoutEnv) (parent : Goose.Core.DestinationId)
    (element : Ty) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    PreservesFresh (repeatElement fuel layout parent element source origin) := by
  cases fuel with
  | zero => exact preservesFresh_stop _
  | succ fuel =>
      unfold repeatElement
      apply preservesFresh_bind
      · exact preservesFresh_lift _ _
      · intro current
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_storedDestination source)
        · intro stored
          apply preservesFresh_bind
          · exact stateQuery_preservesFresh _ (stateQuery_getStorage stored.storage)
          · intro storage
            apply preservesFresh_bind
            · exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
            · intro finish
              apply preservesFresh_bind
              · exact preservesFresh_lift _ _
              · intro _; exact preservesFresh_lift _ _

theorem fixed_writes_preserveFresh (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (element : Ty) (origin : Goose.Core.OriginId) (values : Array Value) :
    PreservesFresh (forIn values PUnit.unit fun value _ => do
      let bytes ← liftExcept (fixedBytes fuel layout element value)
      liftConstruction origin (writeElement destination bytes)
      pure (.yield PUnit.unit)) := by
  apply preservesFresh_arrayForIn
  intro value _
  apply preservesFresh_bind
  · exact stateQuery_preservesFresh _ (stateQuery_liftExcept _)
  · intro bytes
    apply preservesFresh_bind
    · exact preservesFresh_lift _ _
    · intro _; exact preservesFresh_pure _

theorem packed_writes_preserveFresh (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (bytes : ByteArray) (run : SampledRun) (start count : Nat) (origin : Goose.Core.OriginId) :
    PreservesFresh (forIn ([0:count] : Std.Legacy.Range) PUnit.unit fun index _ => do
      let (low, high) ← liftLayout (elementInterval fuel layout bytes run (start + index))
      liftConstruction origin (writeElement destination (bytes.extract low high))
      pure (.yield PUnit.unit)) := by
  apply preservesFresh_rangeForIn
  intro index _
  apply preservesFresh_bind
  · exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
  · intro interval
    rcases interval with ⟨low, high⟩
    simp only
    apply preservesFresh_bind
    · exact preservesFresh_lift _ _
    · intro _; exact preservesFresh_pure _

theorem preservesFresh_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    PreservesFresh (copyValue fuel layout destination value origin source) := by
  cases fuel with
  | zero => exact preservesFresh_stop _
  | succ fuel =>
      unfold copyValue
      apply preservesFresh_bind
      · exact preservesFresh_lift _ _
      · intro current
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_getDestination current)
        · intro pending
          cases elementFound : elementType pending.capability.logicalType with
          | none => exact preservesFresh_stop _
          | some element =>
              cases value with
              | int _ _ | bool _ | unit | record _ _ | ref _ => exact preservesFresh_stop _
              | stored stored =>
                  apply preservesFresh_bind
                  · exact stateQuery_preservesFresh _ (stateQuery_sampledStored stored)
                  · intro sampled
                    rcases sampled with ⟨bytes, run⟩
                    simp only
                    split
                    · exact preservesFresh_stop _
                    · apply preservesFresh_bind
                      · exact preservesFresh_lift _ _
                      · intro _
                        apply preservesFresh_bind
                        · simpa only [Nat.zero_add] using packed_writes_preserveFresh fuel layout current bytes run 0 run.count origin
                        · intro _; exact preservesFresh_lift _ _
              | fixed values =>
                  cases source with
                  | none =>
                      apply preservesFresh_bind
                      · exact fixed_writes_preserveFresh fuel layout current element origin values
                      · intro _; exact preservesFresh_lift _ _
                  | some source =>
                      apply preservesFresh_bind
                      · exact preservesFresh_lift _ _
                      · intro _
                        apply preservesFresh_bind
                        · exact fixed_writes_preserveFresh fuel layout current element origin values
                        · intro _; exact preservesFresh_lift _ _
              | slice location start count =>
                  apply preservesFresh_bind
                  · exact stateQuery_preservesFresh _ (stateQuery_readLoc fuel layout location)
                  · intro backing
                    cases source with
                    | none => exact preservesFresh_stop _
                    | some source =>
                        cases backing with
                        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ => exact preservesFresh_stop _
                        | stored stored =>
                            apply preservesFresh_bind
                            · exact stateQuery_preservesFresh _ (stateQuery_storedPathRun stored)
                            · intro sampled
                              rcases sampled with ⟨bytes, run⟩
                              simp only
                              split
                              · exact preservesFresh_stop _
                              · split
                                · exact preservesFresh_stop _
                                · apply preservesFresh_bind
                                  · exact preservesFresh_lift _ _
                                  · intro _
                                    apply preservesFresh_bind
                                    · exact packed_writes_preserveFresh fuel layout current bytes run start count origin
                                    · intro _; exact preservesFresh_lift _ _
                        | fixed values =>
                            simp only
                            split
                            · exact preservesFresh_stop _
                            · apply preservesFresh_bind
                              · exact preservesFresh_lift _ _
                              · intro _
                                apply preservesFresh_bind
                                · exact fixed_writes_preserveFresh fuel layout current element origin (values.extract start (start + count))
                                · intro _; exact preservesFresh_lift _ _

theorem preservesFresh_deliverCarriers (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesFresh (deliverCarriers fuel layout channels carriers origin) := by
  unfold deliverCarriers
  split
  · exact preservesFresh_stop _
  · apply preservesFresh_listMapM
    intro item
    rcases item with ⟨channel, carrier⟩
    cases channel <;> cases carrier <;> first
      | exact preservesFresh_pure _
      | exact preservesFresh_stop _
      | (apply preservesFresh_bind
         · exact preservesFresh_copyValue _ _ _ _ _ _
         · intro _
           apply preservesFresh_bind
           · exact preservesFresh_completedReceivingDestination _
           · intro _; exact preservesFresh_pure _)

theorem preservesFresh_cleanupDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesFresh (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  apply preservesFresh_bind
  · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
  · intro destination
    split
    · exact preservesFresh_pure _
    · apply preservesFresh_bind
      · exact preservesFresh_get
      · intro state
        split
        · exact preservesFresh_lift _ _
        · split
          · exact preservesFresh_pure _
          · exact preservesFresh_lift _ _

theorem preservesFresh_cleanupReceivingDestination (origin : Goose.Core.OriginId)
    (incoming : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesFresh (cleanupReceivingDestination origin incoming carriers) := by
  unfold cleanupReceivingDestination
  apply preservesFresh_bind
  · exact preservesFresh_lift _ _
  · intro current
    exact preservesFresh_cleanupDestination origin current carriers

theorem preservesFresh_protectDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (action : EvalM α) (preserved : PreservesFresh action) :
    PreservesFresh (protectDestination origin id action) := by
  intro state fresh
  have after := preserved state fresh
  cases result : action state with
  | ok value final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using after
  | stop reason final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      have cleaned := preservesFresh_cleanupReceivingDestination origin id carriers final after
      cases cleanup : cleanupReceivingDestination origin id carriers final <;>
        simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      cases kind with
      | breakValue carriers =>
          have cleaned := preservesFresh_cleanupReceivingDestination origin id carriers final after
          cases cleanup : cleanupReceivingDestination origin id carriers final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
      | continueLoop =>
          have cleaned := preservesFresh_cleanupReceivingDestination origin id [] final after
          cases cleanup : cleanupReceivingDestination origin id [] final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned

theorem freshActivations_initial : FreshActivations .initial := by
  simp [FreshActivations, ExecutionState.initial]

theorem freshAct_result (state : ExecutionState) :
    freshAct state = .ok state.nextAct { state with nextAct := state.nextAct + 1 } := rfl

theorem preservesFresh_freshAct : PreservesFresh freshAct := by
  intro state fresh
  rw [freshAct_result]
  obtain ⟨distinct, earlier⟩ := fresh
  refine ⟨distinct, ?_⟩
  intro activation member
  exact Nat.lt_trans (earlier activation member) (Nat.lt_succ_self _)

theorem preservesFresh_freshScope : PreservesFresh freshScope := by
  intro state fresh
  exact fresh

theorem preservesFresh_returned (activation : Goose.Core.ActId) (carriers : List Carrier) :
    PreservesFresh (returned (α := α) activation carriers) := by
  intro state fresh
  exact fresh

theorem targetActivation_selects_nearest (config : EvalConfig) (targetId : Nat)
    (state final : ExecutionState) (activation : RuntimeActivation)
    (selected : targetActivation config targetId state = .ok activation final) :
    final = state ∧ ∃ target discarded outer,
      config.module.targets[targetId]? = some target ∧
      state.activations = discarded ++ activation :: outer ∧
      target.contains activation.implementation = true ∧
      ∀ earlier ∈ discarded, target.contains earlier.implementation = false := by
  cases targetFound : config.module.targets[targetId]? with
  | none => simp [targetActivation, targetFound, fault, EvalM.stop] at selected
  | some target =>
      cases activationFound : selectTarget? target state.activations with
      | none =>
          simp [targetActivation, targetFound, activationFound, EvalM.get, fault, EvalM.stop, bind] at selected
      | some catcher =>
          simp [targetActivation, targetFound, activationFound, EvalM.get, bind, pure] at selected
          obtain ⟨equal, unchanged⟩ := selected
          subst catcher
          subst final
          obtain ⟨discarded, outer, shape, membership, excluded⟩ :=
            Goose.Proofs.Exit.runtime_select_nearest target state.activations activation activationFound
          exact ⟨rfl, target, discarded, outer, rfl, shape, membership, excluded⟩

theorem fresh_activation_push (state : ExecutionState) (activation : RuntimeActivation)
    (fresh : FreshActivations state) (identifier : activation.act = state.nextAct) :
    FreshActivations { state with
      nextAct := state.nextAct + 1, activations := activation :: state.activations } := by
  obtain ⟨distinct, earlier⟩ := fresh
  constructor
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, distinct⟩
    intro member
    obtain ⟨previous, member, equal⟩ := List.mem_map.mp member
    have smaller := earlier previous member
    rw [equal, identifier] at smaller
    exact Nat.lt_irrefl _ smaller
  · intro current member
    rcases List.mem_cons.mp member with equal | member
    · subst current
      rw [identifier]
      exact Nat.lt_succ_self _
    · exact Nat.lt_trans (earlier current member) (Nat.lt_succ_self _)

theorem fresh_scope_release (state : ExecutionState) (activation : RuntimeActivation)
    (scope scopeInst : Nat) (fresh : FreshActivations state) :
    FreshActivations (releaseScopeState activation scope scopeInst state) := by
  obtain ⟨distinct, earlier⟩ := fresh
  have same : ((releaseScopeState activation scope scopeInst state).activations.map (·.act)) =
      state.activations.map (·.act) := by
    simp [releaseScopeState, List.map_map]
    intro current _
    split <;> rfl
  refine ⟨by rw [same]; exact distinct, ?_⟩
  intro current member
  have mapped : current.act ∈ (releaseScopeState activation scope scopeInst state).activations.map (·.act) :=
    List.mem_map.mpr ⟨current, member, rfl⟩
  rw [same] at mapped
  obtain ⟨previous, member, equal⟩ := List.mem_map.mp mapped
  simpa [releaseScopeState, equal] using earlier previous member

theorem fresh_activation_filter (state : ExecutionState) (predicate : RuntimeActivation → Bool)
    (fresh : FreshActivations state) :
    FreshActivations { state with activations := state.activations.filter predicate } := by
  refine ⟨?_, ?_⟩
  · exact List.Nodup.sublist
      ((List.filter_sublist (p := predicate) (l := state.activations)).map (fun current : RuntimeActivation => current.act)) fresh.1
  · intro activation member
    exact fresh.2 activation (List.mem_filter.mp member).1

theorem preservesFresh_landCarrier (origin : Goose.Core.OriginId) (carrier : Carrier) :
    PreservesFresh (landCarrier origin carrier) := by
  unfold landCarrier
  cases carrier with
  | register value => exact preservesFresh_pure _
  | pendingNamed token => exact preservesFresh_stop _
  | completed id =>
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => exact preservesFresh_lift _ _
        | receiver | child parent => exact preservesFresh_pure _

theorem preservesFresh_landCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesFresh (landCarriers origin carriers) := by
  unfold landCarriers
  apply preservesFresh_bind
  · apply preservesFresh_listForIn
    intro carrier _
    apply preservesFresh_bind
    · exact preservesFresh_landCarrier origin carrier
    · intro _; exact preservesFresh_pure _
  · intro _; exact preservesFresh_pure _

theorem preservesFresh_receivingDestination (id : Goose.Core.DestinationId) :
    PreservesFresh (receivingDestination id) := by
  exact preservesFresh_lift _ _

private def completionLanding (origin : Goose.Core.OriginId) (token : ExitReservationId)
    (replacement : Goose.Core.DestinationId) : EvalM (ForInStep PUnit) := do
  let some (.active _ _ selected _) := (← EvalM.get).construction.exitReservations[token]? | fault .flow
  let receiving ← receivingDestination selected
  if receiving != replacement then
    liftConstruction origin (landExitReplacementInto receiving replacement)
  pure (.yield PUnit.unit)

private theorem preservesFresh_completionLanding (origin : Goose.Core.OriginId)
    (token : ExitReservationId) (replacement : Goose.Core.DestinationId) :
    PreservesFresh (completionLanding origin token replacement) := by
  unfold completionLanding
  apply preservesFresh_bind
  · exact preservesFresh_get
  · intro state
    cases found : state.construction.exitReservations[token]? with
    | none => exact preservesFresh_fault .flow
    | some reservation =>
        cases reservation with
        | waiting incoming => exact preservesFresh_fault .flow
        | active role incoming selected snapshot =>
            apply preservesFresh_bind
            · exact preservesFresh_receivingDestination selected
            · intro receiving
              cases changed : (receiving != replacement) with
              | false => simp; exact preservesFresh_pure _
              | true =>
                  simp
                  apply preservesFresh_bind
                  · exact preservesFresh_lift _ _
                  · intro _; exact preservesFresh_pure _
        | restored | released => exact preservesFresh_fault .flow

theorem preservesFresh_landCarriersInto (origin : Goose.Core.OriginId) (channels : List Channel)
    (carriers : List Carrier) : PreservesFresh (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  split
  · exact preservesFresh_stop _
  · simp only [bind]
    apply preservesFresh_bind
    · apply preservesFresh_listForIn
      intro item _
      cases item with
      | mk channel carrier =>
          simp only
          cases channel with
          | register ty =>
              cases carrier with
              | register value => exact preservesFresh_pure _
              | completed id | pendingNamed _ => exact preservesFresh_stop _
          | construct incoming =>
              cases carrier with
              | register value | pendingNamed _ => exact preservesFresh_stop _
              | completed replacement =>
                  simp only
                  apply preservesFresh_bind
                  · exact preservesFresh_receivingDestination incoming
                  · intro current
                    cases changed : (current != replacement) with
                    | false =>
                        simp
                        exact preservesFresh_pure _
                    | true =>
                        simp
                        apply preservesFresh_bind
                        · exact preservesFresh_lift _ _
                        · intro _; exact preservesFresh_pure _
          | completion token =>
              cases carrier with
              | register value => exact preservesFresh_stop _
              | pendingNamed pending =>
                  cases mismatch : (token != pending) with
                  | false => simp [mismatch]; exact preservesFresh_pure _
                  | true => simp [mismatch]; exact preservesFresh_stop _
              | completed replacement =>
                  change PreservesFresh (completionLanding origin token replacement)
                  exact preservesFresh_completionLanding origin token replacement
    · intro _; exact preservesFresh_pure _

theorem preservesFresh_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : PreservesFresh (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier with
  | register value => exact preservesFresh_pure _
  | pendingNamed token => exact preservesFresh_stop _
  | completed id =>
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
      · intro destination
        simp only
        split
        · exact preservesFresh_lift _ _
        · split <;> split
          all_goals
            first
              | exact preservesFresh_lift _ _
              | (apply preservesFresh_bind
                 · exact preservesFresh_lift _ _
                 · intro _
                   apply preservesFresh_bind
                   · exact stateQuery_preservesFresh _ (stateQuery_receivingLayout layout destination.capability.layout)
                   · intro receiving
                     apply preservesFresh_bind
                     · exact preservesFresh_lift _ _
                     · intro _; exact preservesFresh_lift _ _)

theorem preservesFresh_finishChannels (layout : LayoutEnv) (channels : List Channel) (types : List Ty)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesFresh (finishChannels layout channels types carriers origin) := by
  unfold finishChannels
  apply preservesFresh_bind
  · exact preservesFresh_landCarriersInto origin channels carriers
  · intro _
    split
    · exact preservesFresh_stop _
    · apply preservesFresh_bind
      · apply preservesFresh_listForIn
        intro item _
        rcases item with ⟨carrier, result⟩
        apply preservesFresh_bind
        · exact preservesFresh_finishChannel layout origin carrier result
        · intro _; exact preservesFresh_pure _
      · intro _; exact preservesFresh_pure _

theorem preservesFresh_withScope (activation : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (preserved : PreservesFresh action) :
    PreservesFresh (withScope activation scope scopeInst action) := by
  intro state fresh
  have after := preserved state fresh
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using fresh_scope_release final activation scope scopeInst after
  | stop reason final =>
      simpa [withScope, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using fresh_scope_release final activation scope scopeInst after
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using fresh_scope_release final activation scope scopeInst after

theorem preservesFresh_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (preserved : PreservesFresh action) :
    PreservesFresh (finishActivation layout activation types origin action) := by
  intro state fresh
  have after := preserved state fresh
  cases result : action state with
  | ok carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      let trimmed : ExecutionState := { final with
        activations := final.activations.filter (fun current => current.act != activation.act) }
      have trimmedFresh : FreshActivations trimmed := fresh_activation_filter final _ after
      have landedFresh := preservesFresh_finishChannels layout activation.channels types carriers origin trimmed trimmedFresh
      cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
        simpa [finishActivation, result, trimmed, finished, Goose.Proofs.Exit.stepState] using landedFresh
  | stop reason final =>
      simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | jump target kind final =>
      simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      by_cases caught : target.activation = activation.act
      · let trimmed : ExecutionState := { final with
          activations := final.activations.filter (fun current => current.act != activation.act) }
        have trimmedFresh : FreshActivations trimmed := fresh_activation_filter final _ after
        have landedFresh := preservesFresh_finishChannels layout activation.channels types carriers origin trimmed trimmedFresh
        cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
          simpa [finishActivation, result, caught, trimmed, finished, Goose.Proofs.Exit.stepState] using landedFresh
      · simpa [finishActivation, result, caught, Goose.Proofs.Exit.stepState] using
          fresh_activation_filter final (fun current => current.act != activation.act) after

theorem preservesFresh_withBreakTarget (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (preserved : PreservesFresh action) (received : ∀ kind, PreservesFresh (receive kind)) :
    PreservesFresh (withBreakTarget act scope channels action receive) := by
  intro state fresh
  let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
  let installed : ExecutionState := { state with
    nextScope := state.nextScope + 1, breaks := target :: state.breaks }
  have installedFresh : FreshActivations installed := fresh
  have after := preserved installed installedFresh
  cases result : action installed with
  | ok value final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, FreshActivations] using after
  | stop reason final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, FreshActivations] using after
  | escape activation carriers final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, FreshActivations] using after
  | jump actual kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      let removed : ExecutionState := { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) }
      have removedFresh : FreshActivations removed := after
      by_cases caught : actual = state.nextScope
      · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
          Goose.Proofs.Exit.stepState] using received kind removed removedFresh
      · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
          Goose.Proofs.Exit.stepState] using removedFresh

theorem stateQuery_currentBreak (act : Goose.Core.ActId) (scope : Option BreakScope) :
    StateQuery (currentBreak act scope) := by
  unfold currentBreak
  apply stateQuery_bind
  · exact stateQuery_get
  · intro state
    split
    · exact stateQuery_pure _
    · exact stateQuery_stop _

theorem preservesFresh_jump (target : Nat) (kind : JumpKind) :
    PreservesFresh (jump (α := α) target kind) := by
  intro state fresh
  exact fresh

theorem preservesFresh_emitStdout (bytes : ByteArray) : PreservesFresh (emitStdout bytes) :=
  preservesFresh_lift _ _

theorem preservesFresh_truncateOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (count : Nat) (origin : Goose.Core.OriginId) :
    PreservesFresh (truncateOwner fuel layout location count origin) := by
  cases fuel with
  | zero => exact preservesFresh_stop _
  | succ fuel =>
      unfold truncateOwner
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesFresh_stop _
        | stored stored =>
            apply preservesFresh_bind
            · exact stateQuery_preservesFresh _ (stateQuery_sampledStored stored)
            · intro sampled
              rcases sampled with ⟨bytes, run⟩
              simp only
              split
              · exact preservesFresh_stop _
              · apply preservesFresh_bind
                · exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
                · intro finish
                  cases stored.destination with
                  | none =>
                      apply preservesFresh_bind
                      · exact preservesFresh_pure _
                      · intro owner
                        apply preservesFresh_bind
                        · exact preservesFresh_lift _ _
                        · intro _; exact preservesFresh_writeLoc _ _ _ _
                  | some id =>
                      apply preservesFresh_bind
                      · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
                      · intro pending
                        apply preservesFresh_bind
                        · exact preservesFresh_pure _
                        · intro owner
                          apply preservesFresh_bind
                          · exact preservesFresh_lift _ _
                          · intro _; exact preservesFresh_writeLoc _ _ _ _

theorem preservesFresh_appendFixedValues (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (values : List Value) (origin : Goose.Core.OriginId) :
    PreservesFresh (appendFixedValues fuel layout location values origin) := by
  cases fuel with
  | zero => exact preservesFresh_stop _
  | succ fuel =>
      unfold appendFixedValues
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesFresh_stop _
        | stored stored =>
            simp only
            cases elementFound : elementType stored.ty with
            | none => exact preservesFresh_stop _
            | some element =>
                apply preservesFresh_bind
                · apply preservesFresh_listMapM
                  intro value; exact stateQuery_preservesFresh _ (stateQuery_liftExcept _)
                · intro parts
                  apply preservesFresh_bind
                  · exact preservesFresh_ownerDestination _ _ _ _ _
                  · intro destination
                    apply preservesFresh_bind
                    · apply preservesFresh_listForIn
                      intro bytes state
                      apply preservesFresh_bind
                      · exact preservesFresh_lift _ _
                      · intro _; exact preservesFresh_pure _
                    · intro _
                      apply preservesFresh_bind
                      · exact preservesFresh_lift _ _
                      · intro _
                        apply preservesFresh_bind
                        · exact stateQuery_preservesFresh _ (stateQuery_completedDestination destination)
                        · intro completed; exact preservesFresh_publishOwner _ _ _ _ _ _

theorem preservesFresh_appendRun (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (view : RuntimeView) (origin : Goose.Core.OriginId) :
    PreservesFresh (appendRun fuel layout location view origin) := by
  cases fuel with
  | zero => exact preservesFresh_stop _
  | succ fuel =>
      unfold appendRun
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesFresh_stop _
        | stored stored =>
            apply preservesFresh_bind
            · exact stateQuery_preservesFresh _ (stateQuery_readLoc fuel layout view.location)
            · intro source
              apply preservesFresh_bind
              · exact preservesFresh_ownerDestination _ _ _ _ _
              · intro destination
                have finish : PreservesFresh (do
                    liftConstruction origin (finishDestination destination)
                    let completed ← completedDestination destination
                    publishOwner fuel layout location stored completed origin) := by
                  apply preservesFresh_bind
                  · exact preservesFresh_lift _ _
                  · intro _
                    apply preservesFresh_bind
                    · exact stateQuery_preservesFresh _ (stateQuery_completedDestination destination)
                    · intro completed; exact preservesFresh_publishOwner _ _ _ _ _ _
                cases source with
                | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ =>
                    apply preservesFresh_bind
                    · exact preservesFresh_stop _
                    · intro _; exact finish
                | stored source =>
                      apply preservesFresh_bind
                      · exact stateQuery_preservesFresh _ (stateQuery_sampledStored source)
                      · intro sampled
                        rcases sampled with ⟨bytes, run⟩
                        apply preservesFresh_bind
                        · exact preservesFresh_lift _ _
                        · intro _
                          apply preservesFresh_bind
                          · exact packed_writes_preserveFresh fuel layout destination bytes run view.start view.count origin
                          · intro _; exact finish
                | fixed values =>
                      simp only
                      cases elementFound : elementType stored.ty with
                      | none =>
                          apply preservesFresh_bind
                          · exact preservesFresh_stop _
                          · intro _; exact finish
                      | some element =>
                        apply preservesFresh_bind
                        ·
                          apply preservesFresh_rangeForIn
                          intro index current
                          split
                          · apply preservesFresh_bind
                            · exact stateQuery_preservesFresh _ (stateQuery_liftExcept _)
                            · intro bytes
                              apply preservesFresh_bind
                              · exact preservesFresh_lift _ _
                              · intro _; exact preservesFresh_pure _
                          · apply preservesFresh_bind
                            · exact preservesFresh_stop _
                            · intro _; exact preservesFresh_pure _
                        · intro _; exact finish

theorem preservesFresh_allocateActivation (make : Goose.Core.ActId → RuntimeActivation)
    (identifier : ∀ act, (make act).act = act) (action : RuntimeActivation → EvalM α)
    (preserved : ∀ activation, PreservesFresh (action activation)) :
    PreservesFresh (do
      let act ← freshAct
      let activation := make act
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      action activation) := by
  intro state fresh
  have pushed := fresh_activation_push state (make state.nextAct) fresh (identifier _)
  have after := preserved (make state.nextAct)
    { state with nextAct := state.nextAct + 1, activations := make state.nextAct :: state.activations } pushed
  simpa [freshAct, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState] using after

theorem fresh_activations_map (state : ExecutionState) (change : RuntimeActivation → RuntimeActivation)
    (identifier : ∀ activation, (change activation).act = activation.act)
    (fresh : FreshActivations state) :
    FreshActivations { state with activations := state.activations.map change } := by
  obtain ⟨distinct, earlier⟩ := fresh
  have same : (state.activations.map change).map (·.act) = state.activations.map (·.act) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro activation _
    exact identifier activation
  constructor
  · simpa only [same] using distinct
  · intro activation member
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
    rw [← equal, identifier]
    exact earlier original originalMember

theorem stateQuery_getImplementation (config : EvalConfig) (context : Goose.Core.ContextId) :
    StateQuery (getImplementation config context) := by
  unfold getImplementation
  split
  · split
    · exact stateQuery_pure _
    · exact stateQuery_stop _
  · exact stateQuery_stop _

theorem stateQuery_enclosingActivation (environment : RuntimeActivation) :
    StateQuery (enclosingActivation environment) := by
  unfold enclosingActivation
  apply stateQuery_bind
  · exact stateQuery_get
  · intro state
    split
    · exact stateQuery_pure _
    · exact stateQuery_stop _

theorem stateQuery_targetActivation (config : EvalConfig) (target : Nat) :
    StateQuery (targetActivation config target) := by
  unfold targetActivation
  split
  · apply stateQuery_bind
    · exact stateQuery_get
    · intro state
      split
      · exact stateQuery_pure _
      · exact stateQuery_stop _
  · exact stateQuery_stop _

theorem preservesFresh_escaped (address : ExitAddress) (carriers : List Carrier) :
    PreservesFresh (escaped (α := α) address carriers) := by
  intro state fresh
  exact fresh

theorem preservesFresh_constructLocal (declarations : DeclarationEnv) (owner : Goose.Core.ActId) (ty : Ty)
    (origin : Goose.Core.OriginId) (expression : Expr) (construct : Goose.Core.DestinationId → EvalM Unit)
    (preserved : ∀ destination, PreservesFresh (construct destination)) :
    PreservesFresh (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply preservesFresh_bind
  · exact preservesFresh_newDestination _ _ _ _ _ _ _
  · intro destination
    apply preservesFresh_bind
    · exact preserved destination
    · intro _
      apply preservesFresh_bind
      · exact preservesFresh_completedReceivingDestination destination
      · intro completed
        apply preservesFresh_bind
        · exact preservesFresh_publishCarriers _ _
        · intro _; exact preservesFresh_pure _

def exitChannelPreparation (source _activation : RuntimeActivation) (origin : Goose.Core.OriginId) :
    Channel × Expr → EvalM Channel
  | (channel, operand) => do
      match channel with
      | .register ty => pure (.register ty)
      | .construct incoming =>
          let kind ← exitSource source incoming operand
          let (_, selected) ← liftConstruction origin
            (reserveExitDestination incoming kind)
          pure (.construct selected)
      | .completion token =>
          match (← EvalM.get).construction.exitReservations[token]? with
          | some (.waiting _) => pure (.completion token)
          | some (.active _ _ selected _) => do
              let incoming ← receivingDestination selected
              let kind ← exitSource source incoming operand
              let (_, selected) ← liftConstruction origin
                (reserveExitDestination incoming kind)
              pure (.construct selected)
          | _ => fault .flow

theorem preservesFresh_exitChannelPreparation (source activation : RuntimeActivation)
    (origin : Goose.Core.OriginId) (channel : Channel × Expr) :
    PreservesFresh (exitChannelPreparation source activation origin channel) := by
  rcases channel with ⟨channel, operand⟩
  cases channel with
  | register ty => exact preservesFresh_pure _
  | construct incoming =>
      unfold exitChannelPreparation
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_exitSource source incoming operand)
      · intro kind
        apply preservesFresh_bind
        · exact preservesFresh_lift _ _
        · intro _; exact preservesFresh_pure _
  | completion token =>
      unfold exitChannelPreparation
      apply preservesFresh_bind
      · exact preservesFresh_get
      · intro state
        cases present : state.construction.exitReservations[token]? with
        | none => exact preservesFresh_stop _
        | some reservation =>
            cases reservation with
            | waiting incoming => exact preservesFresh_pure _
            | active role incoming selected snapshot =>
                apply preservesFresh_bind
                · exact preservesFresh_receivingDestination selected
                · intro current
                  apply preservesFresh_bind
                  · exact stateQuery_preservesFresh _ (stateQuery_exitSource source current operand)
                  · intro kind
                    apply preservesFresh_bind
                    · exact preservesFresh_lift _ _
                    · intro _; exact preservesFresh_pure _
            | restored | released => exact preservesFresh_stop _

theorem preservesFresh_exitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : PreservesFresh (exitChannels source activation operands origin) := by
  unfold exitChannels
  split
  · exact preservesFresh_stop _
  · apply preservesFresh_listMapM
    intro item
    exact preservesFresh_exitChannelPreparation source activation origin item

def exitChannelReservationTokens (first : Nat) (state : ExecutionState) :
    List ExitReservationId :=
  (List.range (state.construction.exitReservations.size - first)).map (first + ·)

def exitChannelCleanup (origin : Goose.Core.OriginId) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Carrier) : EvalM Unit := do
  for token in tokens.reverse do
    if cancel then
      liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
        match carrier with | .completed id => some id | _ => none))
    liftConstruction origin (releaseExitReservation token)

theorem preservesFresh_exitChannelCleanup (origin : Goose.Core.OriginId)
    (tokens : List ExitReservationId) (cancel : Bool) (carriers : List Carrier) :
    PreservesFresh (exitChannelCleanup origin tokens cancel carriers) := by
  unfold exitChannelCleanup
  cases cancel with
  | false =>
      apply preservesFresh_bind
      · apply preservesFresh_listForIn
        intro token _
        apply preservesFresh_bind
        · exact preservesFresh_lift _ _
        · intro _; exact preservesFresh_pure _
      · intro _; exact preservesFresh_pure _
  | true =>
      apply preservesFresh_bind
      · apply preservesFresh_listForIn
        intro token _
        apply preservesFresh_bind
        · exact preservesFresh_lift _ _
        · intro _
          apply preservesFresh_bind
          · exact preservesFresh_lift _ _
          · intro _; exact preservesFresh_pure _
      · intro _; exact preservesFresh_pure _

def finishExitChannels (origin : Goose.Core.OriginId) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Carrier)
    (result : ExecutionState → ExecutionStep (List Carrier)) : EvalM (List Carrier) := fun state =>
  match exitChannelCleanup origin tokens cancel carriers state with
  | .ok () final => result final
  | .stop reason final => .stop reason final
  | .escape target values final => .escape target values final
  | .jump target kind final => .jump target kind final

def FreshExecutionStep (result : ExecutionStep α) : Prop :=
  match result with
  | .ok _ final | .stop _ final | .escape _ _ final | .jump _ _ final => FreshActivations final

theorem preservesFresh_finishExitChannels (origin : Goose.Core.OriginId)
    (tokens : List ExitReservationId) (cancel : Bool) (carriers : List Carrier)
    (result : ExecutionState → ExecutionStep (List Carrier))
    (resultPreserved : ∀ state, FreshActivations state → FreshExecutionStep (result state)) :
    PreservesFresh (finishExitChannels origin tokens cancel carriers result) := by
  intro state fresh
  unfold finishExitChannels
  have cleanupFresh := preservesFresh_exitChannelCleanup origin tokens cancel carriers state fresh
  cases cleanupResult : exitChannelCleanup origin tokens cancel carriers state with
  | ok value final =>
      simp only [cleanupResult, Goose.Proofs.Exit.stepState] at cleanupFresh
      cases finalResult : result final <;>
        simpa [FreshExecutionStep, cleanupResult, finalResult, Goose.Proofs.Exit.stepState]
          using resultPreserved final cleanupFresh
  | stop reason final =>
      simpa [cleanupResult, Goose.Proofs.Exit.stepState] using cleanupFresh
  | escape address values final =>
      simpa [cleanupResult, Goose.Proofs.Exit.stepState] using cleanupFresh
  | jump target kind final =>
      simpa [cleanupResult, Goose.Proofs.Exit.stepState] using cleanupFresh

def borrowedExitChannelReceipts (activation : RuntimeActivation) (initial : ExecutionState) :
    List BorrowedWaitingExitReservation :=
  activation.channels.filterMap fun channel => match channel with
    | .completion token => captureWaitingExitReservation token initial.construction
    | _ => none

def borrowedExitChannelStep (origin : Goose.Core.OriginId) (carriers : List Carrier)
    (receipt : BorrowedWaitingExitReservation) : EvalM (ForInStep PUnit) := do
  let token := receipt.token
  liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
    match carrier with | .completed id => some id | _ => none))
  match (← EvalM.get).construction.exitReservations[token]? with
  | some .restored => liftConstruction origin (rearmExitReservation receipt)
  | some (.waiting actual) => if actual != receipt.incoming then fault .flow
  | some (.active ..) => pure ()
  | _ => fault .flow
  pure (.yield PUnit.unit)

theorem preservesFresh_borrowedExitChannelStep (origin : Goose.Core.OriginId)
    (carriers : List Carrier) (receipt : BorrowedWaitingExitReservation) :
    PreservesFresh (borrowedExitChannelStep origin carriers receipt) := by
  unfold borrowedExitChannelStep
  apply preservesFresh_bind
  · exact preservesFresh_lift _ _
  · intro _
    apply preservesFresh_bind
    · exact preservesFresh_get
    · intro state
      cases state.construction.exitReservations[receipt.token]? with
      | none => exact preservesFresh_stop _
      | some reservation =>
          cases reservation with
          | restored =>
              apply preservesFresh_bind
              · exact preservesFresh_lift _ _
              · intro _; exact preservesFresh_pure _
          | released => exact preservesFresh_stop _
          | active role incoming selected snapshot => exact preservesFresh_pure _
          | waiting incoming =>
              dsimp only
              split
              · exact preservesFresh_stop _
              · exact preservesFresh_pure _

def exitChannelCleanupBorrowed (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Carrier) : EvalM Unit := do
  if cancel then
    forIn borrowed.reverse PUnit.unit (fun receipt _ => borrowedExitChannelStep origin carriers receipt)
  for token in tokens.reverse do
    if cancel then
      liftConstruction origin (cancelExitReservation token (carriers.filterMap fun carrier =>
        match carrier with | .completed id => some id | _ => none))
    liftConstruction origin (releaseExitReservation token)

theorem preservesFresh_exitChannelCleanupBorrowed (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Carrier) :
    PreservesFresh (exitChannelCleanupBorrowed origin borrowed tokens cancel carriers) := by
  unfold exitChannelCleanupBorrowed
  cases cancel with
  | false => exact preservesFresh_exitChannelCleanup origin tokens false carriers
  | true =>
      apply preservesFresh_bind
      · apply preservesFresh_listForIn
        intro receipt _
        exact preservesFresh_borrowedExitChannelStep origin carriers receipt
      · intro _
        exact preservesFresh_exitChannelCleanup origin tokens true carriers

def finishBorrowedExitChannels (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Carrier)
    (result : ExecutionState → ExecutionStep (List Carrier)) : EvalM (List Carrier) := fun state =>
  match exitChannelCleanupBorrowed origin borrowed tokens cancel carriers state with
  | .ok () final => result final
  | .stop reason final => .stop reason final
  | .escape target values final => .escape target values final
  | .jump target kind final => .jump target kind final

theorem preservesFresh_finishBorrowedExitChannels (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Carrier)
    (result : ExecutionState → ExecutionStep (List Carrier))
    (resultPreserved : ∀ state, FreshActivations state → FreshExecutionStep (result state)) :
    PreservesFresh (finishBorrowedExitChannels origin borrowed tokens cancel carriers result) := by
  intro state fresh
  unfold finishBorrowedExitChannels
  have cleanupFresh := preservesFresh_exitChannelCleanupBorrowed origin borrowed tokens cancel carriers state fresh
  cases cleanupResult : exitChannelCleanupBorrowed origin borrowed tokens cancel carriers state with
  | ok value final =>
      simp only [cleanupResult, Goose.Proofs.Exit.stepState] at cleanupFresh
      cases finalResult : result final <;>
        simpa [FreshExecutionStep, cleanupResult, finalResult, Goose.Proofs.Exit.stepState]
          using resultPreserved final cleanupFresh
  | stop reason final | escape address values final | jump target kind final =>
      simpa [cleanupResult, Goose.Proofs.Exit.stepState] using cleanupFresh

theorem withExitChannels_decomposition (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (initial : ExecutionState) :
    withExitChannels source activation operands origin action initial =
      match exitChannels source activation operands origin initial with
      | .ok channels prepared =>
          match action channels prepared with
          | .ok carriers afterOperands =>
              match materializeOwnedCarriers origin
                  (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                  carriers afterOperands with
              | .ok completed after => finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation initial)
                  (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                  false completed (.ok completed) after
              | .stop reason after => finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation initial)
                  (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                  false [] (.stop reason) after
              | .escape address completed after => finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation initial)
                  (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                  true completed (.escape address completed) after
              | .jump target kind after =>
                  let completed := match kind with
                    | .breakValue completed => completed
                    | .continueLoop => []
                  finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation initial)
                    (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                    true completed (.jump target kind) after
          | .stop reason afterOperands => finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation initial)
              (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
              false [] (.stop reason) afterOperands
          | .escape address carriers afterOperands => finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation initial)
              (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
              true carriers (.escape address carriers) afterOperands
          | .jump target kind afterOperands =>
              let carriers := match kind with
                | .breakValue carriers => carriers
                | .continueLoop => []
              finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation initial)
                (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                true carriers (.jump target kind) afterOperands
      | .stop reason after => .stop reason after
      | .escape address carriers after => .escape address carriers after
      | .jump target kind after => .jump target kind after := by
  simp only [withExitChannels, finishBorrowedExitChannels, exitChannelCleanupBorrowed, borrowedExitChannelReceipts, borrowedExitChannelStep, exitChannelReservationTokens, bind]
  cases preflight : exitChannels source activation operands origin initial with
  | stop reason after | escape address carriers after | jump target kind after => rfl
  | ok channels prepared =>
      dsimp only
      cases evaluated : action channels prepared with
      | stop reason after | escape address carriers after => rfl
      | jump target kind after => cases kind <;> rfl
      | ok carriers afterOperands =>
          dsimp only
          cases materialized : materializeOwnedCarriers origin
              ((List.range (prepared.construction.exitReservations.size - initial.construction.exitReservations.size)).map
                (initial.construction.exitReservations.size + ·)) carriers afterOperands with
          | ok completed after | stop reason after | escape address completed after => rfl
          | jump target kind after => cases kind <;> rfl

theorem preservesFresh_withExitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (actionPreserved : ∀ channels, PreservesFresh (action channels)) :
    PreservesFresh (withExitChannels source activation operands origin action) := by
  intro state fresh
  rw [withExitChannels_decomposition source activation operands origin action state]
  cases preflight : exitChannels source activation operands origin state with
  | ok channels prepared =>
      have preflightFresh := preservesFresh_exitChannels source activation operands origin state fresh
      simp only [preflight, Goose.Proofs.Exit.stepState] at preflightFresh
      cases evaluation : action channels prepared with
      | ok carriers after =>
          have actionFresh := actionPreserved channels prepared preflightFresh
          simp only [evaluation, Goose.Proofs.Exit.stepState] at actionFresh
          let tokens := exitChannelReservationTokens state.construction.exitReservations.size prepared
          cases materialized : materializeOwnedCarriers origin tokens carriers after with
          | ok completed afterMaterialized =>
              have materializedFresh := preservesFresh_materializeOwnedCarriers origin tokens carriers
                after actionFresh
              simp only [materialized, Goose.Proofs.Exit.stepState] at materializedFresh
              simpa [preflight, evaluation, materialized, tokens] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
                (exitChannelReservationTokens state.construction.exitReservations.size prepared)
                false completed (fun final => .ok completed final)
                (by intro final finalFresh; exact finalFresh) afterMaterialized materializedFresh
          | stop reason afterMaterialized =>
              have materializedFresh := preservesFresh_materializeOwnedCarriers origin tokens carriers
                after actionFresh
              simp only [materialized, Goose.Proofs.Exit.stepState] at materializedFresh
              simpa [preflight, evaluation, materialized, tokens] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
                (exitChannelReservationTokens state.construction.exitReservations.size prepared)
                false [] (fun final => .stop reason final)
                (by intro final finalFresh; exact finalFresh) afterMaterialized materializedFresh
          | escape address completed afterMaterialized =>
              have materializedFresh := preservesFresh_materializeOwnedCarriers origin tokens carriers
                after actionFresh
              simp only [materialized, Goose.Proofs.Exit.stepState] at materializedFresh
              simpa [preflight, evaluation, materialized, tokens] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
                (exitChannelReservationTokens state.construction.exitReservations.size prepared)
                true completed (fun final => .escape address completed final)
                (by intro final finalFresh; exact finalFresh) afterMaterialized materializedFresh
          | jump target kind afterMaterialized =>
              have materializedFresh := preservesFresh_materializeOwnedCarriers origin tokens carriers
                after actionFresh
              simp only [materialized, Goose.Proofs.Exit.stepState] at materializedFresh
              cases kind with
              | breakValue completed =>
                  simpa [preflight, evaluation, materialized, tokens] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
                    (exitChannelReservationTokens state.construction.exitReservations.size prepared)
                    true completed (fun final => .jump target (.breakValue completed) final)
                    (by intro final finalFresh; exact finalFresh) afterMaterialized materializedFresh
              | continueLoop =>
                  simpa [preflight, evaluation, materialized, tokens] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
                    (exitChannelReservationTokens state.construction.exitReservations.size prepared)
                    true [] (fun final => .jump target .continueLoop final)
                    (by intro final finalFresh; exact finalFresh) afterMaterialized materializedFresh
      | stop reason after =>
          have actionFresh := actionPreserved channels prepared preflightFresh
          simp only [evaluation, Goose.Proofs.Exit.stepState] at actionFresh
          simpa only [preflight, evaluation] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
            (exitChannelReservationTokens state.construction.exitReservations.size prepared)
            false [] (fun final => .stop reason final)
            (by intro final finalFresh; exact finalFresh) after actionFresh
      | escape address carriers after =>
          have actionFresh := actionPreserved channels prepared preflightFresh
          simp only [evaluation, Goose.Proofs.Exit.stepState] at actionFresh
          simpa only [preflight, evaluation] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
            (exitChannelReservationTokens state.construction.exitReservations.size prepared)
            true carriers (fun final => .escape address carriers final)
            (by intro final finalFresh; exact finalFresh) after actionFresh
      | jump target kind after =>
          have actionFresh := actionPreserved channels prepared preflightFresh
          simp only [evaluation, Goose.Proofs.Exit.stepState] at actionFresh
          cases kind with
          | breakValue carriers =>
              simpa only [preflight, evaluation] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
                (exitChannelReservationTokens state.construction.exitReservations.size prepared)
                true carriers (fun final => .jump target (.breakValue carriers) final)
                (by intro final finalFresh; exact finalFresh) after actionFresh
          | continueLoop =>
              simpa only [preflight, evaluation] using preservesFresh_finishBorrowedExitChannels origin (borrowedExitChannelReceipts activation state)
                (exitChannelReservationTokens state.construction.exitReservations.size prepared)
                true [] (fun final => .jump target .continueLoop final)
                (by intro final finalFresh; exact finalFresh) after actionFresh
  | stop reason final =>
      have preflightFresh := preservesFresh_exitChannels source activation operands origin state fresh
      simpa [preflight, Goose.Proofs.Exit.stepState] using preflightFresh
  | escape address carriers final =>
      have preflightFresh := preservesFresh_exitChannels source activation operands origin state fresh
      simpa [preflight, Goose.Proofs.Exit.stepState] using preflightFresh
  | jump target kind final =>
      have preflightFresh := preservesFresh_exitChannels source activation operands origin state fresh
      simpa [preflight, Goose.Proofs.Exit.stepState] using preflightFresh


theorem preservesFresh_openElementReceiving (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (location : Goose.Core.Loc) (stored : StoredValue) (element : Ty) (known : Option Nat)
    (origin : Goose.Core.OriginId) :
    PreservesFresh (openElementReceiving layout owner location stored element known origin) := by
  unfold openElementReceiving
  apply preservesFresh_bind
  · exact stateQuery_preservesFresh _ (stateQuery_sampledStored stored)
  · intro sampled
    rcases sampled with ⟨bytes, run⟩
    apply preservesFresh_bind
    · exact stateQuery_preservesFresh _ (stateQuery_receivingLayout layout element)
    · intro receiving
      cases stored.destination with
      | none => exact preservesFresh_lift _ _
      | some id =>
          apply preservesFresh_bind
          · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
          · intro pending
            cases pending.progress <;> first
              | exact preservesFresh_lift _ _
              | exact preservesFresh_stop _

theorem preservesFresh_publishElementReceiving (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (stored : StoredValue) (destination : Goose.Core.DestinationId)
    (origin : Goose.Core.OriginId) :
    PreservesFresh (publishElementReceiving fuel layout location stored destination origin) := by
  cases fuel with
  | zero => exact preservesFresh_stop _
  | succ fuel =>
      unfold publishElementReceiving
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_getDestination destination)
      · intro pending
        cases pending.use with
        | replacement _ => exact preservesFresh_stop _
        | child parent =>
            apply preservesFresh_bind
            · exact preservesFresh_lift _ _
            · intro _
              apply preservesFresh_bind
              · exact stateQuery_preservesFresh _ (stateQuery_storedDestination parent)
              · intro value; exact preservesFresh_writeLoc _ _ _ _
        | receiver =>
            apply preservesFresh_bind
            · exact preservesFresh_lift _ _
            · intro _
              apply preservesFresh_bind
              · exact stateQuery_preservesFresh _ (stateQuery_getStorage stored.storage)
              · intro value; exact preservesFresh_writeLoc _ _ _ _

structure EvaluationPreservesFresh (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, PreservesFresh (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, PreservesFresh (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, PreservesFresh (evalPlace fuel config environment operand)
  view : ∀ environment operand, PreservesFresh (evalView fuel config environment operand)
  produce : ∀ environment channels operand, PreservesFresh (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, PreservesFresh (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, PreservesFresh (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, PreservesFresh (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, PreservesFresh (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, PreservesFresh (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, PreservesFresh (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, PreservesFresh (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, PreservesFresh (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, PreservesFresh (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, PreservesFresh (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, PreservesFresh (execStmts fuel config environment statements)
  statement : ∀ environment statement, PreservesFresh (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, PreservesFresh (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, PreservesFresh (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, PreservesFresh (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, PreservesFresh (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, PreservesFresh (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, PreservesFresh (pushValue fuel config environment owner expression origin)

end Goose.Proofs.ExitExecution
