import Goose.Construct.Eval
import Goose.Proofs.Exit
import Init.Data.List.Monadic

namespace Goose.Proofs.ExitExecution
open Goose.Construct

local instance : LawfulMonad EvalM := LawfulMonad.mk'
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

theorem stateQuery_rootOf (activation : RuntimeActivation) (localVar : Goose.Core.VarId) :
    StateQuery (rootOf activation localVar) := by
  intro state
  cases present : activation.vars[localVar]? with
  | none => simp [rootOf, present, fault, EvalM.stop, Goose.Proofs.Exit.stepState]
  | some descriptor =>
      cases scopeFound : activation.scopes.find? (fun entry => entry.1 == descriptor.scope) <;>
        simp [rootOf, present, scopeFound, fault, EvalM.stop, pure, Goose.Proofs.Exit.stepState]

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

theorem preservesFresh_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    PreservesFresh (liftConstruction origin action) := by
  intro state fresh
  unfold liftConstruction
  cases action state.construction <;> exact fresh

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
        simp only
        split
        · exact preservesFresh_lift _ _
        · split
          · exact preservesFresh_pure _
          · exact preservesFresh_lift _ _

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
      have cleaned := preservesFresh_cleanupDestination origin id carriers final after
      cases cleanup : cleanupDestination origin id carriers final <;>
        simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      cases kind with
      | breakValue carriers =>
          have cleaned := preservesFresh_cleanupDestination origin id carriers final after
          cases cleanup : cleanupDestination origin id carriers final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
      | continueLoop =>
          have cleaned := preservesFresh_cleanupDestination origin id [] final after
          cases cleanup : cleanupDestination origin id [] final <;>
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

theorem preservesFresh_landCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesFresh (landCarriers origin carriers) := by
  unfold landCarriers
  apply preservesFresh_bind
  · apply preservesFresh_listForIn
    intro carrier _
    cases carrier with
    | register value => exact preservesFresh_pure _
    | completed id =>
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
        · intro destination
          cases destination.use with
          | replacement old =>
              apply preservesFresh_bind
              · exact preservesFresh_lift _ _
              · intro _; exact preservesFresh_pure _
          | receiver | child parent => exact preservesFresh_pure _
  · intro _; exact preservesFresh_pure _

theorem preservesFresh_finishChannels (layout : LayoutEnv) (types : List Ty)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesFresh (finishChannels layout types carriers origin) := by
  unfold finishChannels
  apply preservesFresh_bind
  · exact preservesFresh_landCarriers origin carriers
  · intro _
    split
    · exact preservesFresh_stop _
    · apply preservesFresh_bind
      · apply preservesFresh_listForIn
        intro item _
        rcases item with ⟨carrier, result⟩
        cases carrier with
        | register value => exact preservesFresh_pure _
        | completed id =>
            apply preservesFresh_bind
            · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
            · intro destination
              simp only
              split <;> split
              all_goals
                apply preservesFresh_bind
                · exact preservesFresh_lift _ _
                · intro _
                  first
                    | exact preservesFresh_pure _
                    | (apply preservesFresh_bind
                       · exact stateQuery_preservesFresh _ (stateQuery_receivingLayout layout destination.capability.layout)
                       · intro receiving
                         apply preservesFresh_bind
                         · exact preservesFresh_lift _ _
                         · intro _
                           apply preservesFresh_bind
                           · exact preservesFresh_lift _ _
                           · intro _; exact preservesFresh_pure _)
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
      have landedFresh := preservesFresh_finishChannels layout types carriers origin trimmed trimmedFresh
      cases finished : finishChannels layout types carriers origin trimmed <;>
        simpa [finishActivation, result, trimmed, finished, Goose.Proofs.Exit.stepState] using landedFresh
  | stop reason final =>
      simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | jump target kind final =>
      simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      by_cases caught : target = activation.act
      · let trimmed : ExecutionState := { final with
          activations := final.activations.filter (fun current => current.act != activation.act) }
        have trimmedFresh : FreshActivations trimmed := fresh_activation_filter final _ after
        have landedFresh := preservesFresh_finishChannels layout types carriers origin trimmed trimmedFresh
        cases finished : finishChannels layout types carriers origin trimmed <;>
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

end Goose.Proofs.ExitExecution
