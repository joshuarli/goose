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
      | (apply stateQuery_bind
         · exact stateQuery_get
         · intro state
           split <;> first | exact stateQuery_pure _ | exact stateQuery_stop _)

theorem stateQuery_carrierValue (carrier : Carrier) : StateQuery (carrierValue carrier) := by
  cases carrier with
  | register value => exact stateQuery_pure _
  | completed id =>
      unfold carrierValue
      apply stateQuery_bind
      · exact stateQuery_storedDestination id
      · intro stored; exact stateQuery_pure _

theorem stateQuery_singleCarrier (carriers : List Carrier) : StateQuery (singleCarrier carriers) := by
  unfold singleCarrier
  split <;> first | exact stateQuery_pure _ | exact stateQuery_stop _

theorem preservesFresh_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesFresh (publishCarriers origin carriers) := preservesFresh_lift _ _

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
      · exact stateQuery_preservesFresh _ (stateQuery_storedDestination source)
      · intro stored
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_getStorage stored.storage)
        · intro receiving
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
      · exact stateQuery_preservesFresh _ (stateQuery_getDestination destination)
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
                      · simpa only [Nat.zero_add] using packed_writes_preserveFresh fuel layout destination bytes run 0 run.count origin
                      · intro _; exact preservesFresh_lift _ _
            | fixed values =>
                cases source with
                | none =>
                    apply preservesFresh_bind
                    · exact fixed_writes_preserveFresh fuel layout destination element origin values
                    · intro _; exact preservesFresh_lift _ _
                | some source =>
                    apply preservesFresh_bind
                    · exact preservesFresh_lift _ _
                    · intro _
                      apply preservesFresh_bind
                      · exact fixed_writes_preserveFresh fuel layout destination element origin values
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
                                  · exact packed_writes_preserveFresh fuel layout destination bytes run start count origin
                                  · intro _; exact preservesFresh_lift _ _
                      | fixed values =>
                          simp only
                          split
                          · exact preservesFresh_stop _
                          · apply preservesFresh_bind
                            · exact preservesFresh_lift _ _
                            · intro _
                              apply preservesFresh_bind
                              · exact fixed_writes_preserveFresh fuel layout destination element origin (values.extract start (start + count))
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

theorem preservesFresh_landCarrier (origin : Goose.Core.OriginId) (carrier : Carrier) :
    PreservesFresh (landCarrier origin carrier) := by
  unfold landCarrier
  cases carrier with
  | register value => exact preservesFresh_pure _
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

theorem preservesFresh_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : PreservesFresh (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier with
  | register value => exact preservesFresh_pure _
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
      have landedFresh := preservesFresh_finishChannels layout types carriers origin trimmed trimmedFresh
      cases finished : finishChannels layout types carriers origin trimmed <;>
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
      · exact stateQuery_preservesFresh _ (stateQuery_completedDestination destination)
      · intro completed
        apply preservesFresh_bind
        · exact preservesFresh_publishCarriers _ _
        · intro _; exact preservesFresh_pure _

theorem preservesFresh_exitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : PreservesFresh (exitChannels source activation operands origin) := by
  unfold exitChannels
  split
  · exact preservesFresh_stop _
  · apply preservesFresh_listMapM
    intro item
    rcases item with ⟨channel, operand⟩
    cases channel with
    | register ty => exact preservesFresh_pure _
    | construct id =>
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
        · intro destination
          have finish (alias : Bool) : PreservesFresh
              (if (match destination.progress with | .open 0 => true | _ => false) || alias then
                pure (Channel.construct id)
              else do pure (Channel.construct (← liftConstruction origin (openExitReplacement id)))) := by
            split <;> split
            all_goals first
              | exact preservesFresh_pure _
              | (apply preservesFresh_bind
                 · exact preservesFresh_lift _ _
                 · intro _; exact preservesFresh_pure _)
          cases operand <;> first
            | (apply preservesFresh_bind
               · exact preservesFresh_pure _
               · intro alias; exact finish alias)
            | (apply preservesFresh_bind
               · exact stateQuery_preservesFresh _ (stateQuery_rootOf _ _)
               · intro root
                 apply preservesFresh_bind
                 · exact preservesFresh_get
                 · intro state
                   split
                   all_goals
                     apply preservesFresh_bind
                     · exact preservesFresh_pure _
                     · intro alias; exact finish alias)


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

theorem evaluationPreservesFresh_zero (config : EvalConfig) : EvaluationPreservesFresh 0 config := by
  constructor
  all_goals intros
  all_goals simp [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
    buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
    execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
    execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
    PreservesFresh, Goose.Proofs.Exit.stepState, bind]

private theorem evalBound_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) :
    PreservesFresh (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases operand with
  | omitted => simpa only [evalBound] using preservesFresh_pure defaultValue
  | expr expression | fromEnd expression =>
      simp only [evalBound]
      apply preservesFresh_bind
      · exact previous.value _ _
      · intro value
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_expectInt value)
        · intro pair; exact preservesFresh_pure _

private theorem evalPlace_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (operand : Place) :
    PreservesFresh (evalPlace (fuel + 1) config environment operand) := by
  cases operand with
  | var localVar =>
      simp only [evalPlace]
      apply preservesFresh_bind
      · exact stateQuery_preservesFresh _ (stateQuery_rootOf _ _)
      · intro _; exact preservesFresh_pure _
  | global global => simpa only [evalPlace] using preservesFresh_pure (Goose.Core.Loc.mk (.global global) [])
  | deref expression =>
      simp only [evalPlace]
      apply preservesFresh_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_preservesFresh _ (stateQuery_expectRef value)
  | elem view expression origin =>
      simp only [evalPlace]
      apply preservesFresh_bind
      · exact previous.view _ _
      · intro view
        apply preservesFresh_bind
        · exact previous.value _ _
        · intro value
          apply preservesFresh_bind
          · exact stateQuery_preservesFresh _ (stateQuery_expectInt value)
          · intro pair
            rcases pair with ⟨ty, index⟩
            split
            · exact preservesFresh_pure _
            · exact preservesFresh_stop _
  | field place index =>
      simp only [evalPlace]
      apply preservesFresh_bind
      · exact previous.place _ _
      · intro _; exact preservesFresh_pure _

private theorem evalView_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (operand : View) :
    PreservesFresh (evalView (fuel + 1) config environment operand) := by
  cases operand with
  | of place =>
      simp only [evalView]
      apply preservesFresh_bind
      · exact previous.place _ _
      · intro location
        apply preservesFresh_bind
        · exact stateQuery_preservesFresh _ (stateQuery_readLoc _ _ _)
        · intro value
          apply preservesFresh_bind
          · exact stateQuery_preservesFresh _ (stateQuery_arrayLength value)
          · intro pair
            rcases pair with ⟨count, dynamic⟩
            exact preservesFresh_pure _
  | val expression =>
      simp only [evalView]
      apply preservesFresh_bind
      · exact previous.value _ _
      · intro value
        cases value <;> first
          | exact preservesFresh_pure _
          | (apply preservesFresh_bind
             · exact stateQuery_preservesFresh _ (stateQuery_arrayLength _)
             · intro pair
               rcases pair with ⟨count, dynamic⟩
               apply preservesFresh_bind
               · exact preservesFresh_freshScope
               · intro index
                 apply preservesFresh_bind
                 · exact preservesFresh_bindRoot _ _
                 · intro _; exact preservesFresh_pure _)

private theorem evalOperands_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    PreservesFresh (evalOperands (fuel + 1) config environment channels operands) := by
  cases channels <;> cases operands <;> simp only [evalOperands]
  all_goals first
    | exact preservesFresh_pure _
    | exact preservesFresh_stop _
    | (apply preservesFresh_bind
       · exact previous.produce _ _ _
       · intro carriers
         apply preservesFresh_bind
         · exact stateQuery_preservesFresh _ (stateQuery_singleCarrier carriers)
         · intro carrier
           apply preservesFresh_bind
           · exact previous.operands _ _ _
           · intro _; exact preservesFresh_pure _)

private theorem evalPrintArg_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (argument : PrintArg) :
    PreservesFresh (evalPrintArg (fuel + 1) config environment argument) := by
  cases argument with
  | text text => simpa only [evalPrintArg] using preservesFresh_pure text.toUTF8
  | expr expression =>
      simp only [evalPrintArg]
      apply preservesFresh_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_preservesFresh _ ((rendering_stateQueries fuel config.layout).1 _ _)
  | view view =>
      simp only [evalPrintArg]
      apply preservesFresh_bind
      · exact previous.view _ _
      · intro view; exact stateQuery_preservesFresh _ ((rendering_stateQueries fuel config.layout).2.2.2 _ _)

private theorem evalArguments_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) :
    PreservesFresh (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases parameters with
  | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact preservesFresh_pure _
      · exact preservesFresh_stop _
  | cons parameter parameters =>
      cases arguments with
      | nil => simpa only [evalArguments, fault] using preservesFresh_stop (Goose.Core.Stop.fault .arity)
      | cons argument arguments =>
          have finish (value : Value) : PreservesFresh (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
            apply preservesFresh_bind
            · exact previous.arguments _ _ _ _
            · intro _; exact preservesFresh_pure _
          cases argument with
          | byVal expression =>
              simp only [evalArguments]
              apply preservesFresh_bind
              · exact previous.value _ _
              · intro value; exact finish value
          | byRef mutability place =>
              simp only [evalArguments]
              apply preservesFresh_bind
              · exact previous.place _ _
              · intro location
                apply preservesFresh_bind
                · exact preservesFresh_pure _
                · intro value; exact finish value
          | construct expression =>
              simp only [evalArguments]
              split
              · apply preservesFresh_bind
                · apply preservesFresh_constructLocal
                  intro destination; exact previous.build _ _ _
                · intro carrier
                  apply preservesFresh_bind
                  · exact stateQuery_preservesFresh _ (stateQuery_carrierValue carrier)
                  · intro value; exact finish value
              · apply preservesFresh_bind
                · exact preservesFresh_stop _
                · intro value; exact finish value

private theorem execStmts_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) : PreservesFresh (execStmts (fuel + 1) config environment statements) := by
  cases statements with
  | nil => simpa only [execStmts] using preservesFresh_pure (Flow.normal .unit)
  | cons statement statements =>
      simp only [execStmts]
      apply preservesFresh_bind
      · exact previous.statement _ _
      · intro flow
        cases flow with
        | normal value => exact previous.statements _ _
        | breaking value | continuing => exact preservesFresh_pure _

private theorem execResultBlock_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    PreservesFresh (execResultBlock (fuel + 1) config environment channels body) := by
  simpa only [execResultBlock] using previous.resultBlockWith environment [] channels body

private theorem execActivationBody_preservesFresh (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (preserved : PreservesFresh (execResultBlockWith fuel config environment pre environment.channels body)) :
    PreservesFresh (execActivationBody fuel config environment pre body) := by
  unfold execActivationBody
  apply preservesFresh_bind
  · exact preserved
  · intro result
    rcases result with ⟨flow, carriers⟩
    cases flow <;> first | exact preservesFresh_pure _ | exact preservesFresh_stop _

private theorem enterActivation_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    PreservesFresh (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  split
  · apply preservesFresh_finishActivation
    exact previous.activationBody _ _ _
  · exact preservesFresh_stop _

private theorem preservesFresh_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (identifier : ∀ activation, (change activation).act = activation.act)
    (action : EvalM α) (preserved : PreservesFresh action) :
    PreservesFresh (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state fresh
  have updated := fresh_activations_map state change identifier fresh
  simpa [EvalM.get, EvalM.set, bind, pure] using preserved _ updated

private theorem preservesFresh_fault (kind : Goose.Core.FaultKind) : PreservesFresh (fault (α := α) kind) :=
  preservesFresh_stop _

private theorem preservesFresh_timeout : PreservesFresh (timeout (α := α)) := preservesFresh_stop _

private theorem preservesFresh_abortAt (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    PreservesFresh (abortAt (α := α) kind origin) := preservesFresh_stop _

private theorem preservesFresh_fault_bind (kind : Goose.Core.FaultKind) (next : α → EvalM β) :
    PreservesFresh (fault kind >>= next) := by
  intro state fresh
  exact fresh

private theorem preservesFresh_timeout_bind (next : α → EvalM β) :
    PreservesFresh (timeout >>= next) := by
  intro state fresh
  exact fresh

private theorem preservesFresh_abortAt_bind (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId)
    (next : α → EvalM β) : PreservesFresh (abortAt kind origin >>= next) := by
  intro state fresh
  exact fresh

local syntax "fresh_eval" ident : tactic
macro_rules
  | `(tactic| fresh_eval $previous:ident) => `(tactic|
  repeat' first
    | with_reducible assumption
    | with_reducible exact preservesFresh_pure _
    | with_reducible exact preservesFresh_stop _
    | with_reducible exact preservesFresh_fault _
    | with_reducible exact preservesFresh_timeout
    | with_reducible exact preservesFresh_abortAt _ _
    | with_reducible exact preservesFresh_fault_bind _ _
    | with_reducible exact preservesFresh_timeout_bind _
    | with_reducible exact preservesFresh_abortAt_bind _ _ _
    | with_reducible exact preservesFresh_get
    | with_reducible exact preservesFresh_lift _ _
    | with_reducible exact preservesFresh_bindRoot _ _
    | with_reducible exact preservesFresh_bindStaticRoot _ _
    | with_reducible exact preservesFresh_reserveRootObject _
    | with_reducible exact preservesFresh_setObjectOrdinal _ _
    | with_reducible exact preservesFresh_newDestination _ _ _ _ _ _ _
    | with_reducible exact preservesFresh_channelsFor _ _ _ _
    | with_reducible exact preservesFresh_freshAct
    | with_reducible exact preservesFresh_freshScope
    | with_reducible exact preservesFresh_returned _ _
    | with_reducible exact preservesFresh_escaped _ _
    | with_reducible exact preservesFresh_jump _ _
    | with_reducible exact preservesFresh_emitStdout _
    | with_reducible exact preservesFresh_publishCarriers _ _
    | with_reducible exact preservesFresh_copyValue _ _ _ _ _ _
    | with_reducible exact preservesFresh_deliverCarriers _ _ _ _ _
    | with_reducible exact preservesFresh_ownerDestination _ _ _ _ _
    | with_reducible exact preservesFresh_publishOwner _ _ _ _ _ _
    | with_reducible exact preservesFresh_openElementReceiving _ _ _ _ _ _ _
    | with_reducible exact preservesFresh_publishElementReceiving _ _ _ _ _ _
    | with_reducible exact preservesFresh_repeatElement _ _ _ _ _ _
    | with_reducible exact preservesFresh_truncateOwner _ _ _ _ _
    | with_reducible exact preservesFresh_appendFixedValues _ _ _ _ _
    | with_reducible exact preservesFresh_appendRun _ _ _ _ _
    | with_reducible exact preservesFresh_writeLoc _ _ _ _
    | with_reducible exact preservesFresh_landCarriers _ _
    | with_reducible exact preservesFresh_bindAll _ _ _
    | with_reducible exact preservesFresh_exitChannels _ _ _ _
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_rootOf _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_expectInt _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_expectBool _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_expectRef _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_sameIntType _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_comparable _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_readLoc _ _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_arrayLength _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_getDestination _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_getStorage _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_sampledStored _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_readStoredElement _ _ _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_carrierValue _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_singleCarrier _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_completedDestination _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_storedDestination _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_receivingLayout _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_getImplementation _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_enclosingActivation _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_targetActivation _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_currentBreak _ _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_liftExcept _)
    | with_reducible exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
    | with_reducible exact ($previous).value _ _
    | with_reducible exact ($previous).bound _ _ _ _
    | with_reducible exact ($previous).place _ _
    | with_reducible exact ($previous).view _ _
    | with_reducible exact ($previous).produce _ _ _
    | with_reducible exact ($previous).operands _ _ _
    | with_reducible exact ($previous).build _ _ _
    | with_reducible exact ($previous).element _ _ _ _
    | with_reducible exact ($previous).arguments _ _ _ _
    | with_reducible exact ($previous).call _ _ _ _ _
    | with_reducible exact ($previous).activation _ _ _ _
    | with_reducible exact ($previous).activationBody _ _ _
    | with_reducible exact ($previous).resultBlock _ _ _
    | with_reducible exact ($previous).resultBlockWith _ _ _ _
    | with_reducible exact ($previous).block _ _ _ _
    | with_reducible exact ($previous).statements _ _
    | with_reducible exact ($previous).statement _ _
    | with_reducible exact ($previous).printArgument _ _
    | with_reducible exact ($previous).whileLoop _ _ _
    | with_reducible exact ($previous).rangeLoop _ _ _ _ _ _
    | with_reducible exact ($previous).eachLoop _ _ _ _ _ _ _
    | with_reducible exact ($previous).loop _ _ _
    | with_reducible exact ($previous).push _ _ _ _
    | with_reducible apply preservesFresh_allocateActivation
    | with_reducible apply preservesFresh_mapActivations
    | with_reducible apply preservesFresh_protectDestination
    | with_reducible apply preservesFresh_withScope
    | with_reducible apply preservesFresh_finishActivation
    | with_reducible apply preservesFresh_withBreakTarget
    | with_reducible apply preservesFresh_constructLocal
    | with_reducible apply preservesFresh_bind
    | with_reducible apply preservesFresh_listMapM
    | with_reducible apply preservesFresh_listForIn
    | with_reducible apply preservesFresh_arrayForIn
    | with_reducible apply preservesFresh_rangeForIn
    | with_reducible split
    | with_reducible rfl
    | with_reducible intro)

private theorem evalValue_lit_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Goose.Core.IntTy) (value : Int) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.lit ty value)) := by
  simp only [evalValue]
  fresh_eval _previous

private theorem evalValue_bool_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (value : Bool) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.bool value)) := by
  simp only [evalValue]
  fresh_eval _previous

private theorem evalValue_read_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (place : Place) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.read place)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_ref_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (place : Place) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.ref mutability place)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_slice_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (view : View) (lo hi : Bound) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.slice mutability view lo hi origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_len_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (view : View) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.len view)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_un_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.un operation expression origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_bin_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.bin operation first second origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_cmp_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.cmp operation first second)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_and_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.and first second)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_or_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.or first second)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_not_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (expression : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.not expression)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_conv_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.conv kind target expression origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_call_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.call context arguments origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_push_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Option Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.push owner expression origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_pop_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (owner : Place) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.pop owner origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_ifE_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.ifE condition yes no origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_blockE_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (body : Block) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.blockE body origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_arrLit_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.arrLit ty operands origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_fill_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.fill ty expression origin)) := by
  cases ty <;> simp only [evalValue]
  all_goals fresh_eval previous

private theorem evalValue_structLit_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.structLit ty operands)) := by
  cases ty <;> simp only [evalValue]
  all_goals fresh_eval previous

private theorem evalValue_bytes_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.bytes ty bytes origin)) := by
  cases ty <;> try simp only [evalValue]
  all_goals fresh_eval previous
  case slice mutability element =>
    cases element <;> try simp only [evalValue]
    all_goals fresh_eval previous
    case int ty =>
      cases ty <;> simp only [evalValue]
      all_goals fresh_eval previous

private theorem evalValue_str_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.str ty arguments origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_copy_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.copy ty source origin)) := by
  simp only [evalValue]
  fresh_eval previous

private theorem evalValue_resultLocal_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.resultLocal localVar origin)) := by
  simp only [evalValue]
  fresh_eval _previous

private theorem evalValue_values_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (operands : List Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment (Expr.values operands)) := by
  cases operands with
  | nil => simpa only [evalValue] using preservesFresh_pure Value.unit
  | cons expression operands =>
      cases operands <;> simp only [evalValue]
      all_goals fresh_eval previous

private theorem evalValue_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (expression : Expr) :
    PreservesFresh (evalValue (fuel + 1) config environment expression) := by
  cases expression with
  | lit ty value => exact evalValue_lit_preservesFresh_succ fuel config previous environment ty value
  | bool value => exact evalValue_bool_preservesFresh_succ fuel config previous environment value
  | read place => exact evalValue_read_preservesFresh_succ fuel config previous environment place
  | ref mutability place => exact evalValue_ref_preservesFresh_succ fuel config previous environment mutability place
  | slice mutability view lo hi origin => exact evalValue_slice_preservesFresh_succ fuel config previous environment mutability view lo hi origin
  | len view => exact evalValue_len_preservesFresh_succ fuel config previous environment view
  | un operation expression origin => exact evalValue_un_preservesFresh_succ fuel config previous environment operation expression origin
  | bin operation first second origin => exact evalValue_bin_preservesFresh_succ fuel config previous environment operation first second origin
  | cmp operation first second => exact evalValue_cmp_preservesFresh_succ fuel config previous environment operation first second
  | and first second => exact evalValue_and_preservesFresh_succ fuel config previous environment first second
  | or first second => exact evalValue_or_preservesFresh_succ fuel config previous environment first second
  | not expression => exact evalValue_not_preservesFresh_succ fuel config previous environment expression
  | conv kind target expression origin => exact evalValue_conv_preservesFresh_succ fuel config previous environment kind target expression origin
  | call context arguments origin => exact evalValue_call_preservesFresh_succ fuel config previous environment context arguments origin
  | push owner expression origin => exact evalValue_push_preservesFresh_succ fuel config previous environment owner expression origin
  | pop owner origin => exact evalValue_pop_preservesFresh_succ fuel config previous environment owner origin
  | ifE condition yes no origin => exact evalValue_ifE_preservesFresh_succ fuel config previous environment condition yes no origin
  | blockE body origin => exact evalValue_blockE_preservesFresh_succ fuel config previous environment body origin
  | arrLit ty operands origin => exact evalValue_arrLit_preservesFresh_succ fuel config previous environment ty operands origin
  | fill ty expression origin => exact evalValue_fill_preservesFresh_succ fuel config previous environment ty expression origin
  | structLit ty operands => exact evalValue_structLit_preservesFresh_succ fuel config previous environment ty operands
  | bytes ty bytes origin => exact evalValue_bytes_preservesFresh_succ fuel config previous environment ty bytes origin
  | str ty arguments origin => exact evalValue_str_preservesFresh_succ fuel config previous environment ty arguments origin
  | copy ty source origin => exact evalValue_copy_preservesFresh_succ fuel config previous environment ty source origin
  | resultLocal localVar origin => exact evalValue_resultLocal_preservesFresh_succ fuel config previous environment localVar origin
  | values operands => exact evalValue_values_preservesFresh_succ fuel config previous environment operands

private theorem buildElement_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    PreservesFresh (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  fresh_eval previous

private theorem execWhile_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    PreservesFresh (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  fresh_eval previous

private theorem execRange_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    PreservesFresh (execRange (fuel + 1) config environment var ty first last body) := by
  simp only [execRange]
  fresh_eval previous

private theorem execEach_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) :
    PreservesFresh (execEach (fuel + 1) config environment var index byRef body view current) := by
  simp only [execEach]
  fresh_eval previous

private theorem loopBody_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesFresh (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  fresh_eval previous

private theorem pushValue_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesFresh (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  fresh_eval previous

set_option maxHeartbeats 2000000 in
private theorem evalProduce_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) :
    PreservesFresh (evalProduce (fuel + 1) config environment channels expression) := by
  cases channels with
  | nil =>
      cases expression <;> simp only [evalProduce]
      all_goals fresh_eval previous
  | cons channel channels =>
      cases channels with
      | nil =>
          cases channel <;> cases expression <;> simp only [evalProduce]
          all_goals fresh_eval previous
      | cons second channels =>
          cases expression <;> simp only [evalProduce]
          all_goals fresh_eval previous

set_option maxHeartbeats 2000000 in
private theorem buildExpr_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) :
    PreservesFresh (buildExpr (fuel + 1) config environment destination expression) := by
  cases expression <;> try simp only [buildExpr]
  all_goals fresh_eval previous
  case fill ty expression origin =>
    cases ty <;> simp only [buildExpr]
    all_goals fresh_eval previous
  case values operands =>
    cases operands with
    | nil =>
        simp only [buildExpr]
        fresh_eval previous
    | cons expression operands =>
        cases operands <;> simp only [buildExpr]
        all_goals fresh_eval previous

set_option maxHeartbeats 2000000 in
private theorem execStmt_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (statement : Stmt) :
    PreservesFresh (execStmt (fuel + 1) config environment statement) := by
  cases statement <;> try simp only [execStmt]
  all_goals fresh_eval previous
  case ifS condition yes no origin =>
    cases no <;> simp only [execStmt]
    all_goals fresh_eval previous

private theorem execBlock_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesFresh (execBlock (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execBlock]
  fresh_eval previous

private theorem execResultBlockWith_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesFresh (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execResultBlockWith]
  fresh_eval previous

private theorem invokeCall_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    PreservesFresh (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply preservesFresh_bind
  · exact stateQuery_preservesFresh _ (stateQuery_getImplementation config context)
  · intro implementation
    rcases implementation with ⟨id, implementation⟩
    split
    · fresh_eval previous
    · apply preservesFresh_bind
      · fresh_eval previous
      · intro callableChannels
        apply preservesFresh_bind
        · exact previous.arguments _ _ _ _
        · intro values
          apply preservesFresh_bind
          · exact preservesFresh_get
          · intro state
            split
            · fresh_eval previous
            · apply preservesFresh_allocateActivation
                (make := fun act => ⟨id, act, implementation.vars, [], callableChannels⟩)
                (action := fun activation => do
                  let carriers ← enterActivation fuel config activation
                    ((implementation.params.toList.zip values).map fun item => (item.1.var, item.2))
                    implementation.body origin
                  deliverCarriers fuel config.layout channels carriers origin)
              · intro act; rfl
              · intro activation
                fresh_eval previous

theorem evaluation_preservesFresh (fuel : Nat) (config : EvalConfig) :
    EvaluationPreservesFresh fuel config := by
  induction fuel with
  | zero => exact evaluationPreservesFresh_zero config
  | succ fuel previous =>
      refine {
        value := evalValue_preservesFresh_succ fuel config previous
        bound := evalBound_preservesFresh_succ fuel config previous
        place := evalPlace_preservesFresh_succ fuel config previous
        view := evalView_preservesFresh_succ fuel config previous
        produce := evalProduce_preservesFresh_succ fuel config previous
        operands := evalOperands_preservesFresh_succ fuel config previous
        build := buildExpr_preservesFresh_succ fuel config previous
        element := buildElement_preservesFresh_succ fuel config previous
        arguments := evalArguments_preservesFresh_succ fuel config previous
        call := invokeCall_preservesFresh_succ fuel config previous
        activation := enterActivation_preservesFresh_succ fuel config previous
        activationBody := ?_
        resultBlock := execResultBlock_preservesFresh_succ fuel config previous
        resultBlockWith := execResultBlockWith_preservesFresh_succ fuel config previous
        block := execBlock_preservesFresh_succ fuel config previous
        statements := execStmts_preservesFresh_succ fuel config previous
        statement := execStmt_preservesFresh_succ fuel config previous
        printArgument := evalPrintArg_preservesFresh_succ fuel config previous
        whileLoop := execWhile_preservesFresh_succ fuel config previous
        rangeLoop := execRange_preservesFresh_succ fuel config previous
        eachLoop := execEach_preservesFresh_succ fuel config previous
        loop := loopBody_preservesFresh_succ fuel config previous
        push := pushValue_preservesFresh_succ fuel config previous }
      intro environment pre body
      apply execActivationBody_preservesFresh
      exact execResultBlockWith_preservesFresh_succ fuel config previous environment pre environment.channels body

theorem initGlobals_preservesFresh (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    PreservesFresh (initGlobals fuel config globals) := by
  have previous := evaluation_preservesFresh fuel config
  induction globals with
  | nil => simpa only [initGlobals] using preservesFresh_pure ()
  | cons global globals preserved =>
      simp only [initGlobals]
      fresh_eval previous

theorem runModule_preservesFresh (fuel : Nat) (config : EvalConfig) :
    PreservesFresh (runModule fuel config) := by
  have previous := evaluation_preservesFresh fuel config
  unfold runModule
  apply preservesFresh_bind
  · exact initGlobals_preservesFresh _ _ _
  · intro _
    fresh_eval previous

theorem runModule_freshActivations (fuel : Nat) (config : EvalConfig) :
    FreshActivations (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) :=
  runModule_preservesFresh fuel config .initial freshActivations_initial

theorem runModule_selectedTarget_nearest (fuel : Nat) (config : EvalConfig) (targetId : Nat)
    (activation : RuntimeActivation) (final : ExecutionState)
    (selected : targetActivation config targetId
      (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) = .ok activation final) :
    final = Goose.Proofs.Exit.stepState (runModule fuel config .initial) ∧
    activation.act < final.nextAct ∧
    ∃ target discarded outer,
      config.module.targets[targetId]? = some target ∧
      final.activations = discarded ++ activation :: outer ∧
      target.contains activation.implementation = true ∧
      (∀ earlier ∈ discarded, target.contains earlier.implementation = false) ∧
      (final.activations.map (·.act)).Nodup := by
  obtain ⟨unchanged, target, discarded, outer, declared, shape, member, excluded⟩ :=
    targetActivation_selects_nearest config targetId _ final activation selected
  subst final
  obtain ⟨distinct, allocated⟩ := runModule_freshActivations fuel config
  have present : activation ∈
      (Goose.Proofs.Exit.stepState (runModule fuel config .initial)).activations := by
    rw [shape]
    simp
  exact ⟨rfl, allocated activation present, target, discarded, outer, declared, shape,
    member, excluded, distinct⟩

end Goose.Proofs.ExitExecution
