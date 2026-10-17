import Goose.Construct.Eval
import Goose.Proofs.Exit
import Init.Data.List.Monadic
import Init.Data.Range.Lemmas

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
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

def StateQuery (action : EvalM α) : Prop :=
  ∀ state, Goose.Proofs.Exit.stepState (action state) = state

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

theorem stateQuery_currentBreak (act : Goose.Core.ActId) (scope : Option BreakScope) :
    StateQuery (currentBreak act scope) := by
  unfold currentBreak
  apply stateQuery_bind
  · exact stateQuery_get
  · intro state
    split
    · exact stateQuery_pure _
    · exact stateQuery_stop _

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

end Goose.Proofs.ConstructionExecutionProtocol
