import Goose.Proofs.ExitExecutionActivationChannelsProduce

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

elab "construction_channels_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

elab "construction_channels_bind" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesActivationChannels do throwError "expected activation channels"
  let action := target.getAppArgs.back!
  unless action.getAppFn.isConstOf ``Bind.bind do throwError "expected bind"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply preservesActivationChannels_bind))

macro "construction_channels_step " fresh:ident channels:ident : tactic => `(tactic|
  first
    | exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedPathRun _)
    | exact preservesActivationChannels_liftExcept _
    | exact preservesActivationChannels_bindRoot _ _
    | assumption
    | (solve | activation_channels_fresh $fresh)
    | activation_channels_conditional
    | with_reducible exact preservesActivationChannels_pure _
    | with_reducible exact preservesActivationChannels_stop _
    | with_reducible exact preservesActivationChannels_get
    | with_reducible exact preservesActivationChannels_freshAct
    | with_reducible exact preservesActivationChannels_freshScope
    | with_reducible exact preservesActivationChannels_fault _
    | with_reducible exact preservesActivationChannels_timeout
    | with_reducible exact preservesActivationChannels_abortAt _ _
    | with_reducible exact preservesActivationChannels_bindStaticRoot _ _
    | with_reducible exact preservesActivationChannels_setObjectOrdinal _ _
    | exact preservesActivationChannels_bindRoot _ _
    | with_reducible apply preservesActivationChannels_liftConstruction
    | with_reducible exact preservesActivationChannels_liftLayout _
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_rootOf _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectInt _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectBool _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectRef _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_sameIntType _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_comparable _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc _ _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_arrayLength _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_getStorage _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_readStoredElement _ _ _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_carrierValue _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_singleCarrier _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_completedDestination _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedDestination _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_receivingLayout _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_getImplementation _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_enclosingActivation _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_targetActivation _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_currentBreak _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ (stateQuery_liftExcept _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ ((rendering_stateQueries _ _).1 _ _)
    | with_reducible exact preservesActivationChannels_of_stateQuery _ ((rendering_stateQueries _ _).2.2.2 _ _)
    | with_reducible apply preservesActivationChannels_bind
    | with_reducible apply preservesActivationChannels_listMapM
    | with_reducible apply preservesActivationChannels_listForIn
    | with_reducible apply preservesActivationChannels_arrayForIn
    | with_reducible apply preservesActivationChannels_rangeForIn
    | with_reducible exact ($channels).value _ _
    | with_reducible exact ($channels).bound _ _ _ _
    | with_reducible exact ($channels).place _ _
    | with_reducible exact ($channels).view _ _
    | with_reducible exact ($channels).produce _ _ _
    | with_reducible exact ($channels).operands _ _ _
    | with_reducible exact ($channels).build _ _ _
    | with_reducible exact ($channels).element _ _ _ _
    | with_reducible exact ($channels).arguments _ _ _ _
    | with_reducible exact ($channels).call _ _ _ _ _
    | with_reducible exact ($channels).activationBody _ _ _
    | with_reducible exact ($channels).resultBlock _ _ _
    | with_reducible exact ($channels).resultBlockWith _ _ _ _
    | with_reducible exact ($channels).block _ _ _ _
    | with_reducible exact ($channels).statements _ _
    | with_reducible exact ($channels).statement _ _
    | with_reducible exact ($channels).printArgument _ _
    | with_reducible exact ($channels).whileLoop _ _ _
    | with_reducible exact ($channels).rangeLoop _ _ _ _ _ _
    | with_reducible exact ($channels).eachLoop _ _ _ _ _ _ _
    | with_reducible exact ($channels).loop _ _ _
    | with_reducible exact ($channels).push _ _ _ _
    | activation_channels_zeta
    | with_reducible rfl
    | with_reducible construction_channels_intro
    | split)

macro "construction_channels_eval " fresh:ident channels:ident : tactic => `(tactic|
  repeat' construction_channels_step $fresh $channels)

local macro "projection_bind " fresh:ident : tactic => `(tactic|
  (apply preservesActivationChannels_bind
   case firstFresh => first
     | exact stateQuery_preservesFresh _ (stateQuery_exitSource _ _ _)
     | exact preservesFresh_landCarrier _ _
     | exact stateQuery_preservesFresh _ (stateQuery_storedPathRun _)
     | (fresh_eval $fresh <;> first | exact stateQuery_preservesFresh _ (stateQuery_exitSource _ _ _) | exact preservesFresh_exitChannelPreparation _ _ _ _ | exact preservesFresh_landCarrier _ _ | skip)))
local macro "projection_arrayForIn " fresh:ident : tactic => `(tactic|
  (apply preservesActivationChannels_arrayForIn
   case fresh => intros; first | exact preservesFresh_landCarrier _ _ | (fresh_eval $fresh <;> first | exact stateQuery_preservesFresh _ (stateQuery_exitSource _ _ _) | exact preservesFresh_exitChannelPreparation _ _ _ _ | exact preservesFresh_landCarrier _ _ | skip)))
local macro "projection_rangeForIn " fresh:ident : tactic => `(tactic|
  (apply preservesActivationChannels_rangeForIn
   case fresh => intros; first | exact preservesFresh_landCarrier _ _ | (fresh_eval $fresh <;> first | exact stateQuery_preservesFresh _ (stateQuery_exitSource _ _ _) | exact preservesFresh_exitChannelPreparation _ _ _ _ | exact preservesFresh_landCarrier _ _ | skip)))

local macro "projection_listMapM " fresh:ident : tactic => `(tactic|
  (apply preservesActivationChannels_listMapM
   case fresh => intros; first | exact preservesFresh_landCarrier _ _ | (fresh_eval $fresh <;> first | exact stateQuery_preservesFresh _ (stateQuery_exitSource _ _ _) | exact preservesFresh_exitChannelPreparation _ _ _ _ | exact preservesFresh_landCarrier _ _ | skip)))
local macro "projection_listForIn " fresh:ident : tactic => `(tactic|
  (apply preservesActivationChannels_listForIn
   case fresh => intros; first | exact preservesFresh_landCarrier _ _ | (fresh_eval $fresh <;> first | exact stateQuery_preservesFresh _ (stateQuery_exitSource _ _ _) | exact preservesFresh_exitChannelPreparation _ _ _ _ | exact preservesFresh_landCarrier _ _ | skip)))

theorem fixed_writes_preserveActivationChannels (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (element : Ty) (origin : Goose.Core.OriginId) (values : Array Value) :
    PreservesActivationChannels (forIn values PUnit.unit fun value _ => do
      let bytes ← liftExcept (fixedBytes fuel layout element value)
      liftConstruction origin (writeElement destination bytes)
      pure (.yield PUnit.unit)) := by
  have fresh0 := evaluationPreservesFresh_zero config
  projection_arrayForIn fresh0
  intro value _
  projection_bind fresh0
  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_liftExcept _)
  · intro bytes
    projection_bind fresh0
    · exact preservesActivationChannels_liftConstruction _ _
    · intro _; exact preservesActivationChannels_pure _

theorem packed_writes_preserveActivationChannels (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (bytes : ByteArray) (run : SampledRun) (start count : Nat) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (forIn ([0:count] : Std.Legacy.Range) PUnit.unit fun index _ => do
      let (low, high) ← liftLayout (elementInterval fuel layout bytes run (start + index))
      liftConstruction origin (writeElement destination (bytes.extract low high))
      pure (.yield PUnit.unit)) := by
  have fresh0 := evaluationPreservesFresh_zero config
  projection_rangeForIn fresh0
  intro index _
  projection_bind fresh0
  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_liftLayout _)
  · intro interval
    rcases interval with ⟨low, high⟩
    simp only
    projection_bind fresh0
    · exact preservesActivationChannels_liftConstruction _ _
    · intro _; exact preservesActivationChannels_pure _

theorem preservesActivationChannels_copyValue (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    PreservesActivationChannels (copyValue fuel layout destination value origin source) := by
  have fresh0 := evaluationPreservesFresh_zero config
  cases fuel with
  | zero => exact preservesActivationChannels_stop _
  | succ fuel =>
      unfold copyValue
      projection_bind fresh0
      · exact preservesActivationChannels_liftConstruction _ _
      · intro current
        projection_bind fresh0
        · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination current)
        · intro pending
          cases elementFound : elementType pending.capability.logicalType with
          | none => exact preservesActivationChannels_stop _
          | some element =>
              cases value with
              | int _ _ | bool _ | unit | record _ _ | ref _ => exact preservesActivationChannels_stop _
              | stored stored =>
                  projection_bind fresh0
                  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored stored)
                  · intro sampled
                    rcases sampled with ⟨bytes, run⟩
                    simp only
                    split
                    · exact preservesActivationChannels_stop _
                    · projection_bind fresh0
                      · exact preservesActivationChannels_liftConstruction _ _
                      · intro _
                        projection_bind fresh0
                        · simpa only [Nat.zero_add] using packed_writes_preserveActivationChannels config fuel layout current bytes run 0 run.count origin
                        · intro _; exact preservesActivationChannels_liftConstruction _ _
              | fixed values =>
                  cases source with
                  | none =>
                      projection_bind fresh0
                      · exact fixed_writes_preserveActivationChannels config fuel layout current element origin values
                      · intro _; exact preservesActivationChannels_liftConstruction _ _
                  | some source =>
                      projection_bind fresh0
                      · exact preservesActivationChannels_liftConstruction _ _
                      · intro _
                        projection_bind fresh0
                        · exact fixed_writes_preserveActivationChannels config fuel layout current element origin values
                        · intro _; exact preservesActivationChannels_liftConstruction _ _
              | slice location start count =>
                  projection_bind fresh0
                  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc fuel layout location)
                  · intro backing
                    cases source with
                    | none => exact preservesActivationChannels_stop _
                    | some source =>
                        cases backing with
                        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ => exact preservesActivationChannels_stop _
                        | stored stored =>
                            projection_bind fresh0
                            · exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedPathRun stored)
                            · intro sampled
                              rcases sampled with ⟨bytes, run⟩
                              simp only
                              split
                              · exact preservesActivationChannels_stop _
                              · split
                                · exact preservesActivationChannels_stop _
                                · projection_bind fresh0
                                  · exact preservesActivationChannels_liftConstruction _ _
                                  · intro _
                                    projection_bind fresh0
                                    · exact packed_writes_preserveActivationChannels config fuel layout current bytes run start count origin
                                    · intro _; exact preservesActivationChannels_liftConstruction _ _
                        | fixed values =>
                            simp only
                            split
                            · exact preservesActivationChannels_stop _
                            · projection_bind fresh0
                              · exact preservesActivationChannels_liftConstruction _ _
                              · intro _
                                projection_bind fresh0
                                · exact fixed_writes_preserveActivationChannels config fuel layout current element origin (values.extract start (start + count))
                                · intro _; exact preservesActivationChannels_liftConstruction _ _

theorem preservesActivationChannels_bindAll (config : EvalConfig) (act : Goose.Core.ActId)
    (scopeInst : Goose.Core.ScopeInst) (values : List (Goose.Core.VarId × Value)) :
    PreservesActivationChannels (bindAll act scopeInst values) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold bindAll
  projection_bind fresh0
  · projection_listForIn fresh0
    intro entry accumulator
    rcases entry with ⟨localVar, value⟩
    projection_bind fresh0
    · exact preservesActivationChannels_bindRoot _ _
    · intro ignored
      exact preservesActivationChannels_pure _
  · intro ignored
    exact preservesActivationChannels_pure _

theorem preservesActivationChannels_materializeNamedCarriers (config : EvalConfig) (origin : Goose.Core.OriginId)
    (carriers : List Carrier) :
    PreservesActivationChannels (materializeNamedCarriers origin carriers) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold materializeNamedCarriers
  projection_listMapM fresh0
  intro carrier
  cases carrier with
  | register value => exact preservesActivationChannels_pure _
  | completed id => exact preservesActivationChannels_pure _
  | pendingNamed token =>
      projection_bind fresh0
      · exact preservesActivationChannels_liftConstruction _ _
      · intro id; exact preservesActivationChannels_pure _

theorem preservesActivationChannels_materializeOwnedCarriers (config : EvalConfig) (origin : Goose.Core.OriginId)
    (tokens : List ExitReservationId) (carriers : List Carrier) :
    PreservesActivationChannels (materializeOwnedCarriers origin tokens carriers) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold materializeOwnedCarriers
  projection_listMapM fresh0
  intro carrier
  cases carrier with
  | register value => exact preservesActivationChannels_pure _
  | completed id => exact preservesActivationChannels_pure _
  | pendingNamed token =>
      by_cases owns : tokens.contains token = true
      · simp only [owns]
        projection_bind fresh0
        · exact preservesActivationChannels_liftConstruction _ _
        · intro id; exact preservesActivationChannels_pure _
      · simp only [owns]
        exact preservesActivationChannels_pure _

theorem preservesActivationChannels_ownerDestination (config : EvalConfig) (layout : LayoutEnv) (stored : StoredValue)
    (request : Goose.Core.ConstructionRequest) (count : Option Nat) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (ownerDestination layout stored request count origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold ownerDestination
  cases stored.destination with
  | none => exact preservesActivationChannels_newDestination _ _ _ _ _ _ _
  | some id =>
      projection_bind fresh0
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination id)
      · intro destination
        cases destination.progress <;> first
          | exact preservesActivationChannels_liftConstruction _ _
          | exact preservesActivationChannels_newDestination _ _ _ _ _ _ _
          | exact preservesActivationChannels_stop _

theorem preservesActivationChannels_publishOwner (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (publishOwner fuel layout location stored id origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  cases fuel with
  | zero => exact preservesActivationChannels_stop _
  | succ fuel =>
      unfold publishOwner
      projection_bind fresh0
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => exact preservesActivationChannels_stop _
        | child parent =>
            projection_bind fresh0
            · exact preservesActivationChannels_liftConstruction _ _
            · intro _
              projection_bind fresh0
              · exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedDestination parent)
              · intro value; exact preservesActivationChannels_writeLoc fuel layout location _
        | receiver =>
            projection_bind fresh0
            · exact preservesActivationChannels_publishCarriers _ _
            · intro _
              projection_bind fresh0
              · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getStorage stored.storage)
              · intro receiving; exact preservesActivationChannels_writeLoc fuel layout location _

theorem preservesActivationChannels_repeatElement (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv) (parent : Goose.Core.DestinationId)
    (element : Ty) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (repeatElement fuel layout parent element source origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  cases fuel with
  | zero => exact preservesActivationChannels_stop _
  | succ fuel =>
      unfold repeatElement
      projection_bind fresh0
      · exact preservesActivationChannels_liftConstruction _ _
      · intro current
        projection_bind fresh0
        · exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedDestination source)
        · intro stored
          projection_bind fresh0
          · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getStorage stored.storage)
          · intro storage
            projection_bind fresh0
            · exact preservesActivationChannels_of_stateQuery _ (stateQuery_liftLayout _)
            · intro finish
              projection_bind fresh0
              · exact preservesActivationChannels_liftConstruction _ _
              · intro _; exact preservesActivationChannels_liftConstruction _ _

theorem preservesActivationChannels_landCarrier (config : EvalConfig) (origin : Goose.Core.OriginId) (carrier : Carrier) :
    PreservesActivationChannels (landCarrier origin carrier) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold landCarrier
  cases carrier with
  | register value => exact preservesActivationChannels_pure _
  | pendingNamed token => exact preservesActivationChannels_stop _
  | completed id =>
      projection_bind fresh0
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => exact preservesActivationChannels_liftConstruction _ _
        | receiver | child parent => exact preservesActivationChannels_pure _

theorem preservesActivationChannels_landCarriers (config : EvalConfig) (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesActivationChannels (landCarriers origin carriers) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold landCarriers
  projection_bind fresh0
  · projection_listForIn fresh0
    intro carrier _
    projection_bind fresh0
    · exact preservesActivationChannels_landCarrier config origin carrier
    · intro _; exact preservesActivationChannels_pure _
  · intro _; exact preservesActivationChannels_pure _

theorem preservesActivationChannels_openElementReceiving (config : EvalConfig) (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (location : Goose.Core.Loc) (stored : StoredValue) (element : Ty) (known : Option Nat)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (openElementReceiving layout owner location stored element known origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold openElementReceiving
  projection_bind fresh0
  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored stored)
  · intro sampled
    rcases sampled with ⟨bytes, run⟩
    projection_bind fresh0
    · exact preservesActivationChannels_of_stateQuery _ (stateQuery_receivingLayout layout element)
    · intro receiving
      cases stored.destination with
      | none => exact preservesActivationChannels_liftConstruction _ _
      | some id =>
          projection_bind fresh0
          · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination id)
          · intro pending
            cases pending.progress <;> first
              | exact preservesActivationChannels_liftConstruction _ _
              | exact preservesActivationChannels_stop _

theorem preservesActivationChannels_publishElementReceiving (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (stored : StoredValue) (destination : Goose.Core.DestinationId)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (publishElementReceiving fuel layout location stored destination origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  cases fuel with
  | zero => exact preservesActivationChannels_stop _
  | succ fuel =>
      unfold publishElementReceiving
      projection_bind fresh0
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination destination)
      · intro pending
        cases pending.use with
        | replacement _ => exact preservesActivationChannels_stop _
        | child parent =>
            projection_bind fresh0
            · exact preservesActivationChannels_liftConstruction _ _
            · intro _
              projection_bind fresh0
              · exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedDestination parent)
              · intro value; exact preservesActivationChannels_writeLoc _ _ _ _
        | receiver =>
            projection_bind fresh0
            · exact preservesActivationChannels_liftConstruction _ _
            · intro _
              projection_bind fresh0
              · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getStorage stored.storage)
              · intro value; exact preservesActivationChannels_writeLoc _ _ _ _

theorem preservesActivationChannels_appendFixedValues (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (values : List Value) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (appendFixedValues fuel layout location values origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  cases fuel with
  | zero => exact preservesActivationChannels_stop _
  | succ fuel =>
      unfold appendFixedValues
      projection_bind fresh0
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesActivationChannels_stop _
        | stored stored =>
            simp only
            cases elementFound : elementType stored.ty with
            | none => exact preservesActivationChannels_stop _
            | some element =>
                projection_bind fresh0
                · projection_listMapM fresh0
                  intro value; exact preservesActivationChannels_of_stateQuery _ (stateQuery_liftExcept _)
                · intro parts
                  projection_bind fresh0
                  · exact preservesActivationChannels_ownerDestination config _ _ _ _ _
                  · intro destination
                    projection_bind fresh0
                    · projection_listForIn fresh0
                      intro bytes state
                      projection_bind fresh0
                      · exact preservesActivationChannels_liftConstruction _ _
                      · intro _; exact preservesActivationChannels_pure _
                    · intro _
                      projection_bind fresh0
                      · exact preservesActivationChannels_liftConstruction _ _
                      · intro _
                        projection_bind fresh0
                        · exact preservesActivationChannels_of_stateQuery _ (stateQuery_completedDestination destination)
                        · intro completed; exact preservesActivationChannels_publishOwner config _ _ _ _ _ _

theorem preservesActivationChannels_appendRun (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (view : RuntimeView) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (appendRun fuel layout location view origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  cases fuel with
  | zero => exact preservesActivationChannels_stop _
  | succ fuel =>
      unfold appendRun
      projection_bind fresh0
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesActivationChannels_stop _
        | stored stored =>
            projection_bind fresh0
            · exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc fuel layout view.location)
            · intro source
              projection_bind fresh0
              · exact preservesActivationChannels_ownerDestination config _ _ _ _ _
              · intro destination
                have finish : PreservesActivationChannels (do
                    liftConstruction origin (finishDestination destination)
                    let completed ← completedDestination destination
                    publishOwner fuel layout location stored completed origin) := by
                  projection_bind fresh0
                  · exact preservesActivationChannels_liftConstruction _ _
                  · intro _
                    projection_bind fresh0
                    · exact preservesActivationChannels_of_stateQuery _ (stateQuery_completedDestination destination)
                    · intro completed; exact preservesActivationChannels_publishOwner config _ _ _ _ _ _
                cases source with
                | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ =>
                    projection_bind fresh0
                    · exact preservesActivationChannels_stop _
                    · intro _; exact finish
                | stored source =>
                      projection_bind fresh0
                      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored source)
                      · intro sampled
                        rcases sampled with ⟨bytes, run⟩
                        projection_bind fresh0
                        · exact preservesActivationChannels_liftConstruction _ _
                        · intro _
                          projection_bind fresh0
                          · exact packed_writes_preserveActivationChannels config fuel layout destination bytes run view.start view.count origin
                          · intro _; exact finish
                | fixed values =>
                      simp only
                      cases elementFound : elementType stored.ty with
                      | none =>
                          projection_bind fresh0
                          · exact preservesActivationChannels_stop _
                          · intro _; exact finish
                      | some element =>
                        projection_bind fresh0
                        ·
                          projection_rangeForIn fresh0
                          intro index current
                          split
                          · projection_bind fresh0
                            · exact preservesActivationChannels_of_stateQuery _ (stateQuery_liftExcept _)
                            · intro bytes
                              projection_bind fresh0
                              · exact preservesActivationChannels_liftConstruction _ _
                              · intro _; exact preservesActivationChannels_pure _
                          · projection_bind fresh0
                            · exact preservesActivationChannels_stop _
                            · intro _; exact preservesActivationChannels_pure _
                        · intro _; exact finish

theorem preservesActivationChannels_materializeProducer (config : EvalConfig) (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (preserved : PreservesActivationChannels evaluate) (freshAction : PreservesFresh evaluate) :
    PreservesActivationChannels (materializeProducer fuel declarations expression evaluate)  := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold materializeProducer
  split
  · exact preservesActivationChannels_pure _
  · apply preservesActivationChannels_bind _ _ preserved freshAction

    · intro value
      cases value <;> first | exact preservesActivationChannels_pure _ | exact preservesActivationChannels_stop _

theorem preservesActivationChannels_materializedDestination (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv)
    (owner : Goose.Core.ActId) (ty : Ty) (origin : Goose.Core.OriginId)
    (count : Nat) (value : Value) :
    PreservesActivationChannels (materializedDestination fuel layout owner ty origin count value)  := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold materializedDestination
  projection_bind fresh0
  · exact preservesActivationChannels_newDestination _ _ _ _ _ _ _
  · intro destination
    projection_bind fresh0
    · exact preservesActivationChannels_copyValue config _ _ _ _ _ _
    · intro ignored
      exact preservesActivationChannels_completedReceivingDestination _


private theorem activationChannels_cleanupResult (expected : List Goose.Proofs.ConstructionExecutionOwnership.OwnershipActivationChannels)
    (cleanup : EvalM Unit) (resume : ExecutionState → ExecutionStep α)
    (preserved : PreservesActivationChannels cleanup) (state : ExecutionState)
    (fresh : FreshActivations state)
    (before : ActivationChannelsProjection state = expected)
    (continued : ∀ final, ActivationChannelsProjection final = expected → ActivationChannelsOutcome expected (resume final)) :
    ActivationChannelsOutcome expected (match cleanup state with
      | .ok () final => resume final
      | .stop reason final => .stop reason final
      | .escape address carriers final => .escape address carriers final
      | .jump target kind final => .jump target kind final) := by
  have checked := preserved state fresh
  cases result : cleanup state with
  | stop reason final => exact True.intro
  | ok value final =>
    cases value
    have equal : ActivationChannelsProjection final = expected := by
      exact (show ActivationChannelsProjection final = ActivationChannelsProjection state from
        by simpa [ActivationChannelsOutcome, result] using checked).trans before
    exact continued final equal
  | escape address carriers final | jump target kind final =>
    have equal : ActivationChannelsProjection final = expected := by
      exact (show ActivationChannelsProjection final = ActivationChannelsProjection state from
        by simpa [ActivationChannelsOutcome, result] using checked).trans before
    exact equal

theorem preservesActivationChannels_withCompletionChannels (config : EvalConfig)
    (channels : List Channel) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier))
    (body : ∀ planned, PreservesActivationChannels (action planned))
    (bodyFresh : ∀ planned, PreservesFresh (action planned)) :
    PreservesActivationChannels (withCompletionChannels channels origin action) := by
  have fresh0 := evaluationPreservesFresh_zero config
  let setup : EvalM (List Channel × List ExitReservationId) := do
    let planned ← channels.mapM fun channel => match channel with
      | .construct incoming => do
          let token ← liftConstruction origin (waitExitDestination incoming)
          pure (Channel.completion token, some token)
      | .register ty => pure (Channel.register ty, none)
      | .completion _ => fault .flow
    pure (planned.map Prod.fst, planned.filterMap Prod.snd)
  have setupPreserved : PreservesActivationChannels setup := by
    unfold setup
    projection_bind fresh0
    · projection_listMapM fresh0
      intro channel
      cases channel <;> repeat' first
        | exact preservesActivationChannels_pure _
        | exact preservesActivationChannels_stop _
        | exact preservesActivationChannels_liftConstruction _ _
        | projection_bind fresh0
        | intro
    · intro ignored
      exact preservesActivationChannels_pure _
  have setupFresh : PreservesFresh setup := by
    unfold setup
    fresh_eval fresh0
  intro state fresh
  unfold withCompletionChannels
  change ActivationChannelsOutcome (ActivationChannelsProjection state) (match setup state with
    | .ok (planned, tokens) prepared => _
    | .stop reason final => .stop reason final
    | .escape address carriers final => .escape address carriers final
    | .jump target kind final => .jump target kind final)
  have preparedChannels := setupPreserved state fresh
  have preparedFresh := setupFresh state fresh
  cases prepared : setup state with
  | stop reason after => exact True.intro
  | escape address carriers after | jump target kind after =>
    simpa [ActivationChannelsOutcome, prepared] using preparedChannels
  | ok pair after =>
    rcases pair with ⟨planned, tokens⟩
    have afterChannels : ActivationChannelsProjection after = ActivationChannelsProjection state := by
      simpa [ActivationChannelsOutcome, prepared] using preparedChannels
    have afterFresh : FreshActivations after := by
      simpa [Goose.Proofs.Exit.stepState, prepared] using preparedFresh
    let evaluatedAction := do materializeOwnedCarriers origin tokens (← action planned)
    have evaluatedPreserved : PreservesActivationChannels evaluatedAction := by
      apply preservesActivationChannels_bind _ _ (body planned) (bodyFresh planned)
      exact preservesActivationChannels_materializeOwnedCarriers config origin tokens
    have evaluatedFreshness : PreservesFresh evaluatedAction := by
      apply preservesFresh_bind _ _ (bodyFresh planned)
      exact preservesFresh_materializeOwnedCarriers origin tokens
    have evaluatedChannels := evaluatedPreserved after afterFresh
    have evaluatedFresh := evaluatedFreshness after afterFresh
    cases evaluated : evaluatedAction after
    all_goals simp only [evaluated, ActivationChannelsOutcome] at evaluatedChannels
    all_goals simp only [evaluated, Goose.Proofs.Exit.stepState] at evaluatedFresh
    all_goals have evaluatedResult := evaluated
    all_goals dsimp only [evaluatedAction] at evaluatedResult
    all_goals simp only [evaluatedResult]
    case stop reason final =>
      change ActivationChannelsOutcome (ActivationChannelsProjection state)
        (match Goose.Proofs.ConstructionExecutionOwnership.ownershipChannelCleanup origin tokens.reverse false [] final with
        | .ok () cleaned => .stop reason cleaned
        | .stop reason cleaned => .stop reason cleaned
        | .escape address carriers cleaned => .escape address carriers cleaned
        | .jump target kind cleaned => .jump target kind cleaned)
      obtain ⟨cleaned, completed | ⟨stopped, failed⟩⟩ :=
        Goose.Proofs.ConstructionExecutionOwnership.ownershipChannelCleanup_control origin tokens.reverse false [] final
      · simp [completed, ActivationChannelsOutcome]
      · simp [failed, ActivationChannelsOutcome]
    all_goals
      apply activationChannels_cleanupResult
      · simp only [Bool.false_eq_true, ↓reduceIte]
        projection_bind fresh0
        · projection_listForIn fresh0
          intro token accumulator
          repeat' first
            | exact preservesActivationChannels_pure _
            | exact preservesActivationChannels_liftConstruction _ _
            | projection_bind fresh0
            | intro
        · intro ignored
          exact preservesActivationChannels_pure _
      · exact evaluatedFresh
      · first | exact evaluatedChannels.trans afterChannels | rfl
      · intros final equal
        exact equal

private theorem preservesActivationChannels_restoreOwnerRow (snapshot : PendingDestination) :
    PreservesActivationChannels (do
      let state ← EvalM.get
      EvalM.set { state with construction := { state.construction with
        destinations := state.construction.destinations.set! snapshot.capability.id snapshot } }) := by
  apply preservesActivationChannels_stateUpdate
  intro state
  rfl

theorem preservesActivationChannels_restoreCompletedOwner (config : EvalConfig)
    (snapshot : PendingDestination) (incoming : Goose.Core.DestinationId)
    (carried : List Goose.Core.DestinationId) :
    PreservesActivationChannels (restoreCompletedOwner snapshot incoming carried) := by
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  unfold restoreCompletedOwner
  repeat' first
    | exact preservesActivationChannels_restoreOwnerRow _
    | exact preservesActivationChannels_receivingDestination _
    | construction_channels_step fresh0 channels0

private theorem preservesActivationChannels_ownerExtensionGuarded (config : EvalConfig) (snapshot : Option PendingDestination)
    (destination : Goose.Core.DestinationId) (action : Goose.Core.DestinationId → EvalM α)
    (body : PreservesActivationChannels (action destination))
    (actionFresh : PreservesFresh (action destination)) :
    PreservesActivationChannels (fun state =>
      let finish := fun (carriers : List Carrier)
          (result : ExecutionState → ExecutionStep α) (state' : ExecutionState) =>
        match snapshot with
        | none => result state'
        | some parent =>
            match restoreCompletedOwner parent destination (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) state' with
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
  have checked := body state fresh
  have checkedFresh := actionFresh state fresh
  dsimp only
  cases result : action destination state with
  | ok value final => simpa [ActivationChannelsOutcome, result] using checked
  | stop reason final => exact True.intro
  | escape address carriers final =>
    have before : ActivationChannelsProjection final = ActivationChannelsProjection state := by
      simpa [ActivationChannelsOutcome, result] using checked
    have finalFresh : FreshActivations final := by
      simpa [Goose.Proofs.Exit.stepState, result] using checkedFresh
    cases snapshot with
    | none => exact before
    | some parent =>
      apply activationChannels_cleanupResult
      · exact preservesActivationChannels_restoreCompletedOwner config _ _ _
      · exact finalFresh
      · exact before
      · intros cleaned equal; exact equal
  | jump target kind final =>
    have before : ActivationChannelsProjection final = ActivationChannelsProjection state := by
      simpa [ActivationChannelsOutcome, result] using checked
    have finalFresh : FreshActivations final := by
      simpa [Goose.Proofs.Exit.stepState, result] using checkedFresh
    cases snapshot with
    | none => exact before
    | some parent =>
      apply activationChannels_cleanupResult
      · exact preservesActivationChannels_restoreCompletedOwner config _ _ _
      · exact finalFresh
      · exact before
      · intros cleaned equal; exact equal

theorem preservesActivationChannels_withOwnerExtension (config : EvalConfig) (stored : StoredValue) (allocate : EvalM Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → EvalM α) (allocation : PreservesActivationChannels allocate)
    (body : ∀ destination, PreservesActivationChannels (action destination))
    (allocateFresh : PreservesFresh allocate)
    (actionFresh : ∀ destination, PreservesFresh (action destination)) :
    PreservesActivationChannels (withOwnerExtension stored allocate action)  := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold withOwnerExtension
  cases stored.destination with
  | none =>
    simp only [bind, pure]
    apply preservesActivationChannels_bind
    case firstFresh => first | exact allocateFresh | fresh_eval fresh0
    · exact allocation
    · intro destination
      exact preservesActivationChannels_ownerExtensionGuarded config none destination action (body destination) (actionFresh destination)
  | some id =>
    simp only [bind, pure]
    projection_bind fresh0
    · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination id)
    · intro parent
      projection_bind fresh0
      · exact allocation
      · intro destination
        exact preservesActivationChannels_ownerExtensionGuarded config
          (match parent.progress with | .built _ => some parent | _ => none)
          destination action (body destination) (actionFresh destination)



theorem preservesActivationChannels_exitChannelPreparation (config : EvalConfig) (source activation : RuntimeActivation)
    (origin : Goose.Core.OriginId) (channel : Channel × Expr) :
    PreservesActivationChannels (exitChannelPreparation source activation origin channel) := by
  have fresh0 := evaluationPreservesFresh_zero config
  rcases channel with ⟨channel, operand⟩
  cases channel with
  | register ty => exact preservesActivationChannels_pure _
  | construct incoming =>
      unfold exitChannelPreparation
      projection_bind fresh0
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_exitSource source incoming operand)
      · intro kind
        projection_bind fresh0
        · exact preservesActivationChannels_liftConstruction _ _
        · intro _; exact preservesActivationChannels_pure _
  | completion token =>
      unfold exitChannelPreparation
      projection_bind fresh0
      · exact preservesActivationChannels_get
      · intro state
        cases present : state.construction.exitReservations[token]? with
        | none => exact preservesActivationChannels_stop _
        | some reservation =>
            cases reservation with
            | waiting incoming => exact preservesActivationChannels_pure _
            | active role incoming selected snapshot =>
                projection_bind fresh0
                · exact preservesActivationChannels_receivingDestination selected
                · intro current
                  projection_bind fresh0
                  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_exitSource source current operand)
                  · intro kind
                    projection_bind fresh0
                    · exact preservesActivationChannels_liftConstruction _ _
                    · intro _; exact preservesActivationChannels_pure _
            | restored | released => exact preservesActivationChannels_stop _

theorem preservesActivationChannels_exitChannels (config : EvalConfig) (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : PreservesActivationChannels (exitChannels source activation operands origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold exitChannels
  split
  · exact preservesActivationChannels_stop _
  · projection_listMapM fresh0
    intro item
    exact preservesActivationChannels_exitChannelPreparation config source activation origin item

private theorem preservesActivationChannels_ownershipExitCleanup (config : EvalConfig)
    (origin : Goose.Core.OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (cancel : Bool) (carriers : List Carrier) :
    PreservesActivationChannels
      (Goose.Proofs.ConstructionExecutionOwnership.ownershipExitCleanup origin borrowed tokens cancel carriers) := by
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  unfold Goose.Proofs.ConstructionExecutionOwnership.ownershipExitCleanup
  construction_channels_eval fresh0 channels0

private theorem activationChannels_finishOwnershipExitChannels (config : EvalConfig)
    (expected : List Goose.Proofs.ConstructionExecutionOwnership.OwnershipActivationChannels)
    (origin : Goose.Core.OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (result : ExecutionStep (List Carrier))
    (before : ActivationChannelsOutcome expected result)
    (fresh : FreshActivations (Goose.Proofs.Exit.stepState result)) :
    ActivationChannelsOutcome expected
      (Goose.Proofs.ConstructionExecutionOwnership.finishOwnershipExitChannels origin borrowed tokens result) := by
  cases result with
  | stop reason state =>
    obtain ⟨final, completed | ⟨stopped, failed⟩⟩ :=
      Goose.Proofs.ConstructionExecutionOwnership.ownershipExitCleanup_control origin borrowed tokens false [] state
    · simp [Goose.Proofs.ConstructionExecutionOwnership.finishOwnershipExitChannels,
        Goose.Proofs.ConstructionExecutionOwnership.runOwnershipExitContinuation,
        Goose.Proofs.ConstructionExecutionOwnership.OwnershipChannelResult.cancel,
        Goose.Proofs.ConstructionExecutionOwnership.OwnershipChannelResult.carriers,
        Goose.Proofs.ConstructionExecutionOwnership.OwnershipChannelResult.emit, completed, ActivationChannelsOutcome]
    · simp [Goose.Proofs.ConstructionExecutionOwnership.finishOwnershipExitChannels,
        Goose.Proofs.ConstructionExecutionOwnership.runOwnershipExitContinuation,
        Goose.Proofs.ConstructionExecutionOwnership.OwnershipChannelResult.cancel,
        Goose.Proofs.ConstructionExecutionOwnership.OwnershipChannelResult.carriers,
        failed, ActivationChannelsOutcome]
  | ok carriers state | escape address carriers state | jump target kind state =>
    simp only [Goose.Proofs.ConstructionExecutionOwnership.finishOwnershipExitChannels,
      Goose.Proofs.ConstructionExecutionOwnership.runOwnershipExitContinuation,
      Goose.Proofs.ConstructionExecutionOwnership.OwnershipChannelResult.cancel,
      Goose.Proofs.ConstructionExecutionOwnership.OwnershipChannelResult.carriers,
      Goose.Proofs.ConstructionExecutionOwnership.OwnershipChannelResult.emit]
    apply activationChannels_cleanupResult
    · exact preservesActivationChannels_ownershipExitCleanup config _ _ _ _ _
    · exact fresh
    · exact before
    · intros final equal; exact equal

theorem preservesActivationChannels_withExitChannels (config : EvalConfig)
    (source activation : RuntimeActivation) (operands : List Expr) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier))
    (body : ∀ planned, PreservesActivationChannels (action planned))
    (bodyFresh : ∀ planned, PreservesFresh (action planned)) :
    PreservesActivationChannels (withExitChannels source activation operands origin action) := by
  intro state fresh
  rw [Goose.Proofs.ConstructionExecutionOwnership.withExitChannels_ownership_continuation]
  have setupChannels := preservesActivationChannels_exitChannels config source activation operands origin state fresh
  have setupFresh := preservesFresh_exitChannels source activation operands origin state fresh
  cases prepared : exitChannels source activation operands origin state with
  | stop reason after => exact True.intro
  | escape address carriers after | jump target kind after =>
    simpa [ActivationChannelsOutcome, prepared] using setupChannels
  | ok channels after =>
    have afterChannels : ActivationChannelsProjection after = ActivationChannelsProjection state := by
      simpa [ActivationChannelsOutcome, prepared] using setupChannels
    have afterFresh : FreshActivations after := by
      simpa [Goose.Proofs.Exit.stepState, prepared] using setupFresh
    let tokens := Goose.Proofs.ConstructionExecutionOwnership.newOwnershipExitTokens state.construction.exitReservations.size after
    let evaluatedAction := do materializeOwnedCarriers origin tokens (← action channels)
    have actionChannels : PreservesActivationChannels evaluatedAction := by
      apply preservesActivationChannels_bind _ _ (body channels) (bodyFresh channels)
      exact preservesActivationChannels_materializeOwnedCarriers config origin tokens
    have actionFresh : PreservesFresh evaluatedAction := by
      apply preservesFresh_bind _ _ (bodyFresh channels)
      exact preservesFresh_materializeOwnedCarriers origin tokens
    apply activationChannels_finishOwnershipExitChannels config
    · change ActivationChannelsOutcome (ActivationChannelsProjection state) (evaluatedAction after)
      have checked := actionChannels after afterFresh
      cases result : evaluatedAction after with
      | stop reason final => exact True.intro
      | ok value final | escape address carriers final | jump target kind final =>
        have equal : ActivationChannelsProjection final = ActivationChannelsProjection after := by
          simpa [ActivationChannelsOutcome, result] using checked
        exact equal.trans afterChannels
    · exact actionFresh after afterFresh

theorem preservesActivationChannels_returned (activation : Goose.Core.ActId) (carriers : List Carrier) :
    PreservesActivationChannels (returned (α := α) activation carriers) := by
  intro state fresh
  rfl

theorem preservesActivationChannels_escaped (address : ExitAddress) (carriers : List Carrier) :
    PreservesActivationChannels (escaped (α := α) address carriers) := by
  intro state fresh
  rfl

theorem preservesActivationChannels_jump (target : Nat) (kind : JumpKind) :
    PreservesActivationChannels (jump (α := α) target kind) := by
  intro state fresh
  rfl

theorem preservesActivationChannels_emitStdout (bytes : ByteArray) :
    PreservesActivationChannels (emitStdout bytes) :=
  preservesActivationChannels_liftConstruction _ _

theorem preservesActivationChannels_deliverCarriers (config : EvalConfig) (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (deliverCarriers fuel layout channels carriers origin) := by
  have fresh0 := evaluationPreservesFresh_zero config
  unfold deliverCarriers
  split
  · exact preservesActivationChannels_stop _
  · projection_listMapM fresh0
    intro item
    rcases item with ⟨channel, carrier⟩
    cases channel <;> cases carrier <;> first
      | exact preservesActivationChannels_pure _
      | exact preservesActivationChannels_stop _
      | (projection_bind fresh0
         · exact preservesActivationChannels_copyValue config _ _ _ _ _ _
         · intro _
           projection_bind fresh0
           · exact preservesActivationChannels_completedReceivingDestination _
           · intro _; exact preservesActivationChannels_pure _)

elab "construction_channels_wrapper " config:ident : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesActivationChannels do throwError "expected activation channels"
  let action := target.getAppArgs.back!
  let some name := action.getAppFn.constName? | throwError "expected helper"
  let tactic ← match name with
    | ``withExitChannels => `(tactic| apply preservesActivationChannels_withExitChannels $config)
    | ``withOwnerExtension => `(tactic| apply preservesActivationChannels_withOwnerExtension $config)
    | ``withCompletionChannels => `(tactic| apply preservesActivationChannels_withCompletionChannels $config)
    | ``materializeProducer => `(tactic| apply preservesActivationChannels_materializeProducer $config)
    | ``protectDestination => `(tactic| apply preservesActivationChannels_protectDestination $config)
    | ``withScope => `(tactic| apply preservesActivationChannels_withScope)
    | ``withBreakTarget => `(tactic| apply preservesActivationChannels_withBreakTarget)
    | ``constructLocal => `(tactic| apply preservesActivationChannels_constructLocal)
    | _ => throwError "expected helper"
  Lean.Elab.Tactic.evalTactic tactic

macro "activation_channels_construction_eval " fresh:ident channels:ident config:ident : tactic => `(tactic|
  repeat' first
    | with_reducible exact preservesActivationChannels_pure _
    | with_reducible exact preservesActivationChannels_stop _
    | construction_channels_bind
    | (solve | activation_channels_fresh $fresh)
    | construction_channels_intro
    | with_reducible exact ($channels).value _ _
    | with_reducible exact ($channels).bound _ _ _ _
    | with_reducible exact ($channels).place _ _
    | with_reducible exact ($channels).view _ _
    | with_reducible exact ($channels).produce _ _ _
    | with_reducible exact ($channels).operands _ _ _
    | with_reducible exact ($channels).build _ _ _
    | with_reducible exact ($channels).element _ _ _ _
    | with_reducible exact ($channels).arguments _ _ _ _
    | with_reducible exact ($channels).call _ _ _ _ _
    | with_reducible exact ($channels).activationBody _ _ _
    | with_reducible exact ($channels).resultBlock _ _ _
    | with_reducible exact ($channels).resultBlockWith _ _ _ _
    | with_reducible exact ($channels).block _ _ _ _
    | with_reducible exact ($channels).statements _ _
    | with_reducible exact ($channels).statement _ _
    | with_reducible exact ($channels).printArgument _ _
    | with_reducible exact ($channels).whileLoop _ _ _
    | with_reducible exact ($channels).rangeLoop _ _ _ _ _ _
    | with_reducible exact ($channels).eachLoop _ _ _ _ _ _ _
    | with_reducible exact ($channels).loop _ _ _
    | with_reducible exact ($channels).push _ _ _ _
    | activation_channels_conditional
    | exact preservesActivationChannels_returned _ _
    | exact preservesActivationChannels_escaped _ _
    | exact preservesActivationChannels_jump _ _
    | exact preservesActivationChannels_emitStdout _
    | exact preservesActivationChannels_copyValue $config _ _ _ _ _ _
    | exact preservesActivationChannels_bindAll $config _ _ _
    | exact preservesActivationChannels_materializeNamedCarriers $config _ _
    | exact preservesActivationChannels_materializeOwnedCarriers $config _ _ _
    | exact preservesActivationChannels_ownerDestination $config _ _ _ _ _
    | exact preservesActivationChannels_publishOwner $config _ _ _ _ _ _
    | exact preservesActivationChannels_repeatElement $config _ _ _ _ _ _
    | exact preservesActivationChannels_landCarrier $config _ _
    | exact preservesActivationChannels_landCarriers $config _ _
    | exact preservesActivationChannels_openElementReceiving $config _ _ _ _ _ _ _
    | exact preservesActivationChannels_publishElementReceiving $config _ _ _ _ _ _
    | exact preservesActivationChannels_appendFixedValues $config _ _ _ _ _
    | exact preservesActivationChannels_appendRun $config _ _ _ _ _
    | exact preservesActivationChannels_materializedDestination $config _ _ _ _ _ _ _
    | exact preservesActivationChannels_reserveRootObject _
    | exact preservesActivationChannels_newDestination _ _ _ _ _ _ _
    | exact preservesActivationChannels_channelsFor _ _ _ _
    | exact preservesActivationChannels_publishCarriers _ _
    | exact preservesActivationChannels_receivingDestination _
    | exact preservesActivationChannels_completedReceivingDestination _
    | exact preservesActivationChannels_selectCompletionChannel _ _ _
    | exact preservesActivationChannels_truncateOwner _ _ _ _ _
    | exact preservesActivationChannels_writeLoc _ _ _ _
    | exact preservesActivationChannels_prepareNamedCarrierAt $config _ _ _ _
    | exact preservesActivationChannels_prepareNamedCarrier $config _ _ _
    | exact preservesActivationChannels_landCarriersInto $config _ _ _
    | exact preservesActivationChannels_receivingAction _ _ _
    | construction_channels_wrapper $config
    | construction_channels_step $fresh $channels)

end Goose.Proofs.ExitExecution
