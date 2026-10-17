import Goose.GIR.Effects
import Goose.Core.Demand

namespace Goose.GIR

open Goose.Core

namespace ReplacementContentFlow.Model

inductive Atom
  | local (slot : SlotId)
  | global (global : GlobalId)
  | param (parameter : Nat)
  | contents (parameter : Nat)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

inductive Roots
  | pending
  | known (roots : List Atom)
  | unknown
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

def Roots.join : Roots → Roots → Roots
  | .unknown, _ | _, .unknown => .unknown
  | .pending, roots | roots, .pending => roots
  | .known left, .known right =>
      .known (right.foldl (fun roots root => if roots.contains root then roots else roots ++ [root]) left)

def Roots.bind (roots : Roots) (map : Atom → Roots) : Roots :=
  match roots with
  | .pending => .pending
  | .unknown => .unknown
  | .known roots => roots.foldl (fun acc root =>
      match acc, map root with
      | .unknown, _ | _, .unknown => .unknown
      | .pending, _ | _, .pending => .pending
      | left, right => left.join right) (.known [])

def flowAt (roots : Array Roots) (index : Nat) : Roots :=
  roots[index]?.getD .unknown

def addFlow (roots : Array Roots) (index : Nat) (added : Roots) : Array Roots :=
  roots.set! index ((flowAt roots index).join added)

inductive Write
  | unchanged
  | assigned (roots : Roots)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

def Write.join : Write → Write → Write
  | .unchanged, write | write, .unchanged => write
  | .assigned left, .assigned right => .assigned (left.join right)

structure State where
  values : Array Roots
  slots : Array Roots
  contents : Array Roots
  writes : Array Write
  touched : Roots := .known []
  returned : Roots := .pending
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

def Atom.ofRootRef : RootRef → Atom
  | .local slot => .local slot
  | .global index => .global index
  | .param index => .param index

def start (f : Func) (vt : Array (Option VTy)) : State := Id.run do
  let mut values := Array.replicate f.numValues Roots.pending
  if let some entry := f.blocks[0]? then
    for ((value, _), index) in entry.params.zipIdx do
      values := values.set! value (if valRefLike vt value then .known [.param index] else .known [])
  return { values
           slots := Array.replicate f.slots.size .pending
           contents := f.params.toArray.mapIdx fun index type =>
             if type.isRefSlice then .known [.contents index] else .known []
           writes := Array.replicate f.params.length .unchanged
           returned := .known [] }

def content (f : Func) (state : State) (address : Roots) : Roots :=
  address.bind fun
    | .local slot => flowAt state.slots slot
    | .param index =>
        if (f.params[index]?).any Ty.isRefSlice then flowAt state.contents index else .unknown
    | .global _ | .contents _ => .unknown

def write (f : Func) (state : State) (address value : Roots) : State :=
  match address with
  | .pending => state
  | .unknown =>
      { state with slots := state.slots.map (fun _ => .unknown)
                   contents := state.contents.map (fun _ => .unknown)
                   writes := state.writes.map (fun _ => .assigned .unknown) }
  | .known roots => roots.foldl (fun state root =>
      match root with
      | .local slot => { state with slots := addFlow state.slots slot value }
      | .param index =>
          if (f.params[index]?).any Ty.isRefSlice then
            { state with contents := addFlow state.contents index value
                         writes := state.writes.set! index
                           ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned value)) }
          else state
      | .global _ | .contents _ =>
          { state with touched := .unknown }) state

def substitute (f : Func) (state : State) (args : List ValueId) (roots : Roots) : Roots :=
  roots.bind fun
    | .global global => .known [.global global]
    | .param index => (args[index]?).map (flowAt state.values ·) |>.getD .unknown
    | .contents index =>
        (args[index]?).map (fun value => content f state (flowAt state.values value)) |>.getD .unknown
    | .local _ => .unknown

def publicTouches (roots : Roots) : Roots :=
  roots.bind fun
    | .local _ => .known []
    | root => .known [root]

def callState (m : Module) (states : Array State) (f : Func) (state : State)
    (fn : FnId) (args : List ValueId) : Roots × State := Id.run do
  let some callee := m.funcs[fn]? | return (.unknown, { state with touched := .unknown })
  let some effects := states[fn]? | return (.unknown, { state with touched := .unknown })
  let before := state
  let mut state := { state with touched := state.touched.join (substitute f before args (publicTouches effects.touched)) }
  for (type, index) in callee.params.zipIdx do
    if type.isRefSlice then
      match effects.writes[index]?.getD (.assigned .unknown) with
      | .unchanged => pure ()
      | .assigned roots =>
          let address := (args[index]?).map (flowAt before.values ·) |>.getD .unknown
          state := write f state address (substitute f before args roots)
  return (substitute f before args effects.returned, state)

def result (f : Func) (vt : Array (Option VTy)) (state : State)
    (value : ValueId) (op : Op) : Roots :=
  if !valRefLike vt value then .known [] else
    match op with
    | .slotAddr slot => .known [.local slot]
    | .globalAddr global => .known [.global global]
    | .fieldAddr source _ | .refElem source _ | .viewSlice _ source _ _ _
    | .indexChecked source _ _ | .indexProven source _ | .refFreeze source
    | .ownerBorrow source | .sliceView source | .push source _ _ | .snapshot _ source =>
        flowAt state.values source
    | .load address => content f state (flowAt state.values address)
    | .call .. => .pending
    | _ => .unknown

def accessOperands : Inst → List ValueId
  | .term _ => []
  | .def _ (.slotAddr _) | .def _ (.globalAddr _)
  | .def _ (.fieldAddr _ _) | .def _ (.refFreeze _) | .def _ (.ownerBorrow _) => []
  | .eff (.slotInit ..) => []
  | .eff (.store address _ _) => [address]
  | inst => inst.uses

def loadedResults : Inst → List ValueId
  | .def value (.load _) => [value]
  | _ => []

def interiorLoadedResults (vt : Array (Option VTy)) (inst : Inst) : List ValueId :=
  (loadedResults inst).filter fun value =>
    match vt[value]?.join with
    | some (.data type) => !type.isRefLike || type.interiorTarget?.isSome
    | _ => true

def touchValues (vt : Array (Option VTy)) (state : State) (values : List ValueId) : State :=
  { state with touched := values.foldl (fun roots value =>
      if valRefLike vt value then roots.join (flowAt state.values value) else roots) state.touched }

def edge (f : Func) (state : State) (target : BlockId) (args : List ValueId) : State :=
  match f.blocks[target]? with
  | none => { state with touched := .unknown }
  | some block =>
      (block.params.zip args).foldl (fun state (parameter, arg) =>
        { state with values := addFlow state.values parameter.1 (flowAt state.values arg) }) state

def step (m : Module) (states : Array State) (f : Func) (vt : Array (Option VTy))
    (state : State) (inst : Inst) : State := Id.run do
  let state := match inst with
    | .def _ (.call ..) => state
    | _ => touchValues vt state (accessOperands inst)
  match inst with
  | .def value (.call fn args _) =>
      let (roots, after) := callState m states f state fn args
      let after := { after with values := addFlow after.values value (if valRefLike vt value then roots else .known []) }
      return touchValues vt after (interiorLoadedResults vt inst)
  | .def value op =>
      let after := { state with values := addFlow state.values value (result f vt state value op) }
      return touchValues vt after (interiorLoadedResults vt inst)
  | .eff (.slotInit slot value _) =>
      return { state with slots := addFlow state.slots slot (flowAt state.values value) }
  | .eff (.store address value _) =>
      return if valRefLike vt value then write f state (flowAt state.values address) (flowAt state.values value) else state
  | .term (.br target args) => return edge f state target args
  | .term (.condbr _ thenBlock thenArgs elseBlock elseArgs) =>
      return edge f (edge f state thenBlock thenArgs) elseBlock elseArgs
  | .term (.ret [value] _) =>
      return { state with returned := state.returned.join (flowAt state.values value) }
  | _ => return state

def round (m : Module) (states : Array State) (f : Func) (vt : Array (Option VTy))
    (state : State) : State :=
  f.blocks.foldl (fun state block => block.insts.foldl (step m states f vt) state) state

def capacity (m : Module) (f : Func) : Nat :=
  (f.numValues + f.slots.size + 3 * f.params.length + 3) *
    (m.globals.size + f.slots.size + 2 * f.params.length + 3)

def moduleStart (m : Module) (types : Array (Array (Option VTy))) : Array State :=
  m.funcs.mapIdx fun index f => start f (types[index]?.getD #[])

def moduleRound (m : Module) (types : Array (Array (Option VTy))) (states : Array State) : Array State :=
  m.funcs.mapIdx fun index f =>
    round m states f (types[index]?.getD #[]) (states[index]?.getD (start f #[]))

def moduleFuel (m : Module) : Nat :=
  m.funcs.foldl (fun fuel f => fuel + capacity m f) 1

def closeFrom (m : Module) (types : Array (Array (Option VTy))) :
    Nat → Array State → Option (Array State)
  | 0, _ => none
  | fuel + 1, states =>
      let next := moduleRound m types states
      if next == states then some states else closeFrom m types fuel next

def close (m : Module) (types : Array (Array (Option VTy))) : Option (Array State) :=
  closeFrom m types (moduleFuel m) (moduleStart m types)

def normalizeAtom (f : Func) : Atom → Option (List RootRef)
  | .local slot => some [.local slot]
  | .global global => some [.global global]
  | .param index => some (f.parameterRoots index)
  | .contents index =>
      (f.roots.contents.find? (·.1 == index)).map fun row =>
        row.2.flatMap f.expandParameterRoot

def normalize (f : Func) (roots : Roots) : Option (List RootRef) :=
  match roots with
  | .pending | .unknown => none
  | .known roots => roots.foldlM (init := []) fun result root => do
      let mapped ← normalizeAtom f root
      pure (unionRoots result mapped)

def rootsWithin (actual : Option (List RootRef)) (expected : List RootRef) : Bool :=
  actual.any fun roots => roots.all expected.contains

def refReady (vt : Array (Option VTy)) (state : State) (inst : Inst) : Bool :=
  inst.uses.all fun value =>
    match vt[value]? with
    | some (some type) => !type.refLike ||
        match flowAt state.values value with
        | .pending => false
        | _ => true
    | _ => false

def checkWrites (f : Func) (state : State) : Bool :=
  state.writes.toList.zipIdx.all fun (write, index) =>
    match write with
    | .unchanged => true
    | .assigned roots =>
        let actual := normalize f roots
        actual == some [] || (f.roots.contents.find? (·.1 == index)).any fun row =>
          rootsWithin actual (row.2.flatMap f.expandParameterRoot)

def checkReturned (f : Func) (state : State) : Bool :=
  match f.results with
  | [type] =>
      if type.isRefLike then
        (f.roots.results[0]?).any fun roots =>
          rootsWithin (normalize f state.returned) (roots.flatMap f.expandParameterRoot)
      else true
  | [] => true
  | _ => false

def mappedBound (f : Func) (state : State) (args : List ValueId)
    (bound : List RootRef) : Option (List RootRef) := do
  let actual ← args.mapM (fun value => normalize f (flowAt state.values value))
  (Goose.Core.mapResultRoots actual [] bound).toOption

inductive ContentInputBound
  | roots (roots : List RootRef)
  | callerStorage
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

def ContentInputBound.join : ContentInputBound → ContentInputBound → ContentInputBound
  | .callerStorage, _ | _, .callerStorage => .callerStorage
  | .roots left, .roots right => .roots (unionRoots left right)

def ContentInputBound.covers (bound : ContentInputBound)
    (actual : Option (List RootRef)) : Bool :=
  actual.any fun roots => match bound with
    | .roots expected => roots.all expected.contains
    | .callerStorage => true

def admittedArgumentBound (callee : Func) (argumentRoots : Nat → Option (List RootRef))
    (index : Nat) : Option ContentInputBound := do
  let type ← callee.params[index]?
  let actual ← argumentRoots index
  match callee.roots.params.find? (·.1 == index) with
  | some (_, declared) =>
      if type.isRefLike && declared.contains (.param index) then pure .callerStorage
      else pure (.roots (unionRoots actual (declared.filterMap fun
        | .global global => some (.global global)
        | _ => none)))
  | none => pure (.roots actual)

def contentInputBound (callee : Func) (argumentRoots : Nat → Option (List RootRef))
    (bound : List RootRef) : Option ContentInputBound :=
  bound.foldlM (init := .roots []) fun upper root => do
    let next ← match root with
      | .global global => some (.roots [.global global])
      | .param index => admittedArgumentBound callee argumentRoots index
      | .local _ => none
    pure (upper.join next)

def checkCall (m : Module) (f : Func) (state : State) (fn : FnId)
    (args : List ValueId) : Bool :=
  match m.funcs[fn]? with
  | none => false
  | some callee =>
      let parameters := callee.params.zipIdx.all fun (type, index) =>
        if !type.isRefLike then true else
          match args[index]? with
          | none => false
          | some value =>
              let declared := callee.parameterRoots index
              declared.contains (.param index) ||
                (normalize f (flowAt state.values value)).any fun actual =>
                  actual.all fun root =>
                    match root with
                    | .global global => declared.contains (.global global)
                    | .local _ | .param _ => declared.contains (.param index)
      let argumentRoots := fun (index : Nat) => args[index]?.bind fun value =>
        normalize f (flowAt state.values value)
      parameters && callee.roots.contents.toList.all fun (index, bound) =>
        match args[index]?, contentInputBound callee argumentRoots bound with
        | some value, some expected => expected.covers (normalize f (content f state (flowAt state.values value)))
        | _, _ => false

def edgeTyped (f : Func) (vt : Array (Option VTy)) (target : BlockId)
    (args : List ValueId) : Bool :=
  (f.blocks[target]?).any fun block =>
    args.length == block.params.length &&
      (args.zip block.params).all fun (value, (_, type)) => vt[value]? == some (some type)

def annotationsValid (m : Module) (f : Func) : Bool :=
  let external := fun
    | RootRef.global global => global < m.globals.size
    | .param index => index < f.params.length
    | .local _ => false
  let parameters := f.roots.params.toList
  let contents := f.roots.contents.toList
  (parameters.map (·.1)).eraseDups.length == parameters.length &&
    (contents.map (·.1)).eraseDups.length == contents.length &&
    parameters.all (fun (index, roots) => (f.params[index]?).any Ty.isRefLike &&
      roots.all (fun root => external root && match root with
        | .param target => target == index
        | _ => true)) &&
    contents.all (fun (index, roots) => (f.params[index]?).any Ty.isRefSlice && roots.all external) &&
    f.roots.results.all (·.all external)

def checkInstruction (m : Module) (f : Func) (vt : Array (Option VTy)) (state : State)
    (inst : Inst) : Bool :=
  let env : TyEnv := { m.tyEnv f with vals := vt }
  refReady vt state inst && match inst with
  | .def value op =>
      (op.resultTy env).toOption.any (fun type => vt[value]? == some (some type)) &&
      match op with
      | .call fn args _ => checkCall m f state fn args
      | _ => true
  | .eff (.store address value _) =>
      (env.refTy address).toOption.any fun (_, type) => (env.dataTy value).toOption == some type
  | .eff (.slotInit slot value _) =>
      (f.slots[slot]?).any fun slot => (env.dataTy value).toOption == some slot.ty
  | .term (.ret values _) =>
      values.length == f.results.length &&
        (values.zip f.results).all (fun (value, type) => (env.dataTy value).toOption == some type)
  | .term (.br target args) => edgeTyped f vt target args
  | .term (.condbr value thenBlock thenArgs elseBlock elseArgs) =>
      (env.dataTy value).toOption == some .bool &&
        edgeTyped f vt thenBlock thenArgs && edgeTyped f vt elseBlock elseArgs
  | _ => true

def check (m : Module) (f : Func) (vt : Array (Option VTy)) (state : State) : Bool :=
  f.params.all Ty.paramOk && annotationsValid m f &&
    (f.blocks[0]?).any (fun entry => entry.params.map (·.2) == f.params.map VTy.data) &&
    checkWrites f state && checkReturned f state && f.blocks.all fun block =>
    block.params.all (fun (value, type) => vt[value]? == some (some type)) &&
    block.insts.all (checkInstruction m f vt state)

def closeFunctionFrom (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) : Nat → State → Option State
  | 0, _ => none
  | fuel + 1, state =>
      let next := round m states f vt state
      if next == state then if check m f vt state then some state else none
      else closeFunctionFrom m states f vt fuel next

def closeFunction (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) : Option State :=
  closeFunctionFrom m states f vt (capacity m f + 1) (start f vt)

def storageClosed (m : Module) : Bool :=
  m.globals.all (fun global => global.ty.storable && !global.ty.isRefLike)

def certificate (m : Module) (types : Array (Array (Option VTy))) (states : Array State) : Bool :=
  (m.funcs[m.entry]?).any (fun entry => entry.params.isEmpty && entry.results.isEmpty) &&
    (m.funcs.toList.zipIdx.all fun (f, index) =>
      (states[index]?).any (check m f (types[index]?.getD #[]))) &&
    m.globals.all fun global =>
      global.init.params.isEmpty && global.init.results == [global.ty] &&
      (closeFunction m states global.init (global.init.valueTypes m)).isSome

def ownerTouches (m : Module) (roots : List RootRef) : List RootRef :=
  if storageClosed m then roots.filter fun
    | .global index => (m.globals[index]?).all fun global => global.ty.ownerElem?.isSome
    | .local _ | .param _ => true
  else roots

def rawOwnerTouches (m : Module) (roots : Roots) : Roots :=
  roots.bind fun
    | .global global => .known ((ownerTouches m [.global global]).map Atom.ofRootRef)
    | atom => .known [atom]

def ownerDependencies (m : Module) (f : Func) (roots : Roots) : Option (List RootRef) :=
  normalize f (rawOwnerTouches m roots)

def callQuery (m : Module) (f : Func) (vt : Array (Option VTy))
    (states : Array State) (state : State) (fn : FnId) (args : List ValueId) : Option (List RootRef) :=do
  let env : TyEnv := { m.tyEnv f with vals := vt }
  if !(checkCall m f state fn args) ||
      (Op.call fn args none |>.resultTy env).toOption.isNone then failure else pure ()
  let effects ← states[fn]?
  let arguments ← args.foldlM (init := []) fun roots value => do
    if !valRefLike vt value then pure roots else
      let actual ← ownerDependencies m f (flowAt state.values value)
      pure (unionRoots roots actual)
  let touched ← ownerDependencies m f (substitute f state args (publicTouches effects.touched))
  pure (unionRoots arguments touched)


def mutationQuery (m : Module) (f : Func) (vt : Array (Option VTy))
    (states : Array State) (state : State) (fn : FnId) (args : List ValueId) : Option (List RootRef) :=do
  let env : TyEnv := { m.tyEnv f with vals := vt }
  if !(checkCall m f state fn args) ||
      (Op.call fn args none |>.resultTy env).toOption.isNone then failure else pure ()
  let effects ← states[fn]?
  let callee ← m.funcs[fn]?
  callee.params.zipIdx.foldlM (init := []) fun roots (type, index) => do
    if !type.isRefSlice then pure roots else
      match effects.writes[index]?.getD (.assigned .unknown) with
      | .unchanged => pure roots
      | .assigned _ =>
          let value ← args[index]?
          let actual ← normalize f (flowAt state.values value)
          pure (unionRoots roots actual)


end ReplacementContentFlow.Model

structure ReplacementContentFlow where
  private mk ::
  private module : Module
  private states : Option (Array ReplacementContentFlow.Model.State)

structure ReplacementFunctionFlow where
  private mk ::
  private cache : ReplacementContentFlow
  private function : Func
  private types : Array (Option VTy)
  private state : Option ReplacementContentFlow.Model.State

open ReplacementContentFlow.Model in

def replacementContentFlow (m : Module) : ReplacementContentFlow :=
  let types := m.funcs.map (·.valueTypes m)
  let states := if storageClosed m then (close m types).filter (certificate m types) else none
  ⟨m, states⟩

open ReplacementContentFlow.Model in

def ReplacementContentFlow.forFunction (cache : ReplacementContentFlow) (f : Func)
    (vt : Array (Option VTy)) : ReplacementFunctionFlow :=
  let actualTypes := f.valueTypes cache.module
  ⟨cache, f, actualTypes, if vt == actualTypes then
    cache.states.bind fun states => closeFunction cache.module states f actualTypes
    else none⟩

open ReplacementContentFlow.Model in

def ReplacementFunctionFlow.value (flow : ReplacementFunctionFlow) (value : ValueId) : Option (List RootRef) :=
  flow.state.bind fun state => normalize flow.function (flowAt state.values value)

open ReplacementContentFlow.Model in

def ReplacementFunctionFlow.ownerDependencies (flow : ReplacementFunctionFlow) (value : ValueId) : Option (List RootRef) :=
  flow.state.bind fun state => ReplacementContentFlow.Model.ownerDependencies flow.cache.module flow.function (flowAt state.values value)

open ReplacementContentFlow.Model in

def ReplacementFunctionFlow.contents (flow : ReplacementFunctionFlow) (value : ValueId) : Option (List RootRef) :=
  flow.state.bind fun state => normalize flow.function (content flow.function state (flowAt state.values value))

open ReplacementContentFlow.Model in

def ReplacementFunctionFlow.call (flow : ReplacementFunctionFlow) (fn : FnId)
    (args : List ValueId) : Option (List RootRef) := do
  let state ← flow.state
  let states ← flow.cache.states
  callQuery flow.cache.module flow.function flow.types states state fn args

open ReplacementContentFlow.Model in

def ReplacementFunctionFlow.mutation (flow : ReplacementFunctionFlow) (fn : FnId)
    (args : List ValueId) : Option (List RootRef) := do
  let state ← flow.state
  let states ← flow.cache.states
  mutationQuery flow.cache.module flow.function flow.types states state fn args

def ReplacementContentFlow.source (cache : ReplacementContentFlow) : Module := cache.module

def ReplacementContentFlow.model (cache : ReplacementContentFlow) :
    Option (Array ReplacementContentFlow.Model.State) := cache.states

def ReplacementFunctionFlow.source (flow : ReplacementFunctionFlow) : Func := flow.function

def ReplacementFunctionFlow.module (flow : ReplacementFunctionFlow) : Module := flow.cache.module

def ReplacementFunctionFlow.valueTypes (flow : ReplacementFunctionFlow) : Array (Option VTy) := flow.types

def ReplacementFunctionFlow.calleeStates (flow : ReplacementFunctionFlow) :
    Option (Array ReplacementContentFlow.Model.State) := flow.cache.states

def ReplacementFunctionFlow.model (flow : ReplacementFunctionFlow) :
    Option ReplacementContentFlow.Model.State := flow.state

theorem replacementContentFlow_source (m : Module) : (replacementContentFlow m).source = m := rfl

theorem replacementContentFlow_model (m : Module) :
    (replacementContentFlow m).model =
      if ReplacementContentFlow.Model.storageClosed m then
        (ReplacementContentFlow.Model.close m (m.funcs.map (·.valueTypes m))).filter
          (ReplacementContentFlow.Model.certificate m (m.funcs.map (·.valueTypes m)))
      else none := rfl

theorem ReplacementContentFlow.forFunction_model (cache : ReplacementContentFlow) (f : Func)
    (vt : Array (Option VTy)) :
    (cache.forFunction f vt).model =
      if vt == f.valueTypes cache.source then
        cache.model.bind (fun states => ReplacementContentFlow.Model.closeFunction cache.source states f
          (f.valueTypes cache.source))
      else none := rfl

theorem ReplacementFunctionFlow.value_model (flow : ReplacementFunctionFlow) (value : ValueId) :
    flow.value value = flow.model.bind (fun state =>
      ReplacementContentFlow.Model.normalize flow.source (ReplacementContentFlow.Model.flowAt state.values value)) := rfl

theorem ReplacementFunctionFlow.ownerDependencies_model (flow : ReplacementFunctionFlow) (value : ValueId) :
    flow.ownerDependencies value = flow.model.bind (fun state => ReplacementContentFlow.Model.ownerDependencies
      flow.module flow.source (ReplacementContentFlow.Model.flowAt state.values value)) := rfl

theorem ReplacementFunctionFlow.contents_model (flow : ReplacementFunctionFlow) (value : ValueId) :
    flow.contents value = flow.model.bind (fun state => ReplacementContentFlow.Model.normalize flow.source
      (ReplacementContentFlow.Model.content flow.source state (ReplacementContentFlow.Model.flowAt state.values value))) := rfl

theorem ReplacementFunctionFlow.call_model (flow : ReplacementFunctionFlow) (fn : FnId)
    (args : List ValueId) :
    flow.call fn args = flow.model.bind (fun state => flow.calleeStates.bind (fun states =>
      ReplacementContentFlow.Model.callQuery flow.module flow.source flow.valueTypes states state fn args)) := rfl

theorem ReplacementFunctionFlow.mutation_model (flow : ReplacementFunctionFlow) (fn : FnId)
    (args : List ValueId) :
    flow.mutation fn args = flow.model.bind (fun state => flow.calleeStates.bind (fun states =>
      ReplacementContentFlow.Model.mutationQuery flow.module flow.source flow.valueTypes states state fn args)) := rfl

end Goose.GIR
