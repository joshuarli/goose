import Goose.GIR.Effects
import Goose.Core.Demand

namespace Goose.GIR

open Goose.Core

namespace ReplacementContentFlow

private inductive Atom
  | local (slot : SlotId)
  | global (global : GlobalId)
  | param (parameter : Nat)
  | contents (parameter : Nat)
  deriving BEq, Inhabited

private inductive Roots
  | pending
  | known (roots : List Atom)
  | unknown
  deriving BEq, Inhabited

private def Roots.join : Roots → Roots → Roots
  | .unknown, _ | _, .unknown => .unknown
  | .pending, roots | roots, .pending => roots
  | .known left, .known right =>
      .known (right.foldl (fun roots root => if roots.contains root then roots else roots ++ [root]) left)

private def Roots.bind (roots : Roots) (map : Atom → Roots) : Roots :=
  match roots with
  | .pending => .pending
  | .unknown => .unknown
  | .known roots => roots.foldl (fun acc root =>
      match acc, map root with
      | .unknown, _ | _, .unknown => .unknown
      | .pending, _ | _, .pending => .pending
      | left, right => left.join right) (.known [])

private def flowAt (roots : Array Roots) (index : Nat) : Roots :=
  roots[index]?.getD .unknown

private def addFlow (roots : Array Roots) (index : Nat) (added : Roots) : Array Roots :=
  roots.set! index ((flowAt roots index).join added)

private inductive Write
  | unchanged
  | assigned (roots : Roots)
  deriving BEq, Inhabited

private def Write.join : Write → Write → Write
  | .unchanged, write | write, .unchanged => write
  | .assigned left, .assigned right => .assigned (left.join right)

private structure State where
  values : Array Roots
  slots : Array Roots
  contents : Array Roots
  writes : Array Write
  touched : Roots := .known []
  returned : Roots := .pending
  deriving BEq

private def start (f : Func) (vt : Array (Option VTy)) : State := Id.run do
  let mut values := Array.replicate f.numValues Roots.pending
  if let some entry := f.blocks[0]? then
    for ((value, _), index) in entry.params.zipIdx do
      values := values.set! value (if valRefLike vt value then .known [.param index] else .known [])
  return { values
           slots := Array.replicate f.slots.size .pending
           contents := f.params.toArray.mapIdx fun index type =>
             if type.isRefSlice then .known [.contents index] else .known []
           writes := Array.replicate f.params.length .unchanged }

private def content (f : Func) (state : State) (address : Roots) : Roots :=
  address.bind fun
    | .local slot => flowAt state.slots slot
    | .param index =>
        if (f.params[index]?).any Ty.isRefSlice then flowAt state.contents index else .unknown
    | .global _ | .contents _ => .unknown

private def holdersOverlap (f : Func) (left right : Nat) : Bool :=
  (f.parameterRoots left).any fun a =>
    (f.parameterRoots right).any (Goose.Core.rootsMayOverlap a)

private def write (f : Func) (state : State) (address value : Roots) : State :=
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
            f.params.zipIdx.foldl (fun state (type, target) =>
              if type.isRefSlice && (index == target || holdersOverlap f index target) then
                { state with contents := addFlow state.contents target value
                             writes := state.writes.set! target
                               ((state.writes[target]?.getD (.assigned .unknown)).join (.assigned value)) }
              else state) state
          else state
      | .global _ | .contents _ =>
          { state with touched := .unknown }) state

private def substitute (f : Func) (state : State) (args : List ValueId) (roots : Roots) : Roots :=
  roots.bind fun
    | .global global => .known [.global global]
    | .param index => (args[index]?).map (flowAt state.values ·) |>.getD .unknown
    | .contents index =>
        (args[index]?).map (fun value => content f state (flowAt state.values value)) |>.getD .unknown
    | .local _ => .unknown

private def publicTouches (roots : Roots) : Roots :=
  roots.bind fun
    | .local _ => .known []
    | root => .known [root]

private def callState (m : Module) (states : Array State) (f : Func) (state : State)
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

private def result (f : Func) (vt : Array (Option VTy)) (state : State)
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

private def receiver : Inst → Option ValueId
  | .def _ (.load address) | .def _ (.snapshot _ address) | .def _ (.arrayLen address)
  | .def _ (.viewLen address) | .def _ (.indexChecked address ..)
  | .def _ (.indexProven address ..) | .def _ (.push address ..) | .def _ (.pop address ..)
  | .eff (.store address ..) | .eff (.append address ..) | .eff (.popN address ..)
  | .eff (.resize address ..) | .eff (.clear address ..) | .eff (.replace address ..) => some address
  | _ => none

private def edge (f : Func) (state : State) (target : BlockId) (args : List ValueId) : State :=
  match f.blocks[target]? with
  | none => { state with touched := .unknown }
  | some block =>
      (block.params.zip args).foldl (fun state (parameter, arg) =>
        { state with values := addFlow state.values parameter.1 (flowAt state.values arg) }) state

private def step (m : Module) (states : Array State) (f : Func) (vt : Array (Option VTy))
    (state : State) (inst : Inst) : State := Id.run do
  let mut state := state
  if let some address := receiver inst then
    state := { state with touched := state.touched.join (flowAt state.values address) }
  match inst with
  | .def value (.call fn args _) =>
      let (roots, after) := callState m states f state fn args
      return { after with values := addFlow after.values value (if valRefLike vt value then roots else .known []) }
  | .def value op => return { state with values := addFlow state.values value (result f vt state value op) }
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

private def round (m : Module) (states : Array State) (f : Func) (vt : Array (Option VTy))
    (state : State) : State :=
  f.blocks.foldl (fun state block => block.insts.foldl (step m states f vt) state) state

private def capacity (m : Module) (f : Func) : Nat :=
  (f.numValues + f.slots.size + 3 * f.params.length + 3) *
    (m.globals.size + f.slots.size + 2 * f.params.length + 3)

private def close (m : Module) (types : Array (Array (Option VTy))) : Option (Array State) :=
  let initial := m.funcs.mapIdx fun index f => start f (types[index]?.getD #[])
  let rec go : Nat → Array State → Option (Array State)
    | 0, _ => none
    | fuel + 1, states =>
        let next := m.funcs.mapIdx fun index f =>
          round m states f (types[index]?.getD #[]) (states[index]?.getD (start f #[]))
        if next == states then some states else go fuel next
  go (m.funcs.foldl (fun fuel f => fuel + capacity m f) 1) initial

private def normalize (f : Func) (roots : Roots) : Option (List RootRef) :=
  match roots with
  | .pending | .unknown => none
  | .known roots => roots.foldlM (init := []) fun result root => do
      let mapped ← match root with
        | .local slot => some [.local slot]
        | .global global => some [.global global]
        | .param index => some (f.parameterRoots index)
        | .contents index =>
            (f.roots.contents.find? (·.1 == index)).map fun row =>
              row.2.flatMap f.expandParameterRoot
      pure (unionRoots result mapped)

private def rootsWithin (actual : Option (List RootRef)) (expected : List RootRef) : Bool :=
  actual.any fun roots => roots.all expected.contains

private def refReady (vt : Array (Option VTy)) (state : State) (inst : Inst) : Bool :=
  inst.uses.all fun value =>
    match vt[value]? with
    | some (some type) => !type.refLike ||
        match flowAt state.values value with
        | .pending => false
        | _ => true
    | _ => false

private def checkWrites (f : Func) (state : State) : Bool :=
  state.writes.toList.zipIdx.all fun (write, index) =>
    match write with
    | .unchanged => true
    | .assigned roots =>
        let actual := normalize f roots
        actual == some [] || (f.roots.contents.find? (·.1 == index)).any fun row =>
          rootsWithin actual (row.2.flatMap f.expandParameterRoot)

private def mappedBound (f callee : Func) (state : State) (args : List ValueId)
    (bound : List RootRef) : Option (List RootRef) :=
  bound.foldlM (init := []) fun result root => do
    let mapped ← match root with
      | .global global => some [.global global]
      | .param index => do
          let value ← args[index]?
          normalize f (if (callee.params[index]?).any Ty.isRefSlice then
            content f state (flowAt state.values value)
            else flowAt state.values value)
      | .local _ => none
    pure (unionRoots result mapped)

private def checkCall (m : Module) (f : Func) (state : State) (fn : FnId)
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
              declared == [.param index] ||
                (normalize f (flowAt state.values value)).any fun actual =>
                  actual.all fun root =>
                    match root with
                    | .global global => declared.contains (.global global)
                    | .local _ | .param _ => declared.contains (.param index)
      parameters && callee.roots.contents.toList.all fun (index, bound) =>
        match args[index]?, mappedBound f callee state args bound with
        | some value, some expected => rootsWithin (normalize f (content f state (flowAt state.values value))) expected
        | _, _ => false

private def edgeTyped (f : Func) (vt : Array (Option VTy)) (target : BlockId)
    (args : List ValueId) : Bool :=
  (f.blocks[target]?).any fun block =>
    args.length == block.params.length &&
      (args.zip block.params).all fun (value, (_, type)) => vt[value]? == some (some type)

private def annotationsValid (m : Module) (f : Func) : Bool :=
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

private def check (m : Module) (f : Func) (vt : Array (Option VTy)) (state : State) : Bool :=
  let env : TyEnv := { m.tyEnv f with vals := vt }
  f.params.all Ty.paramOk && annotationsValid m f &&
    (f.blocks[0]?).any (fun entry => entry.params.map (·.2) == f.params.map VTy.data) &&
    checkWrites f state && f.blocks.all fun block =>
    block.params.all (fun (value, type) => vt[value]? == some (some type)) &&
    block.insts.all fun inst =>
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

private def closeFunction (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) : Option State :=
  let rec go : Nat → State → Option State
    | 0, _ => none
    | fuel + 1, state =>
        let next := round m states f vt state
        if next == state then if check m f vt state then some state else none else go fuel next
  go (capacity m f + 1) (start f vt)

end ReplacementContentFlow

structure ReplacementContentFlow where
  private mk ::
  private module : Module
  private states : Option (Array ReplacementContentFlow.State)

structure ReplacementFunctionFlow where
  private mk ::
  private cache : ReplacementContentFlow
  private function : Func
  private types : Array (Option VTy)
  private state : Option ReplacementContentFlow.State

open ReplacementContentFlow in

def replacementContentFlow (m : Module) : ReplacementContentFlow :=
  let types := m.funcs.map (·.valueTypes m)
  let states := if m.globals.all (fun global => global.ty.storable && !global.ty.isRefLike) then
    (close m types).filter fun states =>
      (m.funcs[m.entry]?).any (fun entry => entry.params.isEmpty && entry.results.isEmpty) &&
      (m.funcs.toList.zipIdx.all fun (f, index) =>
        (states[index]?).any (check m f (types[index]?.getD #[]))) &&
      m.globals.all fun global =>
        global.init.params.isEmpty && global.init.results == [global.ty] &&
        (closeFunction m states global.init (global.init.valueTypes m)).isSome
  else none
  ⟨m, states⟩

open ReplacementContentFlow in

def ReplacementContentFlow.forFunction (cache : ReplacementContentFlow) (f : Func)
    (vt : Array (Option VTy)) : ReplacementFunctionFlow :=
  let actualTypes := f.valueTypes cache.module
  ⟨cache, f, actualTypes, if vt == actualTypes then
    cache.states.bind fun states => closeFunction cache.module states f actualTypes
    else none⟩

open ReplacementContentFlow in

def ReplacementFunctionFlow.value (flow : ReplacementFunctionFlow) (value : ValueId) : Option (List RootRef) :=
  flow.state.bind fun state => normalize flow.function (flowAt state.values value)

open ReplacementContentFlow in

def ReplacementFunctionFlow.contents (flow : ReplacementFunctionFlow) (value : ValueId) : Option (List RootRef) :=
  flow.state.bind fun state => normalize flow.function (content flow.function state (flowAt state.values value))

open ReplacementContentFlow in

def ReplacementFunctionFlow.call (flow : ReplacementFunctionFlow) (fn : FnId)
    (args : List ValueId) : Option (List RootRef) := do
  let state ← flow.state
  let env : TyEnv := { flow.cache.module.tyEnv flow.function with vals := flow.types }
  if !(checkCall flow.cache.module flow.function state fn args) ||
      (Op.call fn args none |>.resultTy env).toOption.isNone then failure else pure ()
  let states ← flow.cache.states
  let effects ← states[fn]?
  let arguments ← args.foldlM (init := []) fun roots value => do
    if !valRefLike flow.types value then pure roots else
      let actual ← normalize flow.function (flowAt state.values value)
      pure (unionRoots roots actual)
  let touched ← normalize flow.function (substitute flow.function state args (publicTouches effects.touched))
  pure (unionRoots arguments touched)

open ReplacementContentFlow in

def ReplacementFunctionFlow.mutation (flow : ReplacementFunctionFlow) (fn : FnId)
    (args : List ValueId) : Option (List RootRef) := do
  let state ← flow.state
  let env : TyEnv := { flow.cache.module.tyEnv flow.function with vals := flow.types }
  if !(checkCall flow.cache.module flow.function state fn args) ||
      (Op.call fn args none |>.resultTy env).toOption.isNone then failure else pure ()
  let states ← flow.cache.states
  let effects ← states[fn]?
  let callee ← flow.cache.module.funcs[fn]?
  callee.params.zipIdx.foldlM (init := []) fun roots (type, index) => do
    if !type.isRefSlice then pure roots else
      match effects.writes[index]?.getD (.assigned .unknown) with
      | .unchanged => pure roots
      | .assigned _ =>
          let value ← args[index]?
          let actual ← normalize flow.function (flowAt state.values value)
          pure (unionRoots roots actual)

end Goose.GIR
