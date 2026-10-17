import Goose.Construct.GIR.Typing

namespace Goose.Construct.GIR.Borrow

structure Demand where
  values : List ValueId := []
  slots : List SlotId := []
  deriving DecidableEq

private def union (left right : Demand) : Demand :=
  ⟨(left.values ++ right.values).eraseDups, (left.slots ++ right.slots).eraseDups⟩

private def transfer (f : Func) (demand : Demand) (inst : Inst) : Demand :=
  let values := match inst with
    | .def id _ => demand.values.filter (· != id)
    | _ => demand.values
  let slots := match inst with
    | .def _ (.slotAddr slot) => (slot :: demand.slots).eraseDups
    | .eff (.enter scope) | .eff (.leave scope) =>
        demand.slots.filter (fun slot => (f.slots[slot]?).any (·.scope != scope))
    | _ => demand.slots
  ⟨(values ++ inst.uses).eraseDups, slots⟩

private def edges : Term → List (BlockId × List ValueId)
  | .br target args => [(target,args)]
  | .condbr _ left la right ra => [(left,la),(right,ra)]
  | .invoke _ _ _ normal forwarded escapes _ =>
      (normal,forwarded) :: escapes.map (fun edge => (edge.block,edge.args))
  | _ => []

private def edgeDemand (f : Func) (term : Term) (target : BlockId) (args : List ValueId) (demand : Demand) : Demand :=
  match f.blocks[target]? with
  | none => demand
  | some block =>
      let leading := match term with | .invoke .. => block.params.length - args.length | _ => 0
      let mappings := (block.params.drop leading).map (·.1) |>.zip args
      let values := demand.values.flatMap fun id =>
        match mappings.find? (·.1 == id) with
        | some (_,arg) => [arg]
        | none => if (block.params.take leading).any (·.1 == id) then [] else [id]
      { demand with values := values.eraseDups }

private def continuation (f : Func) (entries : Array Demand) (block : Block) : Demand :=
  match block.lastTerm? with
  | none => {}
  | some term => (edges term).foldl (fun demand (target,args) =>
      union demand (edgeDemand f term target args (entries[target]?.getD {}))) {}

private def demands (f : Func) : Array Demand := Id.run do
  let mut entries := Array.replicate f.blocks.size ({} : Demand)
  for _ in [0:(f.blocks.size + 1) * (f.numValues + f.slots.size + 1) + 1] do
    let previous := entries
    for (block,id) in f.blocks.toList.zipIdx do
      let entry := block.insts.reverse.foldl (transfer f) (continuation f entries block)
      entries := entries.set! id (union (entries[id]?.getD {}) entry)
    if previous == entries then break
  return entries

private def overlap : RootRef → RootRef → Bool
  | .static, _ | _, .static => false
  | .param _, _ | _, .param _ => true
  | .local left, .local right | .global left, .global right => left == right
  | _, _ => false

private def contains : Nat → Ty → Ty → Bool
  | 0, _, _ => true
  | fuel + 1, owner, element =>
      owner == element || match owner with
      | .arr child _ | .varr child | .grow child | .growshrink child | .limited child _ => contains fuel child element
      | .structT _ fields => fields.toList.any (fun field => contains fuel field element)
      | _ => false

private def borrowed (fuel : Nat) (owner : Ty) : VTy → Bool
  | .data (.ref _ pointee) => pointee != owner && (owner.element?).any (fun element => contains fuel element pointee)
  | .data (.slice _ element) | .view _ element => (owner.element?).any (fun child => contains fuel child element)
  | .pack results => results.any (fun result => match result.ty with
      | .ref _ pointee => pointee != owner && (owner.element?).any (fun element => contains fuel element pointee)
      | .slice _ element => (owner.element?).any (fun child => contains fuel child element)
      | _ => false)
  | _ => false

private def ownerType : Ty → Option Ty
  | .ref _ owner => if owner matches .grow _ | .growshrink _ then some owner else none
  | owner => if owner matches .grow _ | .growshrink _ then some owner else none

private def rootType (m : Module) (f : Func) : RootRef → Option Ty
  | .local slot => (f.slots[slot]?).map (·.ty)
  | .global global => (m.globals[global]?).map (·.ty)
  | .param position => f.params[position]?
  | .static => none

private def initializedSlots (f : Func) : Array (List SlotId) := Id.run do
  let mut entries : Array (List SlotId) := Array.replicate f.blocks.size []
  for _ in [0:(f.blocks.size + 1) * (f.slots.size + 1) + 1] do
    let previous := entries
    for (block,id) in f.blocks.toList.zipIdx do
      let mut bound := entries[id]?.getD []
      for inst in block.insts do
        match inst with
        | .eff (.slotInit slot ..) | .eff (.destBind slot ..) => bound := (slot :: bound).eraseDups
        | .eff (.enter scope) | .eff (.leave scope) => bound := bound.filter (fun slot => (f.slots[slot]?).any (·.scope != scope))
        | _ => pure ()
      if let some term := block.lastTerm? then
        for (target,_) in edges term do
          entries := entries.set! target ((entries[target]?.getD [] ++ bound).eraseDups)
    if previous == entries then break
  return entries

def check (m : Module) (f : Func) (types : Array (Option VTy))
    (roots : ValueId → List RootRef) (contents : RootRef → List RootRef)
    (effects : Array Summary) : Except String Unit := do
  unless effects.size == m.funcs.size && types.size == f.numValues do throw "shrink analysis metadata shape mismatch"
  let entries := demands f
  let bindings := initializedSlots f
  let fuel := m.types.size + f.numValues + 1
  let data (id : ValueId) := (types[id]?.join).bind fun type => match type with | .data ty => some ty | _ => none
  let direct (id : ValueId) : List (Ty × List RootRef) :=
    ((data id).bind ownerType).map (fun ty => [(ty,roots id)]) |>.getD []
  let targets (targets : List Target) (args : List ValueId) : List (Ty × List RootRef) := targets.flatMap fun
    | .global global => ((m.globals[global]?).bind fun global => ownerType global.ty).map (fun ty => [(ty,[.global global])]) |>.getD []
    | .param position => (args[position]?).map direct |>.getD []
  let call (callee : FnId) (args : List ValueId) : List (Ty × List RootRef) :=
    match m.funcs[callee]? with
    | none => []
    | some function => match function.summary with
      | .known _ => targets ((effects[callee]?).map (·.shrinks) |>.getD []) args
      | .unknown => args.flatMap direct ++ m.globals.toList.zipIdx.flatMap (fun (global,id) =>
          (ownerType global.ty).map (fun ty => [(ty,[.global id])]) |>.getD [])
  for (block,id) in f.blocks.toList.zipIdx do
    let mut points : List Demand := []
    let mut demand := continuation f entries block
    for inst in block.insts.reverse do
      points := demand :: points
      demand := transfer f demand inst
    let mut bound := bindings[id]?.getD []
    for (inst,future) in block.insts.zip points do
      let shrinking := match inst with
        | .def _ (.pop receiver _) | .eff (.popN receiver ..) | .eff (.resize receiver ..) |
          .eff (.clear receiver _) | .eff (.replace receiver ..) | .def _ (.destOpen (.whole receiver) ..) => direct receiver
        | .def _ (.call callee args _) | .def _ (.callConstruct callee args _ _) | .term (.invoke callee args ..) => call callee args
        | _ => []
      let retained := match inst with
        | .def _ (.call _ args _) | .def _ (.callConstruct _ args _ _) | .term (.invoke _ args ..) => args
        | _ => []
      for (owner,shrinkingRoots) in shrinking do
        for value in (future.values ++ retained).eraseDups do
          if (types[value]?.join).any (borrowed fuel owner) then
            if (roots value).any (fun root => shrinkingRoots.any (overlap root)) then
              throw "shrink invalidates demanded or retained interior reference, slice or view"
        for slot in future.slots do
          if bound.contains slot then
            if let some descriptor := f.slots[slot]? then
              if borrowed fuel owner (.data descriptor.ty) then
                if (contents (.local slot)).any (fun root => shrinkingRoots.any (overlap root)) then
                  throw "shrink invalidates demanded reference or slice variable"
        for root in retained.flatMap roots do
          if let some ty := rootType m f root then
            if borrowed fuel owner (.data ty) then
              if (contents root).any (fun root => shrinkingRoots.any (overlap root)) then
                throw "shrinking call invalidates demanded argument contents"
      match inst with
      | .eff (.slotInit slot ..) | .eff (.destBind slot ..) => bound := (slot :: bound).eraseDups
      | .eff (.enter scope) | .eff (.leave scope) => bound := bound.filter (fun slot => (f.slots[slot]?).any (·.scope != scope))
      | _ => pure ()

end Goose.Construct.GIR.Borrow
