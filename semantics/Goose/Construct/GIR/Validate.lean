import Goose.Construct.GIR.Evidence
import Goose.Construct.GIR.Provenance
import Goose.Construct.Layout

namespace Goose.Construct.GIR
open Goose.Core (OriginId Mutability VarKind Request)

inductive Code
  | v001 | v010 | v020 | v030 | v040 | v050 | v060 | v070 | v080 | v090 | v100
  deriving DecidableEq, Repr

def Code.tag : Code → String
  | .v001 => "GIR-V001" | .v010 => "GIR-V010" | .v020 => "GIR-V020"
  | .v030 => "GIR-V030" | .v040 => "GIR-V040" | .v050 => "GIR-V050"
  | .v060 => "GIR-V060" | .v070 => "GIR-V070" | .v080 => "GIR-V080"
  | .v090 => "GIR-V090" | .v100 => "GIR-V100"

structure Violation where
  code : Code
  message : String
  deriving Repr

abbrev Check := Except Violation

def violation (code : Code) (message : String) : Check α := .error ⟨code, message⟩

def checkTypeResult (action : TyR α) : Check α :=
  action.mapError fun message => ⟨.v010, message⟩

def Func.entryTypes (f : Func) : List VTy :=
  f.params.map (fun ty => .data (if ty.nonfixed then .ref .mutable ty else ty)) ++
    f.results.filterMap destinationType?

def Inst.origin? : Inst → Option (Option OriginId)
  | .def _ op => match op with
    | .bin op _ _ _ o => if op matches .add | .sub | .mul | .div | .mod then some o else o.map some
    | .un op _ _ o => if op matches .neg then some o else o.map some
    | .conv kind _ _ _ o => if kind matches .as then some o else o.map some
    | .viewSlice _ _ _ _ o |
      .indexChecked _ _ o | .push _ _ o | .pop _ o | .call _ _ o | .bytes _ o |
      .destOpen _ _ _ _ o | .destChild _ _ o | .destFinish _ o | .destNamed _ o |
      .resultExitDest _ o | .destAbandonNamed _ _ o | .destPublishRef _ o | .destArg _ o | .destAbandon _ o |
      .destValue _ o | .destRelocate _ _ o | .destStage _ o | .destFit _ o |
      .callConstruct _ _ _ o | .targetDest _ _ o | .render _ o => some o
    | _ => none
  | .eff e => match e with
    | .slotInit _ _ o | .store _ _ o | .append _ _ o | .popN _ _ o | .resize _ _ _ o |
      .clear _ o | .replace _ _ o | .print _ o | .appendValue _ _ o | .destWrite _ _ o |
      .destAttach _ _ o | .destBytes _ _ o | .destText _ _ o | .destCopy _ _ o |
      .destBind _ _ o | .destPublish _ o | .destCancel _ o | .destRepeat _ _ o | .destSnapshot _ _ o => some o
    | _ => none
  | .term t => match t with
    | .ret _ o => o.map some
    | .abort _ o | .exit _ o | .invoke _ _ _ _ _ _ o | .escape _ _ _ o => some o
    | _ => none

def Term.edges (term : Term) : List (BlockId × List ValueId) :=
  match term with
  | .br block args => [(block,args)]
  | .condbr _ left la right ra => [(left,la),(right,ra)]
  | .invoke _ _ _ normal forwarded escapes _ => (normal,forwarded) :: escapes.map (fun e => (e.block,e.args))
  | _ => []

def Module.environment (m : Module) (f : Func) : TyEnv :=
  { m.tyEnv f with vals := f.valueTypes m }

private def allTypesValid (m : Module) : Ty → Bool
  | .int _ | .bool | .unit => true
  | .arr e n => n > 0 && (e.flat || e.variableElement) && allTypesValid m e
  | .varr e | .grow e => (e.flat || e.variableElement) && allTypesValid m e
  | .growshrink e => e.flat && allTypesValid m e
  | .limited e n => n > 0 && n < 2^31 && e.flat && allTypesValid m e
  | .ref _ e => (e.storable || (e matches .ref _ (.slice ..))) && allTypesValid m e
  | .slice _ e => (e.flat || e.variableElement) && allTypesValid m e
  | .structT sid fs => match m.structs[sid]? with
    | some d => fs == TyList.ofList (d.fields.toList.map (·.ty)) && fs.flat
    | none => false
  | .tuple _ => false

private def parameterBinding (f : Func) (slot : SlotId) (value : ValueId) : Bool :=
  match f.blocks[0]?, f.slots[slot]?, f.params[slot]? with
  | some entry, some descriptor, some ty =>
      descriptor.scope == 0 && descriptor.ty == ty && (entry.params[slot]?).any (·.1 == value)
  | _, _, _ => false

private def ownedParameter (f : Func) (slot : SlotId) (value : ValueId) : Bool :=
  (f.params[slot]?).any (·.nonfixed) && parameterBinding f slot value

private def borrowedSliceParameter (f : Func) (slot : SlotId) : Bool :=
  match f.slots[slot]?, f.params[slot]? with
  | some descriptor, some ty =>
      descriptor.scope == 0 && descriptor.ty == ty && (ty matches .ref _ (.slice ..))
  | _, _ => false

private def checkTables (m : Module) (f : Func) : Check Unit := do
  unless f.blocks.size > 0 do violation .v001 "function has no entry block"
  let definitions := f.blocks.toList.flatMap Block.defs
  unless definitions.eraseDups.length == definitions.length &&
      definitions.all (· < f.numValues) do violation .v001 "SSA value ids must be unique and dense"
  for block in f.blocks do
    unless block.insts.all (fun inst => inst.uses.all (· < f.numValues)) do
      violation .v001 "SSA use outside value table"
  for descriptor in f.results do
    unless allTypesValid m descriptor.ty && (descriptor.ty.storable || descriptor.ty == .unit) do violation .v010 "invalid result type"
    unless descriptor.ty.nonfixed == (descriptor.request != .register) do
      violation .v010 "result request does not match fixed/nonfixed type"
    if let some slot := descriptor.namedLocal then
      unless descriptor.request == .value do violation .v060 "named result requires value request"
      let some slotDef := f.slots[slot]? | violation .v001 "named result slot outside table"
      unless slotDef.scope == 0 && slotDef.ty.adaptsTo descriptor.ty do
        violation .v060 "named result slot is not eligible receiving storage"
  let aliases := f.results.filterMap (·.namedLocal)
  unless aliases.eraseDups == aliases do violation .v060 "one slot aliases several results"
  for (slot,index) in f.slots.toList.zipIdx do
    unless allTypesValid m slot.ty && (slot.ty.storable || borrowedSliceParameter f index) do violation .v010 "invalid slot type"
    unless slot.scope < f.scopes.size do violation .v001 "slot scope outside table"
  for ty in f.params do
    unless allTypesValid m ty && (ty.storable || (ty matches .ref _ (.slice ..))) do violation .v010 "invalid parameter type"
  let some entry := f.blocks[0]? | violation .v001 "entry block missing"
  unless entry.params.map (·.2) == f.entryTypes do violation .v010 "entry carriers differ from source parameters and result channels"
  for ((id,_),ty) in (entry.params.take f.params.length).zip f.params do
    if ty.nonfixed || (ty matches .ref _ (.slice ..)) then
      let bindings := f.blocks.toList.flatMap (·.insts) |>.filterMap fun
        | .eff (.slotInit slot value _) => if parameterBinding f slot value && value == id then some slot else none
        | _ => none
      unless bindings.length == 1 && entry.insts.any (fun inst => match inst with
          | .eff (.slotInit slot value _) => value == id && bindings == [slot]
          | _ => false) do violation .v060 "owned or borrowed-slice parameter must bind exactly one original entry slot"

private def requireVal (env : TyEnv) (value : ValueId) (expected : VTy) : Check Unit := do
  unless (← checkTypeResult (env.valTy value)) == expected do violation .v010 "operand type mismatch"

private def checkEffect (f : Func) (env : TyEnv) : Effect → Check Unit
  | .enter _ | .leave _ => pure ()
  | .slotInit slotId value _ => do
      let some slot := env.slots[slotId]? | violation .v001 "initialization slot outside table"
      if slot.ty.nonfixed then
        unless ownedParameter f slotId value do violation .v060 "nonfixed initialization requires destination publication or corresponding owned entry parameter"
        requireVal env value (.data (.ref .mutable slot.ty))
      else
        if slot.ty matches .ref _ (.slice ..) then
          unless parameterBinding f slotId value do violation .v060 "reference-to-slice slot requires its matching source entry parameter"
        requireVal env value (.data slot.ty)
  | .store reference value _ => do
      let (mutability, ty) ← checkTypeResult (env.refTy reference)
      unless mutability == .mutable do violation .v030 "store through read-only reference"
      if ty.nonfixed then violation .v060 "nonfixed store detaches receiving value"
      requireVal env value (.data ty)
  | .print parts _ => do
      for part in parts do
        if let .val value := part then
          match ← checkTypeResult (env.valTy value) with
          | .data ty => if ty.nonfixed then violation .v010 "nonfixed print requires sampled view"
          | .view .. => pure ()
          | _ => violation .v010 "protocol carrier cannot be printed"
  | .destSnapshot destination value _ => do
      let (ty, _) ← checkTypeResult (env.destTy destination)
      let .arr element _ ← checkTypeResult (env.dataTy value) | violation .v010 "destination snapshot requires fixed array"
      unless element.flat && ty.element? == some element do violation .v010 "destination snapshot element mismatch"
  | .destRepeat destination source _ => do
      let (ty, _) ← checkTypeResult (env.destTy destination)
      let .arr element _ := ty | violation .v010 "repeat requires fixed count destination"
      let (sourceTy, request) ← checkTypeResult (env.builtTy source)
      unless element == sourceTy && request == .value do violation .v010 "repeat source element/type mismatch"
  | .destWrite destination value _ => do
      let (ty, _) ← checkTypeResult (env.destTy destination)
      let some element := ty.element? | violation .v010 "destination has no element"
      unless element.flat do violation .v010 "nonfixed element requires child destination"
      requireVal env value (.data element)
  | .destAttach parent child _ => do
      let (ty, _) ← checkTypeResult (env.destTy parent)
      let (element, request) ← checkTypeResult (env.builtTy child)
      unless ty.element? == some element && request == .value do violation .v010 "attached child type/request mismatch"
  | .destBytes destination _ _ => do
      let (ty, _) ← checkTypeResult (env.destTy destination)
      unless ty.element? == some (.int .u8) do violation .v010 "text/bytes require u8 destination"
  | .destText destination value _ => do
      let (ty, _) ← checkTypeResult (env.destTy destination)
      unless ty.element? == some (.int .u8) do violation .v010 "text requires u8 destination"
      match ← checkTypeResult (env.valTy value) with
      | .data ty => if ty.nonfixed then violation .v010 "text operand requires fixed value or sampled view"
      | .view .. => pure ()
      | _ => violation .v010 "text cannot render protocol carrier"
  | .destCopy destination source _ => do
      let (ty, _) ← checkTypeResult (env.destTy destination)
      let sourceTy ← checkTypeResult (env.valTy source)
      let element ← match sourceTy with
        | .data (.ref _ t) => pure t.element?
        | .data (.slice _ e) | .view _ e => pure (some e)
        | _ => violation .v010 "copy requires source storage or sampled view"
      unless element == ty.element? do violation .v010 "copy source/destination element mismatch"
  | .destBind slot value _ => do
      let descriptor ← checkTypeResult (env.namedResult slot)
      requireVal env value (carrierType descriptor)
  | .destPublish built _ => do let _ ← checkTypeResult (env.builtTy built)
  | .destCancel cancelled _ => do
      unless (← checkTypeResult (env.valTy cancelled)) matches .cancelled .. do
        violation .v010 "cancel requires cancellation certificate"
  | .appendValue reference value _ => do
      let (_, owner) ← checkTypeResult (env.refTy reference)
      unless owner.growing do violation .v010 "append receiver is not growing"
      let .arr element _ ← checkTypeResult (env.dataTy value) | violation .v010 "append_value requires fixed array"
      unless !element.nonfixed && owner.element? == some element do violation .v010 "append_value element mismatch"
  | .append reference view _ => do
      let (_, owner) ← checkTypeResult (env.refTy reference)
      let (_, element) ← checkTypeResult (env.viewTy view)
      unless owner.growing && owner.element? == some element do violation .v010 "append types differ"
  | .clear reference _ => do
      let (_, owner) ← checkTypeResult (env.refTy reference)
      unless owner.growing && !((owner matches .grow _)) do violation .v010 "shrink operation requires growshrink or limited"
  | .popN reference count _ => do
      let (_, owner) ← checkTypeResult (env.refTy reference)
      unless owner matches .growshrink _ | .limited .. do violation .v010 "pop_n requires shrinkable owner"
      let _ ← checkTypeResult (env.intTy count)
  | .resize reference size fill _ => do
      let (_, owner) ← checkTypeResult (env.refTy reference)
      unless owner matches .growshrink _ | .limited .. do violation .v010 "resize requires shrinkable owner"
      let _ ← checkTypeResult (env.intTy size)
      if let some value := fill then
        let some element := owner.element? | violation .v010 "resize receiver has no element"
        requireVal env value (.data element)
  | .replace reference run _ => do
      let (_, owner) ← checkTypeResult (env.refTy reference)
      requireVal env run (.data owner)
      violation .v060 "construction replacement requires destination protocol"

private def edgeTypes (m : Module) (_f : Func) (env : TyEnv) (term : Term) (block : BlockId) : Check (List VTy) := do
  match term with
  | .invoke callee _ destinations normal _ escapes _ =>
      let some callee := m.funcs[callee]? | violation .v001 "invoke callee outside table"
      if block == normal then pure (callee.results.map carrierType)
      else
        let some edge := escapes.find? (·.block == block) | violation .v020 "invoke edge missing"
        let some target := m.targets[edge.target]? | violation .v001 "invoke target outside table"
        let some member := m.funcs[target.first]? | violation .v001 "target member outside table"
        let cancelled ← destinations.mapM fun id => do
          let (ty, request) ← checkTypeResult (env.destTy id)
          pure (VTy.cancelled ty request)
        pure (member.results.map carrierType ++ cancelled)
  | _ => pure []

private def checkTypesAndEdges (m : Module) (f : Func) : Check Unit := do
  let env := m.environment f
  for block in f.blocks do
    unless block.terms.length == 1 && block.lastTerm?.isSome do violation .v020 "block requires one final terminator"
    for inst in block.insts do
      match inst with
      | .def result op =>
          let ty ← checkTypeResult (op.resultTy env)
          requireVal env result ty
      | .eff effect => checkEffect f env effect
      | .term term =>
          match term with
          | .ret results _ =>
              unless results.length == f.results.length do violation .v010 "return result arity mismatch"
              for (result, descriptor) in results.zip f.results do requireVal env result (carrierType descriptor)
          | .condbr condition .. => requireVal env condition (.data .bool)
          | .exit value _ => let _ ← checkTypeResult (env.intTy value)
          | .invoke callee args destinations _ _ _ _ => let _ ← checkTypeResult (env.checkCall callee args destinations)
          | .escape target results cancellations _ =>
              let some target := m.targets[target]? | violation .v001 "escape target outside table"
              let some targetFunc := m.funcs[target.first]? | violation .v001 "target member outside table"
              unless results.length == targetFunc.results.length do violation .v010 "escape result arity mismatch"
              for (id, descriptor) in results.zip targetFunc.results do requireVal env id (carrierType descriptor)
              let expected := f.results.filterMap fun r => (destinationType? r).map fun
                | .dest t q => VTy.cancelled t q
                | other => other
              unless expected.length == cancellations.length do violation .v010 "escape cancellation arity mismatch"
              for (id, ty) in cancellations.zip expected do requireVal env id ty
          | _ => pure ()
          for (target, args) in term.edges do
            let some targetBlock := f.blocks[target]? | violation .v020 "branch target outside blocks"
            let leading ← edgeTypes m f env term target
            let types ← args.mapM fun arg => checkTypeResult (env.valTy arg)
            unless targetBlock.params.map (·.2) == leading ++ types do violation .v020 "branch carrier arity/type mismatch"

private inductive ReturnFlow
  | returns
  | stops
  | branches (blocks : List BlockId)

private def blockReturnFlow (m : Module) (functionId : FnId) (mayReturn : Array Bool) : List Inst → ReturnFlow
  | [] => .returns
  | .def _ (.call callee ..) :: rest | .def _ (.callConstruct callee ..) :: rest =>
      if mayReturn[callee]?.getD true then blockReturnFlow m functionId mayReturn rest else .stops
  | .term (.ret ..) :: _ | .term .unreachable :: _ => .returns
  | .term (.br block ..) :: _ => .branches [block]
  | .term (.condbr _ left _ right _) :: _ => .branches [left,right]
  | .term (.invoke callee _ _ normal _ escapes _) :: _ =>
      .branches ((if mayReturn[callee]?.getD true then [normal] else []) ++ escapes.map (·.block))
  | .term (.escape target ..) :: _ =>
      if (m.targets[target]?).any (fun target => target.contains functionId) then .returns else .stops
  | .term (.abort ..) :: _ | .term (.exit ..) :: _ => .stops
  | _ :: rest => blockReturnFlow m functionId mayReturn rest

private def functionMayReturn (m : Module) (mayReturn : Array Bool) (functionId : FnId) (f : Func) : Bool := Id.run do
  let mut reached := [0]
  for _ in [0:f.blocks.size + 1] do
    let previous := reached
    for id in reached do
      let some block := f.blocks[id]? | return true
      match blockReturnFlow m functionId mayReturn block.insts with
      | .returns => return true
      | .stops => pure ()
      | .branches targets => reached := (reached ++ targets).eraseDups
    if previous == reached then return false
  return true

private def functionsMayReturn (m : Module) : Array Bool := Id.run do
  let initial := Array.replicate m.funcs.size true
  let mut current := initial
  for _ in [0:m.funcs.size + 1] do
    let next := m.funcs.mapIdx (functionMayReturn m current)
    if next == current then return current
    current := next
  return initial

private def checkUnreachable (m : Module) : Check Unit := do
  let mayReturn := functionsMayReturn m
  for f in m.funcs do
    for (block,index) in f.blocks.toList.zipIdx do
      if block.lastTerm?.any (fun term => term matches .unreachable) then
        let followsCall := match (block.insts.dropLast).getLast? with
          | some (.def _ (.call callee ..)) | some (.def _ (.callConstruct callee ..)) => !mayReturn[callee]?.getD true
          | _ => false
        let predecessors := f.blocks.toList.filterMap fun block => do
          let term ← block.lastTerm?
          if term.successors.contains index then some term else none
        let invokeContinuation := block.insts.length == 1 && !predecessors.isEmpty && predecessors.all (fun term =>
          match term with
          | .invoke callee _ _ normal _ escapes _ =>
              normal == index && !(escapes.any (fun edge => edge.block == index)) && !mayReturn[callee]?.getD true
          | _ => false)
        unless followsCall || invokeContinuation do violation .v020 "unreachable lacks proven nonreturning call or invoke normal continuation"

private def reachable (f : Func) : List Nat := Id.run do
  let mut found := [0]
  for _ in [0:f.blocks.size] do
    for block in found do
      if let some block := f.blocks[block]? then
        if let some term := block.lastTerm? then found := (found ++ term.successors).eraseDups
  return found

private def checkDominance (f : Func) : Check Unit := do
  let live := reachable f
  unless live.length == f.blocks.size do violation .v020 "unreachable CFG block"
  let initial := f.blocks.mapIdx fun i _ => if i == 0 then [0] else live
  let mut dom := initial
  for _ in [0:f.blocks.size * f.blocks.size + 1] do
    for target in live.tail do
      let predecessors := live.filter fun block =>
        ((f.blocks[block]?).bind Block.lastTerm?).any (fun term => term.successors.contains target)
      let shared := predecessors.foldl (fun shared predecessor => shared.filter fun d => (dom[predecessor]?.getD []).contains d) live
      dom := dom.set! target ((target :: shared).eraseDups)
  for h : bi in [0:f.blocks.size] do
    let block := f.blocks[bi]
    let mut available := f.blocks.toList.zipIdx |>.flatMap fun (other,index) =>
      if index != bi && (dom[bi]?.getD []).contains index then other.defs else []
    available := available ++ block.params.map (·.1)
    for inst in block.insts do
      unless inst.uses.all available.contains do violation .v020 "SSA operand is not dominated by its definition"
      if let .def result _ := inst then available := result :: available

private def checkScopes (f : Func) : Check Unit := do
  let mut entries : Array (Option (List Nat)) := Array.replicate f.blocks.size none
  entries := entries.set! 0 (some [])
  for _ in [0:f.blocks.size + 1] do
    for h : bi in [0:f.blocks.size] do
      if let some initial := (entries[bi]?).bind (fun value => value) then
        let mut scopes := initial
        for inst in f.blocks[bi].insts do
          match inst with
          | .eff (.enter scope) =>
              let some parent := f.scopes[scope]? | violation .v040 "entered scope outside tree"
              unless parent == scopes.head? && !scopes.contains scope do violation .v040 "scope entry does not follow tree"
              scopes := scope :: scopes
          | .eff (.leave scope) =>
              unless scopes.head? == some scope do violation .v040 "scope leave does not match innermost scope"
              scopes := scopes.tail
          | .def _ (.slotAddr slot) | .def _ (.destOpen (.slot slot) ..) =>
              let some slot := f.slots[slot]? | violation .v001 "slot outside table"
              unless scopes.contains slot.scope do violation .v030 "slot access outside entered scope"
          | .term (.ret ..) | .term (.escape ..) =>
              unless scopes.isEmpty do violation .v040 "return/escape with entered scopes"
          | .term term =>
              for target in term.successors do
                match entries[target]? with
                | some (some previous) => unless previous == scopes do violation .v040 "scope stack differs across CFG join"
                | some none => entries := entries.set! target (some scopes)
                | none => violation .v020 "scope edge outside blocks"
          | _ => pure ()

private def externalRoots (arguments : List (List RootRef)) (roots : List RootRef) : List RootRef :=
  roots.flatMap fun
    | .param position => arguments[position]?.getD []
    | .local _ => []
    | root => [root]

private def expandParameter (f : Func) : RootRef → List RootRef
  | .param position =>
      let declared := (f.roots.params.find? (·.1 == position)).map (·.2) |>.getD []
      if declared.isEmpty then [.param position] else declared
  | root => [root]


private def storageRebinds (f : Func) (roots : Array (List RootRef)) (reference : ValueId) : List Target :=
  (roots[reference]?.getD []).filterMap fun
    | .param position =>
        if (f.params[position]?).any (fun ty => ty matches .ref _ (.slice ..)) then some (.param position) else none
    | .local slot =>
        match f.slots[slot]?, f.params[slot]? with
        | some descriptor, some parameter =>
            if descriptor.scope == 0 && descriptor.ty == parameter && (parameter matches .ref .. | .slice ..) then some (.param slot) else none
        | _, _ => none
    | _ => none

private def escapeResultIndex (m : Module) (functionId : FnId) (targetId : Nat) : Nat :=
  m.funcs.size + functionId * m.targets.size + targetId

private def globalContentIndex (m : Module) (globalId : Core.GlobalId) : Nat :=
  m.funcs.size * (m.targets.size + 1) + globalId

private def storedGlobalRoots (m : Module) (returns : Array (List (List RootRef))) (global : Nat) : List RootRef :=
  ((returns[m.funcs.size - m.globals.size + global]?.getD []).flatten ++
    (returns[globalContentIndex m global]?.getD []).flatten).eraseDups

private def mergeRootRows (previous next : List (List RootRef)) : List (List RootRef) :=
  if previous.isEmpty then next else if next.isEmpty then previous else (previous.zip next).map fun (a,b) => (a ++ b).eraseDups

private def argumentContents (m : Module) (f : Func) (returns : Array (List (List RootRef)))
    (roots slots : Array (List RootRef)) (value : ValueId) : List RootRef :=
  (roots[value]?.getD []).flatMap fun (root : RootRef) =>
    let backing : List RootRef := match root with
      | .local slot => slots[slot]?.getD []
      | .param position => (f.roots.contents.find? (fun (row : Nat × List RootRef) => row.1 == position)).map (fun row => row.2) |>.getD []
      | .global global => storedGlobalRoots m returns global
      | .static => [.static]
    backing.flatMap (expandParameter f)


private def callContents (m : Module) (f callee : Func) (returns : Array (List (List RootRef)))
    (roots slots : Array (List RootRef)) (args : List ValueId) (position : Nat) : List RootRef :=
  let declared := (callee.roots.contents.find? (·.1 == position)).map (·.2) |>.getD []
  declared.flatMap fun
    | .global global => [RootRef.global global]
    | .static => [.static]
    | .param source =>
        if let some arg := args[source]? then
          if (callee.params[source]?).any (fun t => t matches .ref _ (.slice ..)) then
            argumentContents m f returns roots slots arg
          else (roots[arg]?.getD []).flatMap (expandParameter f)
        else []
    | .local _ => []

private def storageRoots (m : Module) (f : Func) (returns : Array (List (List RootRef))) : Array (List RootRef) × Array (List RootRef) := Id.run do
  let types := f.valueTypes m
  let mut roots := Array.replicate f.numValues []
  let mut slots := Array.replicate f.slots.size []
  let mut packs : Array (List (List RootRef)) := Array.replicate f.numValues []
  if let some entry := f.blocks[0]? then
    for ((id,_), ty, position) in (entry.params.take f.params.length |>.zip f.params |>.zipIdx).map (fun ((id,ty),position) => (id,ty,position)) do
      let boundSlot := entry.insts.findSome? fun
        | .eff (.slotInit slot value _) => if value == id then some slot else none
        | _ => none
      roots := roots.set! id (if ty.nonfixed then [.local (boundSlot.getD position)] else if ty matches .ref .. | .slice .. then [.param position] else [])
  for _ in [0:f.numValues + f.slots.size + 1] do
    let previousRoots := roots
    let previousSlots := slots
    let previousPacks := packs
    for block in f.blocks do
      for inst in block.insts do
        let get (id : ValueId) := roots[id]?.getD []
        match inst with
        | .def id op =>
            match op with
            | .call callee args _ | .callConstruct callee args _ _ =>
                if let some definition := m.funcs[callee]? then
                  for ((parameter,arg),position) in (definition.params.zip args).zipIdx do
                    if parameter matches .ref _ (.slice ..) then
                      let contents := callContents m f definition returns roots slots args position
                      for root in get arg do
                        if let .local slot := root then
                          slots := slots.set! slot ((slots[slot]?.getD [] ++ contents).eraseDups)
                let rows := (returns[callee]?.getD []).map (externalRoots (args.map get))
                packs := packs.set! id (mergeRootRows (packs[id]?.getD []) rows)
            | _ => pure ()
            let found : List RootRef := match op with
              | .slotAddr slot => [.local slot]
              | .globalAddr global => [.global global]
              | .bytes .. => [.static]
              | .load reference =>
                  if ((types[id]?).bind (fun value => value)).any (fun t => t matches .data (.ref ..) | .data (.slice ..)) then
                    (get reference).flatMap fun
                      | .local slot => slots[slot]?.getD []
                      | .param position =>
                          if (f.params[position]?).any (fun ty => ty matches .ref _ (.slice ..)) then
                            (f.roots.contents.find? (fun (row : Nat × List RootRef) => row.1 == position)).map (fun row => row.2) |>.getD []
                          else [.param position]
                      | .global global =>
                          if (m.globals[global]?).any (fun global => global.ty matches .ref .. | .slice ..) then
                            storedGlobalRoots m returns global
                          else [.global global]
                      | root => [root]
                  else []
              | .refFreeze source | .snapshot _ source | .sliceView source | .viewSlice _ source _ _ _ |
                .refElem source _ | .indexChecked source _ _ | .indexProven source _ | .fieldAddr source _ |
                .destFinish source _ | .destPublishRef source _ | .destArg source _ | .destAbandon source _ | .destValue source _ |
                .destRelocate source _ _ | .destStage source _ | .destFit source _ | .destChild source _ _ => get source
              | .destOpen receiver _ _ _ _ => match receiver with
                | .slot slot => [.local slot]
                | .global global => [.global global]
                | .push reference | .append reference | .whole reference => get reference
                | .arg _ _ => []
              | .destNamed slot _ => [.local slot]
              | .call callee args _ | .callConstruct callee args _ _ =>
                  externalRoots (args.map get) ((returns[callee]?.getD []).flatten)
              | .result pack position => (packs[pack]?.getD [])[position]?.getD []
              | _ => []
            roots := roots.set! id ((get id ++ found).eraseDups)
        | .eff (.slotInit slot value _) => slots := slots.set! slot ((slots[slot]?.getD [] ++ get value).eraseDups)
        | .eff (.store reference value _) =>
            for root in get reference do
              if let .local slot := root then slots := slots.set! slot ((slots[slot]?.getD [] ++ get value).eraseDups)
        | .term term =>
            if let .invoke callee args _ _ _ _ _ := term then
              if let some definition := m.funcs[callee]? then
                for ((parameter,arg),position) in (definition.params.zip args).zipIdx do
                  if parameter matches .ref _ (.slice ..) then
                    let contents := callContents m f definition returns roots slots args position
                    for root in get arg do
                      if let .local slot := root then
                        slots := slots.set! slot ((slots[slot]?.getD [] ++ contents).eraseDups)
            for (target,args) in term.edges do
              if let some targetBlock := f.blocks[target]? then
                let skip := match term with
                  | .invoke callee _ _ normal _ _ _ =>
                      if target == normal then (m.funcs[callee]?).map (·.results.length) |>.getD 0 else targetBlock.params.length - args.length
                  | _ => 0
                if let .invoke callee callArgs _ normal _ escapeEdges _ := term then
                  let rows := if target == normal then returns[callee]?.getD [] else
                    match escapeEdges.find? (·.block == target) with
                    | some edge => returns[escapeResultIndex m callee edge.target]?.getD []
                    | none => []
                  for ((id,_),row) in targetBlock.params.zip rows do
                    roots := roots.set! id ((get id ++ externalRoots (callArgs.map get) row).eraseDups)
                for ((id,type), arg) in (targetBlock.params.drop skip).zip args do
                  roots := roots.set! id ((get id ++ get arg).eraseDups)
                  if type matches .pack .. then
                    packs := packs.set! id (mergeRootRows (packs[id]?.getD []) (packs[arg]?.getD []))
        | _ => pure ()
    if roots == previousRoots && slots == previousSlots && packs == previousPacks then break
  return (roots,slots)

private def valueRoots (m : Module) (f : Func) (returns : Array (List (List RootRef))) : Array (List RootRef) :=
  (storageRoots m f returns).1

private def resultRoots (m : Module) : Array (List (List RootRef)) := Id.run do
  let normal := m.funcs.map fun f => f.results.map fun _ => []
  let propagated := m.funcs.flatMap fun _ => m.targets.map fun target =>
    (m.funcs[target.first]?).map (fun member => member.results.map fun _ => []) |>.getD []
  let mut returns := normal ++ propagated ++ Array.replicate m.globals.size [[]]
  for _ in [0:m.funcs.size * (m.funcs.foldl (fun n f => n + f.numValues) 0) + 1] do
    let previous := returns
    for h : fi in [0:m.funcs.size] do
      let f := m.funcs[fi]
      let roots := valueRoots m f returns
      for block in f.blocks do
        for inst in block.insts do
          if let .eff (.store reference value _) := inst then
            let storing := (roots[value]?.getD []).flatMap (expandParameter f)
            for root in roots[reference]?.getD [] do
              let receiving := expandParameter f root
              for receiver in receiving do
                if let .global global := receiver then
                  let index := globalContentIndex m global
                  returns := returns.set! index [((returns[index]?.getD []).flatten ++ storing).eraseDups]
        match block.lastTerm? with
        | some (.ret operands _) =>
            let found := (returns[fi]?.getD []).zip operands |>.map fun (previous,id) => (previous ++ roots[id]?.getD []).eraseDups
            returns := returns.set! fi found
        | some (.escape target operands _ _) =>
            let index := escapeResultIndex m fi target
            let found := (returns[index]?.getD []).zip operands |>.map fun (previous,id) => (previous ++ roots[id]?.getD []).eraseDups
            returns := returns.set! index found
        | _ => pure ()
    if returns == previous then break
  return returns

private def checkLifetimes (m : Module) (f : Func) (returns : Array (List (List RootRef))) : Check Unit := do
  let roots := valueRoots m f returns
  let types := f.valueTypes m
  let mut entries : Array (Option (List Nat)) := Array.replicate f.blocks.size none
  entries := entries.set! 0 (some [])
  for _ in [0:f.blocks.size + 1] do
    for h : bi in [0:f.blocks.size] do
      if let some initial := (entries[bi]?).bind (fun value => value) then
        let mut scopes := initial
        for inst in f.blocks[bi].insts do
          for id in inst.uses do
            if ((types[id]?).bind (fun value => value)).any (fun type => type matches .data (.ref ..) | .data (.slice ..) | .view ..) then
              for root in roots[id]?.getD [] do
                if let .local slot := root then
                  let some slot := f.slots[slot]? | violation .v040 "reference root names missing local slot"
                  unless scopes.contains slot.scope do violation .v040 "reference/view use reaches storage outside its owning scope"
          match inst with
          | .eff (.enter scope) => scopes := scope :: scopes
          | .eff (.leave _) => scopes := scopes.tail
          | .term term =>
              for target in term.successors do
                entries := entries.set! target (some scopes)
              if let .escape target values _ _ := term then
                let some target := m.targets[target]? | violation .v001 "escape target missing"
                let some member := m.funcs[target.first]? | violation .v001 "escape target member missing"
                for (id,descriptor) in values.zip member.results do
                  if descriptor.ty matches .ref .. | .slice .. then
                    unless (roots[id]?.getD []).all (fun root => !(root matches .local _)) do
                      violation .v040 "nonlocal reference result reaches helper-local storage"
          | _ => pure ()

private def emptySummary : Summary := ⟨[],[],[],[],[],[],[],[],false,false⟩

private def unionSummary (left right : Summary) : Summary :=
  { reads := (left.reads ++ right.reads).eraseDups, writes := (left.writes ++ right.writes).eraseDups,
    grows := (left.grows ++ right.grows).eraseDups, shrinks := (left.shrinks ++ right.shrinks).eraseDups,
    rebinds := (left.rebinds ++ right.rebinds).eraseDups, constructs := (left.constructs ++ right.constructs).eraseDups,
    needs := (left.needs ++ right.needs).eraseDups, escapes := (left.escapes ++ right.escapes).eraseDups,
    aborts := left.aborts || right.aborts, outputs := left.outputs || right.outputs }

private def rootsTargets (roots : List RootRef) : List Target := roots.filterMap fun
  | .param i => some (.param i)
  | .global i => some (.global i)
  | _ => none


private def mapTargets (roots : Array (List RootRef)) (args : List ValueId) (targets : List Target) : List Target :=
  targets.flatMap fun
    | .global id => [.global id]
    | .param i => rootsTargets (roots[(args[i]?.getD roots.size)]?.getD [])

private def receiverType? (m : Module) (f : Func) (receiver : DestReceiver) : Option Ty :=
  match receiver with
  | .slot id => (f.slots[id]?).map (·.ty)
  | .global id => (m.globals[id]?).map (·.ty)
  | .arg callee position => (m.funcs[callee]?).bind fun f => f.params[position]?
  | .push reference => (m.environment f |>.refTy reference).toOption.bind fun (_,ty) => ty.element?
  | .append reference | .whole reference => (m.environment f |>.refTy reference).toOption.map (·.2)

private def constructionMaximum (m : Module) (f : Func) (provenance : Provenance) (id : ValueId) : Option Nat := Id.run do
  let owner := provenance.values[id]?.getD []
  let same (id : ValueId) := provenance.values[id]?.getD [] == owner
  let cyclic (start : Nat) := Id.run do
    let mut reached := ((f.blocks[start]?).bind Block.lastTerm?).map Term.successors |>.getD []
    for _ in [0:f.blocks.size] do
      for id in reached do
        reached := (reached ++ (((f.blocks[id]?).bind Block.lastTerm?).map Term.successors |>.getD [])).eraseDups
    return reached.contains start
  let env := m.environment f
  let mut costs : Array Nat := #[]
  for (block,index) in f.blocks.toList.zipIdx do
    let mut count := 0
    for inst in block.insts do
      match inst with
      | .eff (.destBytes destination bytes _) => if same destination then count := count + bytes.length
      | .eff (.destWrite destination _ _) | .eff (.destAttach destination _ _) => if same destination then count := count + 1
      | .eff (.destRepeat destination _ _) =>
          if same destination then
            match (env.destTy destination).toOption with
            | some (.arr _ length, _) => count := count + length
            | _ => return none
      | .eff (.destSnapshot destination snapshot _) =>
          if same destination then
            match (env.dataTy snapshot).toOption with
            | some (.arr _ length) => count := count + length
            | _ => return none
      | .eff (.destText destination _ _) | .eff (.destCopy destination _ _) => if same destination then return none
      | .def _ (.callConstruct callee _ destinations _) | .term (.invoke callee _ destinations _ _ _ _) =>
          let some callee := m.funcs[callee]? | return none
          let results := callee.results.filter (·.ty.nonfixed)
          for (destination,result) in destinations.zip results do
            if same destination then
              match result.ty with
              | .arr _ length => count := count + length
              | .limited _ capacity => count := count + capacity
              | .varr _ => count := count + (2^32 - 1)
              | _ => return none
      | _ => pure ()
    if count > 0 && cyclic index then return none
    costs := costs.push count
  let mut entries : Array (Option Nat) := Array.replicate f.blocks.size none
  entries := entries.set! 0 (some 0)
  let mut maximum := 0
  for _ in [0:f.blocks.size + 1] do
    for (block,index) in f.blocks.toList.zipIdx do
      if let some initial := (entries[index]?).join then
        let count := initial + costs[index]!
        maximum := max maximum count
        for successor in (block.lastTerm?.map Term.successors).getD [] do
          entries := entries.set! successor (some (max count ((entries[successor]?).join.getD 0)))
  return some maximum

private def deriveEffects (m : Module) (returns : Array (List (List RootRef))) : Array Summary := Id.run do
  let mut summaries := m.funcs.map fun _ => emptySummary
  for _ in [0:m.funcs.size * (m.globals.size + m.targets.size + 10) + 1] do
    for h : fi in [0:m.funcs.size] do
      let f := m.funcs[fi]
      let roots := valueRoots m f returns
      let provenance := f.provenance m fi
      let capacityAbort (id : ValueId) (ty : Ty) (request : Core.ConstructionRequest) := match ty with
        | .limited _ capacity => (constructionMaximum m f provenance id).all (· > capacity)
        | .varr _ => request == .value && (constructionMaximum m f provenance id).all (· >= 2^32)
        | _ => false
      let limited (id : ValueId) := ((m.environment f).refTy id).toOption.any (fun (_,ty) => ty matches .limited ..)
      let get (id : ValueId) := rootsTargets ((roots[id]?.getD []).flatMap (expandParameter f))
      let mut summary := emptySummary
      let addCall (summary : Summary) (callee : FnId) (args : List ValueId) :=
        let found := summaries[callee]?.getD emptySummary
        unionSummary summary { found with
          reads := mapTargets (roots.map (fun roots => roots.flatMap (expandParameter f))) args found.reads, writes := mapTargets (roots.map (fun roots => roots.flatMap (expandParameter f))) args found.writes,
          grows := mapTargets (roots.map (fun roots => roots.flatMap (expandParameter f))) args found.grows, shrinks := mapTargets (roots.map (fun roots => roots.flatMap (expandParameter f))) args found.shrinks,
          rebinds := mapTargets (roots.map (fun roots => roots.flatMap (expandParameter f))) args found.rebinds, constructs := [] }
      for block in f.blocks do
        for inst in block.insts do
          match inst with
          | .def _ (.load reference) | .def _ (.snapshot _ reference) | .def _ (.arrayLen reference) =>
              summary := unionSummary summary { emptySummary with reads := get reference }
          | .def _ (.push reference _ _) =>
              summary := unionSummary summary { emptySummary with grows := get reference, writes := get reference, aborts := limited reference }
          | .def _ (.pop reference _) =>
              summary := unionSummary summary { emptySummary with shrinks := get reference, reads := get reference, aborts := true }
          | .def _ (.call callee args _) | .def _ (.callConstruct callee args _ _) |
              .term (.invoke callee args _ _ _ _ _) => summary := addCall summary callee args
          | .def _ (.targetDest target _ _) | .term (.escape target _ _ _) =>
              summary := unionSummary summary { emptySummary with needs := [target], escapes := [target] }
          | .def id (.destOpen receiver logical request _ _) =>
              let receiving := (receiverType? m f receiver).getD logical
              let aborts := match receiver with
                | .append reference | .push reference => limited reference
                | _ => capacityAbort id receiving request
              let effect := match receiver with
                | .push reference | .append reference => { emptySummary with grows := get reference, writes := get reference, aborts }
                | .whole reference => { emptySummary with reads := get reference, grows := get reference, shrinks := get reference, writes := get reference, aborts }
                | _ => { emptySummary with aborts }
              summary := unionSummary summary effect
          | .def id (.destChild _ ty _) => summary := { summary with aborts := summary.aborts || capacityAbort id ty .value }
          | .def _ (.destFit ..) => pure ()
          | .def _ (.bin op ..) =>
              if op matches .add | .sub | .mul | .div | .mod then summary := { summary with aborts := true }
          | .def _ (.un .neg ..) | .def _ (.conv .as ..) | .def _ (.viewSlice ..) | .def _ (.indexChecked ..) => summary := { summary with aborts := true }
          | .eff (.store reference _ _) =>
              summary := unionSummary summary { emptySummary with writes := get reference, rebinds := storageRebinds f roots reference }
          | .eff (.destCopy _ source _) | .eff (.destText _ source _) | .def _ (.render source _) => summary := unionSummary summary { emptySummary with reads := get source }
          | .eff (.append reference source _) => summary := unionSummary summary { emptySummary with grows := get reference, writes := get reference, reads := get source, aborts := limited reference }
          | .eff (.appendValue reference _ _) => summary := unionSummary summary { emptySummary with grows := get reference, writes := get reference, aborts := limited reference }
          | .eff (.popN reference _ _) => summary := unionSummary summary { emptySummary with reads := get reference, shrinks := get reference, aborts := true }
          | .eff (.clear reference _) => summary := unionSummary summary { emptySummary with reads := get reference, shrinks := get reference }
          | .eff (.resize reference _ fill _) => summary := unionSummary summary { emptySummary with reads := get reference, writes := if fill.isSome then get reference else [], grows := if fill.isSome then get reference else [], shrinks := get reference, aborts := true }
          | .eff (.print parts _) =>
              let reads := parts.flatMap fun
                | .val id => get id
                | .text _ => []
              summary := unionSummary summary { emptySummary with reads, outputs := true }
          | .term (.abort ..) => summary := { summary with aborts := true }
          | .term (.ret _ _) => summary := { summary with constructs := f.results.zipIdx |>.filterMap fun (r,i) => if r.ty.nonfixed then some i else none }
          | _ => pure ()
      let handled := m.targets.toList.zipIdx |>.filterMap fun (target,index) => if target.contains fi then some index else none
      summary := { summary with needs := summary.needs.filter (!handled.contains ·), escapes := summary.escapes.filter (!handled.contains ·) }
      summaries := summaries.set! fi summary
  return summaries

private def included [BEq α] (actual declared : List α) : Bool := actual.all declared.contains


private def checkParameterRoots (m : Module) (returns : Array (List (List RootRef))) : Check Unit := do
  for f in m.funcs do
    let (roots,slots) := storageRoots m f returns
    for block in f.blocks do
      for inst in block.insts do
        let call? : Option (FnId × List ValueId) := match inst with
          | .def _ (.call callee args _) | .def _ (.callConstruct callee args _ _) | .term (.invoke callee args _ _ _ _ _) => some (callee,args)
          | _ => none
        if let some (callee,args) := call? then
          let some callee := m.funcs[callee]? | violation .v001 "callee missing in root analysis"
          for ((parameter,arg),position) in (callee.params.zip args).zipIdx do
            if parameter matches .ref .. | .slice .. then
              let expected := (roots[arg]?.getD []).flatMap (expandParameter f)
              let declared := (callee.roots.params.find? (·.1 == position)).map (·.2) |>.getD []
              let mapped := declared.flatMap fun
                | .global global => [RootRef.global global]
                | .static => [.static]
                | .param source => (roots[args[source]?.getD roots.size]?.getD []).flatMap (expandParameter f)
                | .local _ => []
              unless included expected mapped do violation .v050 "callee parameter roots omit backing storage supplied at a call"
            if parameter matches .ref _ (.slice ..) then
              let actual := argumentContents m f returns roots slots arg
              let mapped := callContents m f callee returns roots slots args position
              unless included actual mapped do violation .v050 "callee content roots omit slice backing storage supplied at a call"

private def checkStoredContents (m : Module) (returns : Array (List (List RootRef))) : Check Unit := do
  for f in m.funcs do
    let roots := valueRoots m f returns
    for block in f.blocks do
      for inst in block.insts do
        if let .eff (.store reference value _) := inst then
          for root in roots[reference]?.getD [] do
            if let .param position := root then
              if (f.params[position]?).any (fun ty => ty matches .ref _ (.slice ..)) then
                let actual := (roots[value]?.getD []).flatMap (expandParameter f)
                let declared := (f.roots.contents.find? (·.1 == position)).map (·.2) |>.getD []
                unless included actual (declared.flatMap (expandParameter f)) do
                  violation .v050 "slice store backing roots escape the parameter's declared contents"

private def declaredEffectTargets (f : Func) (targets : List Target) : List Target :=
  targets.flatMap fun
    | .param position => Target.param position :: rootsTargets (expandParameter f (.param position))
    | .global global => [.global global]

private def checkSummaries (m : Module) (returns : Array (List (List RootRef))) (derived : Array Summary) : Check Unit := do
  for h : fi in [0:m.funcs.size] do
    let f := m.funcs[fi]
    let actual := derived[fi]?.getD emptySummary
    if let .known declared := f.summary then
      for block in f.blocks do
        for inst in block.insts do
          let callee? := match inst with
            | .def _ (.call callee ..) | .def _ (.callConstruct callee ..) | .term (.invoke callee ..) => some callee
            | _ => none
          if let some callee := callee? then
            unless (m.funcs[callee]?).any (fun f => f.summary matches .known _) do violation .v050 "known summary calls unknown callee summary"
      unless included actual.reads (declaredEffectTargets f declared.reads) && included actual.writes (declaredEffectTargets f declared.writes) &&
          included actual.grows (declaredEffectTargets f declared.grows) && included actual.shrinks (declaredEffectTargets f declared.shrinks) &&
          included actual.rebinds (declaredEffectTargets f declared.rebinds) && included actual.constructs declared.constructs &&
          included actual.needs declared.needs && included actual.escapes declared.escapes &&
          (!actual.aborts || declared.aborts) && (!actual.outputs || declared.outputs) do
        violation .v050 "effect summary omits independently derived body/callee effects"
    let actualRoots := returns[fi]?.getD []
    for (descriptor, roots, index) in (f.results.zip actualRoots |>.zipIdx).map (fun ((r,rs),i) => (r,rs,i)) do
      if descriptor.ty.nonfixed then
        unless (f.roots.results[index]?.getD []).isEmpty do violation .v050 "nonfixed result has reference roots"
      else if descriptor.ty matches .ref .. | .slice .. then
        unless roots.all (fun root => !(root matches .local _)) do violation .v040 "reference result points into local/by-value parameter storage"
        unless included (roots.flatMap (expandParameter f)) (f.roots.results[index]?.getD []) do violation .v050 "result root annotation omits derived backing roots"

structure Ownership where
  live : List ValueId := []
  named : List SlotId := []
  suspended : List (ValueId × ValueId) := []
  projections : List (ValueId × Nat) := []
  arguments : List (ValueId × FnId × Nat) := []
  availableSlots : List SlotId := []
  allocatedSlots : List SlotId := []
  stagedOwners : List DestinationOwner := []
  suspendedNamed : List SlotId := []
  deriving DecidableEq, Repr

private def protocolType : VTy → Bool
  | .dest .. | .built .. | .cancelled .. => true
  | .pack rs => rs.any (fun r => r.ty.nonfixed)
  | _ => false

private def consume (state : Ownership) (id : ValueId) : Check Ownership := do
  unless state.live.contains id do violation .v060 "linear carrier is unavailable or already consumed"
  unless !(state.suspended.any (fun pair => pair.1 == id)) do violation .v060 "parent destination is suspended by child"
  pure { state with live := state.live.filter (· != id) }

private def remapOwnership (state : Ownership) (params : List (ValueId × VTy)) (args : List ValueId) : Ownership :=
  let rename (id : ValueId) := ((args.zip (params.map (·.1))).find? (·.1 == id)).map (·.2) |>.getD id
  { state with
    live := (state.live.map rename).eraseDups
    suspended := state.suspended.map (fun (a,b) => (rename a,rename b))
    projections := state.projections.map (fun (a,b) => (rename a,b))
    arguments := state.arguments.map (fun (a,b,c) => (rename a,b,c)) }

private def fixedPackUse (type : VTy) (id : ValueId) (inst : Inst) : Bool :=
  match type, inst with
  | .pack descriptors, .def _ (.result pack position) =>
      pack == id && (descriptors[position]?).any (!·.ty.nonfixed)
  | .pack _, .term (.br ..) | .pack _, .term (.condbr ..) | .pack _, .term (.invoke ..) => true
  | _, _ => false

private def checkOwnership (m : Module) (functionId : FnId) (f : Func) (returns : Array (List (List RootRef))) (derived : Array Summary) : Check Unit := do
  let types := f.valueTypes m
  let roots := valueRoots m f returns
  let provenance := f.provenance m functionId
  let getRoots (id : ValueId) := (roots[id]?.getD []).flatMap (expandParameter f)
  let typeOf (id : ValueId) := ((types[id]?).bind (fun value => value)).getD (.data .unit)
  let mut entries : Array (Option Ownership) := Array.replicate f.blocks.size none
  let some entry := f.blocks[0]? | violation .v001 "ownership entry missing"
  entries := entries.set! 0 (some { live := entry.params.filterMap fun (id,t) => if protocolType t then some id else none })
  for _ in [0:f.blocks.size + 1] do
    for h : bi in [0:f.blocks.size] do
      if let some initial := (entries[bi]?).bind (fun value => value) then
        let mut state := initial
        for inst in f.blocks[bi].insts do
          for id in inst.uses do
            unless !(getRoots id).any (fun root => match root with | .local slot => state.suspendedNamed.contains slot | _ => false) do
              violation .v060 "alternate result expression reaches suspended named local"
            let observes := match inst with
              | .def _ (.load _) | .def _ (.snapshot ..) | .def _ (.render ..) | .def _ (.destOpen ..) | .def _ (.arrayLen _) | .def _ (.push ..) | .def _ (.pop ..) | .def _ (.call ..) | .def _ (.callConstruct ..) | .term (.invoke ..) => true
              | .eff (.store ..) | .eff (.append ..) | .eff (.appendValue ..) | .eff (.popN ..) | .eff (.resize ..) | .eff (.clear ..) | .eff (.destCopy ..) | .eff (.destText ..) | .eff (.print ..) => true
              | _ => false
            if observes && !protocolType (typeOf id) then
              for root in getRoots id do
                if let .local slot := root then
                  unless state.availableSlots.contains slot do violation .v060 "reference/view observes unpublished or uninitialized local receiving storage"
            if protocolType (typeOf id) then
              unless state.live.contains id || fixedPackUse (typeOf id) id inst do violation .v060 "use of consumed linear carrier"
            if state.arguments.any (fun (argument,_,_) => argument == id) then
              unless inst matches .def _ (.call ..) | .def _ (.callConstruct ..) | .term (.invoke ..) do
                violation .v060 "owned constructed argument has a use outside its associated call"
          let changed : List RootRef := match inst with
            | .def _ (.destOpen (.append reference) ..) | .def _ (.destOpen (.push reference) ..) | .def _ (.destOpen (.whole reference) ..) => getRoots reference
            | .eff (.store reference ..) => (storageRebinds f roots reference).flatMap fun
                | .param position => expandParameter f (.param position)
                | .global global => [.global global]
            | .def _ (.push receiver ..) | .def _ (.pop receiver ..) | .eff (.append receiver ..) |
              .eff (.appendValue receiver ..) | .eff (.popN receiver ..) | .eff (.resize receiver ..) |
              .eff (.clear receiver ..) => getRoots receiver
            | .def _ (.call callee args _) | .def _ (.callConstruct callee args _ _) | .term (.invoke callee args _ _ _ _ _) =>
                let summary := derived[callee]?.getD emptySummary
                (summary.grows ++ summary.shrinks ++ summary.rebinds).flatMap fun
                  | Target.global global => [RootRef.global global]
                  | Target.param position => getRoots (args[position]?.getD roots.size)
            | _ => []
          let accessed : List RootRef := match inst with
            | .def _ (.load reference) | .def _ (.snapshot _ reference) | .def _ (.arrayLen reference) |
                .def _ (.render reference _) | .def _ (.viewLen reference) | .def _ (.sliceView reference) |
                .def _ (.viewSlice _ reference ..) | .def _ (.fieldAddr reference _) |
                .eff (.store reference ..) | .eff (.destCopy _ reference _) | .eff (.destText _ reference _) => getRoots reference
            | .eff (.print parts _) => parts.flatMap fun
                | .val id => getRoots id
                | .text _ => []
            | .def _ (.call callee args _) | .def _ (.callConstruct callee args _ _) | .term (.invoke callee args _ _ _ _ _) =>
                let summary := derived[callee]?.getD emptySummary
                (summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds).flatMap fun
                  | Target.global global => [RootRef.global global]
                  | Target.param position => getRoots (args[position]?.getD roots.size)
            | _ => changed
          for live in state.live do
            for owner in provenance.values[live]?.getD [] do
              let receivingRoots := match owner with
                | .receiver (.push reference) | .receiver (.append reference) | .receiver (.whole reference) => getRoots reference
                | _ => []
              unless !(changed.any receivingRoots.contains) do violation .v060 "C-NOGROW: mutation reaches active receiving storage"
              if owner matches .receiver (.whole _) then
                unless !(accessed.any receivingRoots.contains) do violation .v060 "whole replacement operand reaches cleared receiver"
          let consumeCall (state : Ownership) (callee : FnId) (args destinations : List ValueId) : Check Ownership := do
            let some calleeDef := m.funcs[callee]? | violation .v001 "callee missing for argument ownership"
            for (parameter,arg) in calleeDef.params.zip args do
              if parameter.nonfixed then
                unless state.arguments.any (fun (id,_,_) => id == arg) do violation .v060 "nonfixed by-value call argument lacks exactly associated owned completion"
            let mut state := state
            for (arg,position) in args.zipIdx do
              if let some (_,expected,expectedPosition) := state.arguments.find? (fun (id,_,_) => id == arg) then
                unless expected == callee && expectedPosition == position do violation .v060 "constructed argument transferred to wrong callee/parameter"
                state := { state with arguments := state.arguments.filter (fun (id,_,_) => id != arg) }
            for destination in destinations do state ← consume state destination
            pure state
          match inst with
          | .def result op =>
              match op with
              | .destOpen (.slot slot) .. =>
                  unless !state.allocatedSlots.contains slot do violation .v060 "receiving slot is initialized more than once in one scope activation"
                  state := { state with allocatedSlots := slot :: state.allocatedSlots }
              | .slotAddr slot =>
                  unless !state.suspendedNamed.contains slot do violation .v060 "alternate result names suspended local"
              | .resultExitDest position _ =>
                  if let some slot := (f.results[position]?).bind (·.namedLocal) then
                    state := { state with suspendedNamed := slot :: state.suspendedNamed }
              | .destChild parent _ _ =>
                  unless !(state.suspended.any (fun pair => pair.1 == parent)) do violation .v060 "parent already has pending child"
                  state := { state with suspended := (parent,result) :: state.suspended }
              | .destFinish id _ | .destValue id _ | .destRelocate id _ _ | .destFit id _ | .destStage id _ | .destAbandon id _ =>
                  let owners := provenance.values[id]?.getD []
                  match op with
                  | .destStage .. =>
                      unless !(owners.any state.stagedOwners.contains) do violation .v060 "receiving destination is staged more than once"
                      state := { state with stagedOwners := (owners ++ state.stagedOwners).eraseDups }
                  | .destFit .. =>
                      unless owners.all state.stagedOwners.contains do violation .v060 "fit has no outstanding receiving stage"
                      state := { state with stagedOwners := state.stagedOwners.filter (!owners.contains ·) }
                  | .destAbandon .. => state := { state with stagedOwners := state.stagedOwners.filter (!owners.contains ·) }
                  | _ => pure ()
                  state ← consume state id
                  state := { state with suspended := state.suspended.map fun (parent,child) => (parent,if child == id then result else child) }
              | .destPublishRef built _ =>
                  unless !(provenance.values[built]?.getD []).any state.stagedOwners.contains do violation .v060 "staged push publication requires fit"
                  state ← consume state built
              | .destArg built _ =>
                  state ← consume state built
                  let rec producer : Nat → ValueId → Option (FnId × Nat)
                    | 0, _ => none
                    | fuel + 1, id => do
                        let inst ← f.blocks.toList.flatMap (·.insts) |>.find? fun
                          | .def result _ => result == id
                          | _ => false
                        match inst with
                        | .def _ (.destOpen (.arg callee position) ..) => some (callee,position)
                        | .def _ (.destFinish input _) | .def _ (.destFit input _) | .def _ (.destStage input _) => producer fuel input
                        | _ => none
                  let some (callee,position) := producer f.numValues built | violation .v060 "dest_arg completion has no dr_arg provenance"
                  state := { state with arguments := (result,callee,position) :: state.arguments }
              | .destNamed slot _ =>
                  unless state.named.contains slot do violation .v060 "named result is unbound or already returned"
                  state := { state with named := state.named.filter (· != slot), availableSlots := state.availableSlots.filter (· != slot) }
              | .destAbandonNamed slot _ _ =>
                  unless state.named.contains slot do violation .v060 "named abandonment has no bound alias"
                  state := { state with named := state.named.filter (· != slot), availableSlots := state.availableSlots.filter (· != slot) }
              | .result pack position =>
                  if protocolType (typeOf result) then
                    unless !(state.projections.contains (pack,position)) do violation .v060 "nonfixed pack component projected twice"
                    state := { state with projections := (pack,position) :: state.projections }
                    if let .pack descriptors := typeOf pack then
                      let required := descriptors.zipIdx |>.filterMap fun (r,i) => if r.ty.nonfixed then some i else none
                      if required.all (fun i => state.projections.contains (pack,i)) then
                        state ← consume state pack
                        state := { state with projections := state.projections.filter (fun (id,_) => id != pack) }
              | .callConstruct callee args destinations _ => state ← consumeCall state callee args destinations
              | .call callee args _ => state ← consumeCall state callee args []
              | _ => pure ()
              if protocolType (typeOf result) then state := { state with live := result :: state.live }
          | .eff effect => match effect with
              | .slotInit slot _ _ =>
                  unless !state.allocatedSlots.contains slot do violation .v060 "local slot is initialized more than once in one scope activation"
                  state := { state with availableSlots := slot :: state.availableSlots, allocatedSlots := slot :: state.allocatedSlots }
              | .leave scope =>
                  unless !state.named.any (fun slot => (f.slots[slot]?).any (·.scope == scope)) do violation .v060 "named result ownership survives scope leave without completion/cancellation"
                  state := { state with
                    availableSlots := state.availableSlots.filter (fun slot => (f.slots[slot]?).any (·.scope != scope))
                    allocatedSlots := state.allocatedSlots.filter (fun slot => (f.slots[slot]?).any (·.scope != scope)) }
              | .destAttach parent child _ =>
                  unless state.suspended.contains (parent,child) do violation .v060 "child attach does not match suspended parent"
                  state ← consume state child
                  state := { state with suspended := state.suspended.filter (· != (parent,child)) }
              | .destBind slot built _ =>
                  state ← consume state built
                  unless !state.allocatedSlots.contains slot do violation .v060 "named result slot is initialized more than once"
                  state := { state with named := slot :: state.named, availableSlots := slot :: state.availableSlots, allocatedSlots := slot :: state.allocatedSlots }
              | .destRepeat parent source _ =>
                  unless !(state.suspended.any (fun pair => pair.1 == parent)) do violation .v060 "repeat writes suspended parent"
                  state ← consume state source
              | .destPublish built _ =>
                  unless !(provenance.values[built]?.getD []).any state.stagedOwners.contains do violation .v060 "staged completion is published before fit"
                  for owner in provenance.values[built]?.getD [] do
                    if let .receiver (.slot slot) := owner then state := { state with availableSlots := slot :: state.availableSlots }
                  state ← consume state built
              | .destCancel built _ => state ← consume state built
              | .destWrite parent _ _ | .destBytes parent _ _ | .destText parent _ _ | .destCopy parent _ _ | .destSnapshot parent _ _ =>
                  unless !(state.suspended.any (fun pair => pair.1 == parent)) do violation .v060 "write to suspended parent destination"
              | _ => pure ()
          | .term term =>
              match term with
              | .ret operands _ | .escape _ operands _ _ =>
                  let ids := match term with | .escape _ _ cancelled _ => operands ++ cancelled | _ => operands
                  for id in operands do
                    if protocolType (typeOf id) then
                      unless !(provenance.values[id]?.getD []).any state.stagedOwners.contains do violation .v060 "staged completion is transferred before fit"
                  for id in ids do if protocolType (typeOf id) then state ← consume state id
                  unless state.live.isEmpty && state.named.isEmpty && state.arguments.isEmpty do violation .v060 "return/escape leaks destination, completion, cancellation or argument ownership"
              | .invoke callee args destinations normal forwarded escapes _ =>
                  state ← consumeCall state callee args destinations
                  let some callee := m.funcs[callee]? | violation .v001 "invoke callee missing"
                  for (target,args) in term.edges do
                    let some targetBlock := f.blocks[target]? | violation .v020 "invoke successor missing"
                    let leadingCount := targetBlock.params.length - args.length
                    let mut edgeState := remapOwnership state (targetBlock.params.drop leadingCount) args
                    for (id,t) in targetBlock.params.take leadingCount do
                      if protocolType t then edgeState := { edgeState with live := id :: edgeState.live }
                    match entries[target]? with
                    | some (some previous) => unless previous == edgeState do violation .v060 "linear ownership differs at invoke join"
                    | some none => entries := entries.set! target (some edgeState)
                    | none => violation .v020 "invoke successor outside blocks"
                  let _ := (normal,forwarded,escapes,callee)
              | _ =>
                  for (target,args) in term.edges do
                    let some block := f.blocks[target]? | violation .v020 "ownership branch outside blocks"
                    let edgeState := remapOwnership state block.params args
                    match entries[target]? with
                    | some (some previous) => unless previous == edgeState do violation .v060 "linear ownership differs across CFG join"
                    | some none => entries := entries.set! target (some edgeState)
                    | none => violation .v020 "ownership successor outside blocks"

private def checkTargets (m : Module) (derived : Array Summary) (initializers : List FnId) : Check Unit := do
  for target in m.targets do
    let some first := m.funcs[target.first]? | violation .v001 "target member missing"
    for member in target.rest do
      let some member := m.funcs[member]? | violation .v001 "target member missing"
      unless (member.results.map fun r => (r.ty,r.request)) == (first.results.map fun r => (r.ty,r.request)) do
        violation .v010 "target members have different result channels"
  let mut available : Array (Option (List Nat)) := Array.replicate m.funcs.size none
  available := available.set! m.entry (some [])
  for initializer in initializers do available := available.set! initializer (some [])
  for _ in [0:m.funcs.size * (m.targets.size + 1) + 1] do
    for h : fi in [0:m.funcs.size] do
      if let some inherited := (available[fi]?).bind (fun value => value) then
        let handled := m.targets.toList.zipIdx |>.filterMap fun (t,i) => if t.contains fi then some i else none
        let active := (handled ++ inherited).eraseDups
        let f := m.funcs[fi]
        let required := if initializers.contains fi then (derived[fi]?.getD emptySummary).needs else
          match f.summary with | .known s => s.needs | .unknown => (List.range m.targets.size)
        unless included required active do violation .v070 "target requirement unavailable on an enclosing call path"
        for block in f.blocks do
          for inst in block.insts do
            let call? : Option (FnId × Bool × List Nat) := match inst with
              | .def _ (.call callee _ _) | .def _ (.callConstruct callee _ _ _) => some (callee,false,[])
              | .term (.invoke callee _ _ _ _ edges _) => some (callee,true,edges.map (·.target))
              | _ => none
            if let some (callee,invoke,edges) := call? then
              let some calleeDef := m.funcs[callee]? | violation .v001 "callee outside functions"
              let escapes := match calleeDef.summary with | .known s => s.escapes | .unknown => List.range m.targets.size
              unless included (derived[callee]?.getD emptySummary).escapes escapes do violation .v050 "callee escape annotation incomplete"
              if invoke then
                unless edges == escapes do violation .v070 "invoke escape edges differ from possible propagated targets"
              else unless escapes.isEmpty do violation .v070 "plain call may propagate an escape"
              let current := (available[callee]?).bind (fun value => value)
              let next := match current with | none => active | some current => current.filter active.contains
              available := available.set! callee (some next)
            match inst with
            | .def _ (.targetDest target _ _) => unless active.contains target do violation .v070 "target destination has no active member"
            | .term (.escape target _ _ _) =>
                unless active.contains target && !handled.contains target do violation .v070 "escape must propagate to an enclosing target member"
            | _ => pure ()

private def checkKnownCounts (m : Module) (f : Func) : Check Unit := do
  for block in f.blocks do
    for (inst,index) in block.insts.zipIdx do
      if let .def destination (.destOpen _ receivingType _ (some known) _) := inst then
        if let some (.constInt _ expected) := f.defOp? known then
          if expected < 0 then continue
          let mut aliases := [destination]
          let mut count := some 0
          for inst in block.insts.drop (index + 1) do
            match inst with
            | .eff (.destBytes destination bytes _) => if aliases.contains destination then count := count.map (· + bytes.length)
            | .eff (.destWrite destination _ _) | .eff (.destAttach destination _ _) => if aliases.contains destination then count := count.map (· + 1)
            | .eff (.destRepeat destination _ _) =>
                if aliases.contains destination then
                  match receivingType with
                  | .arr _ length => count := count.map (· + length)
                  | _ => count := none
            | .eff (.destSnapshot destination snapshot _) =>
                if aliases.contains destination then
                  match (m.environment f |>.dataTy snapshot).toOption with
                  | some (.arr _ length) => count := count.map (· + length)
                  | _ => count := none
            | .eff (.destText destination _ _) | .eff (.destCopy destination _ _) => if aliases.contains destination then count := none
            | .def result (.destStage source _) | .def result (.destValue source _) => if aliases.contains source then aliases := result :: aliases
            | .def _ (.callConstruct _ _ destinations _) | .term (.invoke _ _ destinations _ _ _ _) => if destinations.any aliases.contains then count := none
            | .def _ (.destFinish destination _) =>
                if aliases.contains destination then
                  if let some completedCount := count then
                    unless completedCount == expected.toNat do violation .v060 "known destination element count differs from completed writes"
                  break
            | .term _ => break
            | _ => pure ()

private def checkPermissions (m : Module) (f : Func) : Check Unit := do
  let env := m.environment f
  let permissions := f.permissions m env.vals
  let binding (id : ValueId) : Check Unit :=
    unless (permissions[id]?.getD (false,false)).1 do violation .v030 "mutation requires writable binding provenance"
  let contents (id : ValueId) : Check Unit :=
    unless (permissions[id]?.getD (false,false)).2 do violation .v030 "mutation requires writable contents provenance"
  for block in f.blocks do
    for inst in block.insts do
      match inst with
      | .eff (.store reference ..) => binding reference
      | .eff (.append reference ..) | .eff (.appendValue reference ..) | .eff (.popN reference ..) |
          .eff (.resize reference ..) | .eff (.clear reference ..) | .def _ (.push reference ..) | .def _ (.pop reference ..) => contents reference
      | .def _ (.destOpen (.append reference) ..) | .def _ (.destOpen (.push reference) ..) => contents reference
      | .def _ (.destOpen (.whole reference) ..) => binding reference
      | _ => pure ()

private def checkChannelOwners (m : Module) (functionId : FnId) (f : Func) : Check Unit := do
  let provenance := f.provenance m functionId
  let owners (id : ValueId) := provenance.values[id]?.getD []
  let requireOwner (id : ValueId) (owner : DestinationOwner) : Check Unit :=
    unless owners id == [owner] do violation .v060 "carrier does not belong to the exact receiving channel"
  let env := m.environment f
  let receiverType (owner : DestinationOwner) : Option Ty := match owner with
    | .receiver (.slot slot) => (f.slots[slot]?).map (·.ty)
    | .receiver (.global global) => (m.globals[global]?).map (·.ty)
    | .receiver (.arg callee position) => (m.funcs[callee]?).bind fun f => f.params[position]?
    | .receiver (.append reference) | .receiver (.whole reference) => (env.refTy reference).toOption.map (·.2)
    | .receiver (.push reference) => (env.refTy reference).toOption.bind fun (_,ty) => ty.element?
    | .result position => (f.results[position]?).map (·.ty)
    | .target target position => ((m.targets[target]?).bind fun t => m.funcs[t.first]?).bind fun f => (f.results[position]?).map (·.ty)
    | .child _ => none
  let rec sourceOp : Nat → ValueId → (Op → Bool) → Bool
    | 0, _, _ => false
    | fuel + 1, id, predicate =>
        match f.defOp? id with
        | some op =>
            if predicate op then true else match op with
            | .destFinish input _ | .destValue input _ | .destStage input _ | .destFit input _ |
                .destRelocate input _ _ => sourceOp fuel input predicate
            | _ => false
        | none => false
  for block in f.blocks do
    for inst in block.insts do
      match inst with
      | .term (.ret operands _) =>
          for ((id,descriptor),position) in (operands.zip f.results).zipIdx do
            if descriptor.ty.nonfixed then requireOwner id (.result position)
      | .term (.escape target operands cancellations _) =>
          let some targetDef := m.targets[target]? | violation .v001 "escape target missing"
          let some member := m.funcs[targetDef.first]? | violation .v001 "target member missing"
          for ((id,descriptor),position) in (operands.zip member.results).zipIdx do
            if descriptor.ty.nonfixed then requireOwner id (.target target position)
          let positions := f.results.zipIdx |>.filterMap fun (r,i) => if r.ty.nonfixed then some i else none
          for (id,position) in cancellations.zip positions do requireOwner id (.result position)
      | .eff (.destPublish id _) =>
          let [.receiver receiver] := owners id | violation .v060 "publication requires owning source receiver"
          if receiver matches .arg .. then violation .v060 "argument completion requires dest_arg transfer"
      | .eff (.destRepeat destination source _) =>
          let [.receiver (.slot sourceSlot)] := owners source | violation .v060 "repeat source must be unpublished private slot completion"
          unless !(f.results.any (·.namedLocal == some sourceSlot)) do violation .v060 "repeat source cannot alias receiving result storage"
          unless !(owners destination).any (fun owner => owner == .receiver (.slot sourceSlot)) do violation .v060 "repeat source and destination storage overlap"
      | .eff (.destBind slot id _) =>
          let some position := f.results.findIdx? (·.namedLocal == some slot) | violation .v060 "binding slot is not named result"
          requireOwner id (.result position)
      | .def _ (.destPublishRef id _) =>
          unless (owners id).any (fun owner => owner matches .receiver (.push ..)) && (owners id).length == 1 do
            violation .v060 "reference publication requires exact push receiving channel"
      | .def _ (.destArg id _) =>
          unless (owners id).all (fun owner => owner matches .receiver (.arg ..)) && !(owners id).isEmpty do
            violation .v060 "constructed argument lacks associated parameter receiving storage"
      | .def _ (.destAbandonNamed slot replacement _) =>
          let some position := f.results.findIdx? (·.namedLocal == some slot) | violation .v060 "named abandonment alias missing"
          let exactTarget : Bool := match owners replacement with
            | [.target target result] => result == position && (m.targets[target]?).any (fun target => target.contains functionId)
            | _ => false
          unless exactTarget do
            requireOwner replacement (.result position)
            unless sourceOp f.numValues replacement (fun op => match op with
              | .resultExitDest result _ => result == position
              | _ => false) do
              violation .v060 "named replacement does not originate at this activation result exit destination"
      | .def _ (.destRelocate id reason _) =>
          match reason with
          | .headerRemoval =>
              unless sourceOp f.numValues id (fun op => op matches .destValue ..) do violation .v060 "header removal lacks element_run to value adaptation"
          | .exitValue =>
              unless sourceOp f.numValues id (fun op => op matches .resultExitDest .. | .targetDest ..) ||
                (owners id).any (fun owner => owner matches .target ..) do violation .v060 "exit relocation lacks saved replacement channel/start"
      | .def _ (.destStage id _) =>
          unless (owners id).any (fun owner => (receiverType owner).any (fun ty => ty matches .limited ..)) do violation .v060 "stage does not receive into limited storage"
          unless sourceOp f.numValues id (fun op => match op with | .destOpen _ _ _ none _ => true | _ => false) do
            violation .v060 "stage requires unknown length at receiving open"
      | _ => pure ()

private def checkRenderedSnapshots (f : Func) : Check Unit := do
  let rendered := f.blocks.toList.flatMap (·.insts) |>.filterMap fun
    | .def result (.render ..) => some result
    | _ => none
  for block in f.blocks do
    for inst in block.insts do
      for id in inst.uses do
        if rendered.contains id then
          match inst with
          | .eff (.print ..) => pure ()
          | .eff (.destText _ source _) => unless source == id do violation .v060 "rendered snapshot only supplies text operand"
          | _ => violation .v060 "operand-time rendered snapshot escapes its print/text consumer"

private inductive CopyOrigin
  | descriptor | unmaterialized
  deriving DecidableEq

private def checkCopyOrigins (m : Module) (f : Func) : Check Unit := do
  let types := f.valueTypes m
  let slice (id : ValueId) := ((types[id]?).join).any (fun ty => ty matches .data (.slice ..))
  let mut origins : Array (List CopyOrigin) := Array.replicate f.numValues []
  if let some entry := f.blocks[0]? then
    for (id,type) in entry.params.take f.params.length do
      if type matches .data (.slice ..) then origins := origins.set! id [.descriptor]
  for _ in [0:f.numValues + 1] do
    let previous := origins
    for block in f.blocks do
      for inst in block.insts do
        let get (id : ValueId) : List CopyOrigin := origins[id]?.getD []
        match inst with
        | .def id op =>
            let found : List CopyOrigin := match op with
              | .snapshot .. => [.descriptor]
              | .load _ => if slice id then [.descriptor] else []
              | .bytes .. | .render .. => [.unmaterialized]
              | .call .. | .callConstruct .. | .result .. => if slice id then [.unmaterialized] else []
              | .sliceView source | .viewSlice _ source .. => get source
              | _ => []
            origins := origins.set! id ((get id ++ found).eraseDups)
        | .term term =>
            for (target,args) in term.edges do
              if let some destination := f.blocks[target]? then
                let skip := match term with
                  | .invoke callee _ _ normal _ _ _ =>
                      if target == normal then (m.funcs[callee]?).map (·.results.length) |>.getD 0 else destination.params.length - args.length
                  | _ => 0
                for (id,type) in destination.params.take skip do
                  if type matches .data (.slice ..) then origins := origins.set! id ((get id ++ [CopyOrigin.unmaterialized]).eraseDups)
                for ((id,_),arg) in (destination.params.drop skip).zip args do
                  origins := origins.set! id ((get id ++ get arg).eraseDups)
        | _ => pure ()
    if origins == previous then break
  for block in f.blocks do
    for inst in block.insts do
      if let .eff (.destCopy _ source _) := inst then
        if !((types[source]?).join).any (fun ty => ty matches .data (.ref ..)) then
          unless origins[source]?.getD [] == [.descriptor] do
            violation .v060 "ordinary copy requires a materialized source descriptor or sampled storage place"

private def checkOrigins (m : Module) (f : Func) : Check Unit := do
  for block in f.blocks do
    for inst in block.insts do
      if let some org := inst.origin? then
        let some org := org | violation .v100 "instruction requires origin"
        unless org < m.origins.size do violation .v100 "instruction origin outside table"

private def checkCertificates (m : Module) (f : Func) : Check Unit :=
  (checkEvidence m f (f.valueTypes m)).mapError fun message => ⟨.v080,message⟩

namespace Validate

def validate (m : Module) : Check Unit := do
  unless m.entry < m.funcs.size do violation .v001 "entry outside function table"
  for type in m.types do
    match type with
    | .data ty => unless allTypesValid m ty do violation .v010 "invalid data type table entry"
    | .view _ element => unless (element.flat || element.variableElement) && allTypesValid m element do violation .v010 "invalid sampled view element"
    | .dest ty _ | .built ty _ | .cancelled ty _ => unless ty.nonfixed && allTypesValid m ty do violation .v010 "invalid protocol receiving type"
    | .pack descriptors =>
        unless descriptors.length >= 2 do violation .v010 "result pack requires several positions"
        for descriptor in descriptors do
          unless allTypesValid m descriptor.ty && (descriptor.ty.storable || descriptor.ty == .unit) && descriptor.namedLocal.isNone &&
              descriptor.ty.nonfixed == (descriptor.request != .register) do violation .v010 "invalid result pack component"
  let some entry := m.funcs[m.entry]? | violation .v001 "entry missing"
  unless entry.params.isEmpty && entry.results.isEmpty do violation .v001 "entry must have no source parameters or results"
  for global in m.globals do
    unless allTypesValid m global.ty && global.ty.storable do violation .v010 "invalid global type"
    unless global.init.params.isEmpty && global.init.results.length == 1 do violation .v001 "global initializer signature mismatch"
    let some result := global.init.results.head? | violation .v001 "global initializer has no result"
    unless result.ty == global.ty && result.namedLocal.isNone do violation .v010 "global initializer result differs from global"
  for descriptor in m.structs do
    unless !descriptor.displayName.isEmpty do violation .v010 "struct display name is empty"
    let mut occupied : List Nat := []
    for field in descriptor.fields do
      let some width := fixedByteSize? ⟨m.structs⟩ field.ty | violation .v010 "struct field is not flat fixed"
      unless field.byteOffset + width <= descriptor.byteSize do violation .v010 "struct field interval outside layout"
      let interval := (List.range width).map (field.byteOffset + ·)
      unless !(interval.any occupied.contains) do violation .v010 "struct field intervals overlap"
      occupied := occupied ++ interval
  let initializers := (List.range m.globals.size).map (m.funcs.size + ·)
  let all := { m with funcs := m.funcs ++ m.globals.map (·.init) }
  for f in all.funcs do checkTables all f
  for f in all.funcs do checkTypesAndEdges all f
  for f in all.funcs do checkDominance f
  checkUnreachable all
  for f in all.funcs do checkPermissions all f
  for f in all.funcs do checkScopes f
  let returns := resultRoots all
  for f in all.funcs do checkLifetimes all f returns
  let effects := deriveEffects all returns
  checkParameterRoots all returns
  checkStoredContents all returns
  checkSummaries all returns effects
  for (f,index) in all.funcs.toList.zipIdx do checkOwnership all index f returns effects
  for (f,index) in all.funcs.toList.zipIdx do checkChannelOwners all index f
  for f in all.funcs do checkKnownCounts all f
  for f in all.funcs do checkRenderedSnapshots f
  for f in all.funcs do checkCopyOrigins all f
  checkTargets all effects initializers
  for f in all.funcs do checkCertificates all f
  for f in all.funcs do checkOrigins all f

end Validate
end Goose.Construct.GIR
