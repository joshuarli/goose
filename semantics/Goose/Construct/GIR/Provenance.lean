import Goose.Construct.GIR.Typing

namespace Goose.Construct.GIR

inductive DestinationOwner
  | receiver (receiver : DestReceiver)
  | result (position : Nat)
  | target (target position : Nat)
  | child (parent : ValueId)
  | receiving (handle : ValueId)
  | reservation (ticket : ValueId)
  deriving DecidableEq, Repr

structure Provenance where
  values : Array (List DestinationOwner)
  packs : Array (List (List DestinationOwner))

private def mergeOwners (current added : List DestinationOwner) : List DestinationOwner :=
  (current ++ added).eraseDups

private def resultOwners (f : Func) (arguments : List (List DestinationOwner)) : List (List DestinationOwner) := Id.run do
  let mut destinations := arguments
  let mut outputs := []
  for descriptor in f.results do
    if descriptor.ty.nonfixed then
      outputs := outputs ++ [destinations.head?.getD []]
      destinations := destinations.tail
    else outputs := outputs ++ [[]]
  return outputs

def Func.provenance (m : Module) (functionId : FnId) (f : Func) : Provenance := Id.run do
  let mut values := Array.replicate f.numValues []
  let mut packs := Array.replicate f.numValues []
  if let some entry := f.blocks[0]? then
    let channels := f.results.zipIdx |>.filterMap fun (r,i) => if r.ty.nonfixed then some i else none
    for ((id,_),position) in (entry.params.drop f.params.length).zip channels do
      values := values.set! id [.result position]
  for _ in [0:f.numValues * (f.blocks.size + 1) + 1] do
    for block in f.blocks do
      for inst in block.insts do
        let get (id : ValueId) := values[id]?.getD []
        match inst with
        | .def id op =>
            let owners := match op with
              | .destOpen receiver .. => [.receiver receiver]
              | .destChild parent .. => [.child parent]
              | .destAdapt source _ _ _ | .destAdaptFinish source _ | .destFinish source _ | .destPrepareNamed source _ _ | .destAbandon source _ | .destValue source _ |
                  .destFit source _ | .destStage source _ | .destPublishRef source _ | .destArg source _ => get source
              | .destRelocate source _ _ => get source
              | .destNamed slot _ | .destAbandonNamed slot _ _ =>
                  f.results.zipIdx |>.filterMap fun (r,i) => if r.namedLocal == some slot then some (.result i) else none
              | .receivingOpen source => mergeOwners (get source) [.receiving id]
              | .targetReceiving target position _ => [.target target position,.receiving id]
              | .destRenew source => get source
              | .destRefresh source _ => get source
              | .exitReserve source _ _ => mergeOwners (get source) [.reservation id]
              | .exitWait source => mergeOwners (get source) [.reservation id]
              | .exitAdopt receiver built => mergeOwners (mergeOwners (get receiver) (get built)) [.reservation id]
              | .reservedDest ticket | .reservedNamed ticket _ => get ticket
              | .exitLand ticket built _ =>
                  let ticketOwners := get ticket
                  match ticketOwners.findSome? fun
                    | .result position =>
                        if ticketOwners.any (fun owner => match owner with
                          | .target target targetPosition => targetPosition == position &&
                              (m.targets[target]?).any (fun target => target.contains functionId)
                          | _ => false) then some position else none
                    | _ => none with
                  | some position => [.result position]
                  | none => mergeOwners (get built) ticketOwners
              | .receivingCancel source carried _ => mergeOwners (get source) (carried.flatMap get)
              | .result pack position => (packs[pack]?.getD [])[position]?.getD []
              | .callConstruct callee _ destinations _ =>
                  let outputs := (m.funcs[callee]?).map (fun f => resultOwners f (destinations.map get)) |>.getD []
                  if outputs.length == 1 then outputs.head?.getD [] else []
              | _ => []
            values := values.set! id (mergeOwners (get id) owners)
            if let .exitAdopt receiver built := op then
              let receivers := get receiver |>.filterMap fun
                | .receiving handle => some (.receiving handle)
                | _ => none
              values := values.set! built (mergeOwners (get built) (.reservation id :: receivers))
            match op with
            | .callConstruct callee _ destinations _ =>
                let outputs := (m.funcs[callee]?).map (fun f => resultOwners f (destinations.map get)) |>.getD []
                packs := packs.set! id outputs
            | _ => pure ()
        | .term term =>
            let edges : List (BlockId × List (List DestinationOwner) × List ValueId) := match term with
              | .br target args => [(target,[],args)]
              | .condbr _ left la right ra => [(left,[],la),(right,[],ra)]
              | .invoke callee _ destinations normal forwarded escapes _ =>
                  let leading := (m.funcs[callee]?).map (fun f => resultOwners f (destinations.map get)) |>.getD []
                  (normal,leading,forwarded) :: escapes.map (fun (edge : EscapeEdge) =>
                    let results := ((m.targets[edge.target]?).bind (fun t => m.funcs[t.first]?)).map (·.results) |>.getD []
                    let targetOwners := results.zipIdx |>.map fun (r,i) => if r.ty.nonfixed then [DestinationOwner.target edge.target i] else []
                    (edge.block,targetOwners ++ destinations.map get,edge.args))
              | _ => []
            for (target,leading,args) in edges do
              if let some block := f.blocks[target]? then
                for ((id,_),owners) in (block.params.take leading.length).zip leading do
                  values := values.set! id (mergeOwners (get id) owners)
                for ((id,_),arg) in (block.params.drop leading.length).zip args do
                  values := values.set! id (mergeOwners (get id) (get arg))
                  packs := packs.set! id (packs[arg]?.getD [])
        | _ => pure ()
  return ⟨values,packs⟩

end Goose.Construct.GIR
