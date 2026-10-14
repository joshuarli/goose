import Goose.Construct.GIR.Typing

namespace Goose.Construct.GIR

inductive DestinationOwner
  | receiver (receiver : DestReceiver)
  | result (position : Nat)
  | target (target position : Nat)
  | child (parent : ValueId)
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
              | .destAdapt source _ _ _ | .destAdaptFinish source _ | .destFinish source _ | .destAbandon source _ | .destValue source _ |
                  .destFit source _ | .destStage source _ | .destPublishRef source _ | .destArg source _ => get source
              | .destRelocate source reason _ =>
                  (get source).map fun owner => match owner with
                    | .target target position =>
                        if reason == .exitValue && (m.targets[target]?).any (fun t => t.contains functionId) then .result position else owner
                    | _ => owner
              | .destNamed slot _ | .destAbandonNamed slot _ _ =>
                  f.results.zipIdx |>.filterMap fun (r,i) => if r.namedLocal == some slot then some (.result i) else none
              | .resultExitDest position _ => [.result position]
              | .targetDest target position _ => [.target target position]
              | .result pack position => (packs[pack]?.getD [])[position]?.getD []
              | .callConstruct callee _ destinations _ =>
                  let outputs := (m.funcs[callee]?).map (fun f => resultOwners f (destinations.map get)) |>.getD []
                  if outputs.length == 1 then outputs.head?.getD [] else []
              | _ => []
            values := values.set! id (mergeOwners (get id) owners)
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
