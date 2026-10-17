import Goose.Construct.GIR.Typing



namespace Goose.Construct.GIR

open Goose.Core (IntTy)

abbrev Facts := List Fact

def Fact.mentions (value : ValueId) : Fact → Bool
  | .ge0 i => i == value
  | .lt i n | .viewLenGe i n => i == value || n == value
  | .lenGe reference n => reference == value || n == value

def addFact (facts : Facts) (fact : Fact) : Facts :=
  if fact ∈ facts then facts else facts ++ [fact]

def killValue (facts : Facts) (value : ValueId) : Facts :=
  facts.filter fun fact => !fact.mentions value

def killLengths (facts : Facts) : Facts :=
  facts.filter fun
    | .lenGe .. => false
    | _ => true

def findDefIn (value : ValueId) : List Inst → Option Op
  | [] => none
  | .def result op :: rest => if result == value then some op else findDefIn value rest
  | _ :: rest => findDefIn value rest

def Func.defOp? (f : Func) (value : ValueId) : Option Op :=
  let rec blocks : List Block → Option Op
    | [] => none
    | block :: rest => (findDefIn value block.insts).orElse fun _ => blocks rest
  blocks f.blocks.toList

def isArrayOwner : Ty → Bool
  | .arr .. | .varr .. | .grow .. | .growshrink .. | .limited .. => true
  | _ => false

def isI64At (vt : Array (Option VTy)) (value : ValueId) : Bool :=
  vt[value]? == some (some (.data (.int .i64)))

def Fact.wellTyped (_m : Module) (_f : Func) (vt : Array (Option VTy)) : Fact → Bool
  | .ge0 i => isI64At vt i
  | .lt i n => isI64At vt i && isI64At vt n
  | .lenGe reference n =>
    isI64At vt n && match vt[reference]? with
      | some (some (.data (.ref _ owner))) => isArrayOwner owner
      | _ => false
  | .viewLenGe v n =>
    isI64At vt n && match vt[v]? with
      | some (some (.view ..)) => true
      | _ => false

def provesIndex (facts : Facts) (view index : ValueId) : Bool :=
  (.ge0 index) ∈ facts && facts.any fun
    | .viewLenGe v n => v == view && (.lt index n) ∈ facts
    | _ => false

def killsLengths : Inst → Bool
  | .def _ (.call ..) | .def _ (.callConstruct ..) | .def _ (.push ..) | .def _ (.pop ..) | .term (.invoke ..) => true
  | .eff (.slotInit ..) | .eff (.store ..) | .eff (.append ..) | .eff (.popN ..) | .eff (.resize ..)
  | .eff (.clear ..) | .eff (.replace ..) | .eff (.enter ..) | .eff (.leave ..) => true
  | .eff (.appendValue ..) | .eff (.destPublish ..) | .eff (.destBind ..) | .eff (.destWrite ..) | .eff (.destCopy ..) => true
  | _ => false

def transferInst (_m : Module) (_f : Func) (facts : Facts) (inst : Inst) : Except String Facts := do
  match inst with
  | .def _ (.indexProven view index) =>
    unless provesIndex facts view index do throw "a proven index is not justified by its entry facts"
  | _ => pure ()
  let facts := match inst with
    | .def result _ => killValue facts result
    | _ => facts
  let facts := if killsLengths inst then killLengths facts else facts
  match inst with
  | .def result (.constInt .i64 n) =>
    pure (if 0 ≤ n then addFact facts (.ge0 result) else facts)
  | .def result (.arrayLen reference) =>
    pure (addFact (addFact facts (.lenGe reference result)) (.ge0 result))
  | .def result (.snapshot _ reference) =>
    pure (facts.foldl (fun acc fact => match fact with
      | .lenGe found bound => if found == reference then addFact acc (.viewLenGe result bound) else acc
      | _ => acc) facts)
  | _ => pure facts

def transferBlock (m : Module) (f : Func) (facts : Facts) (block : Block) : Except String Facts :=
  block.insts.foldlM (transferInst m f) facts

def translateEdge (f : Func) (facts : Facts) (target : BlockId) (_args : List ValueId) : Facts :=
  match f.blocks[target]? with
  | none => []
  | some block =>
    let params := block.params.map (·.1)
    facts.filter fun fact => !(params.any fact.mentions)

def addTrueEdgeFacts (f : Func) (facts : Facts) (condition : ValueId) : Facts :=
  match f.defOp? condition with
  | some (.cmp .lt .i64 i n) => addFact facts (.lt i n)
  | _ => facts

def edgeFacts (f : Func) (facts : Facts) (condition : Option ValueId)
    (target : BlockId) (args : List ValueId) : Facts :=
  translateEdge f (match condition with
    | some value => addTrueEdgeFacts f facts value
    | none => facts) target args

def hasProvenIndex (f : Func) : Bool :=
  f.blocks.any fun block => block.insts.any fun
    | .def _ (.indexProven ..) => true
    | _ => false

def checkSubset (claimed derived : Facts) : Except String Unit :=
  if claimed.all (· ∈ derived) then pure () else throw "a block fact is not implied by a predecessor"

def checkEvery (xs : List α) (check : α → Except String Unit) : Except String Unit :=
  match xs with
  | [] => pure ()
  | x :: rest => do
    check x
    checkEvery rest check

def checkFactSet (m : Module) (f : Func) (vt : Array (Option VTy))
    (facts : Facts) : Except String Unit := do
  unless facts.Nodup do throw "a block fact set contains a duplicate"
  unless facts.all (Fact.wellTyped m f vt) do throw "a block fact set contains an ill-typed fact"

def checkBlockEvidence (m : Module) (f : Func) (certificate : FactCertificate)
    (blockId : BlockId) : Except String Unit := do
  let some block := f.blocks[blockId]?
    | throw "the fact certificate names a block outside the function"
  let facts ← transferBlock m f (certificate[blockId]?.getD []) block
  match block.lastTerm? with
  | some (.br target args) =>
    let claimed := certificate[target]?.getD []
    checkSubset claimed (edgeFacts f facts none target args)
  | some (.condbr condition yes yesArgs no noArgs) =>
    checkSubset (certificate[yes]?.getD []) (edgeFacts f facts (some condition) yes yesArgs)
    checkSubset (certificate[no]?.getD []) (edgeFacts f facts none no noArgs)
  | some (.invoke _ _ _ normal forwarded escapes _) =>
    checkSubset (certificate[normal]?.getD []) (edgeFacts f facts none normal forwarded)
    for edge in escapes do
      checkSubset (certificate[edge.block]?.getD []) (edgeFacts f facts none edge.block edge.args)
  | _ => pure ()

def checkEvidence (m : Module) (f : Func) (vt : Array (Option VTy)) : Except String Unit := do
  let some certificate := f.certificate
    | if hasProvenIndex f then throw "a proven index has no fact certificate" else pure ()
  unless certificate.size == f.blocks.size do throw "the fact certificate does not have one set per block"
  unless certificate[0]?.getD [] == [] do throw "the entry block asserts facts"
  checkEvery certificate.toList (checkFactSet m f vt)
  checkEvery (List.range f.blocks.size) (checkBlockEvidence m f certificate)

end Goose.Construct.GIR
