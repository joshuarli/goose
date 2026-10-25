import Goose.GIR.ReplacementContentFlowProofsCanonicalDefinitions
import Goose.GIR.ReplacementContentFlowProofsCanonicalCallTransfer
import Goose.GIR.ReplacementContentFlowProofsCanonicalEdges

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

structure FunctionRootFacts (func : Func) : Prop where
  unique : (func.roots.contents.toList.map Prod.fst).Nodup
  closed : ∀ index root, root ∈ func.parameterRoots index →
    root = .param index ∨ ∃ global, root = .global global
  parameters : ∀ type ∈ func.params, type.paramOk = true
  contentExternal : ∀ index slot, RootRef.local slot ∉ func.contentRoots index
  resultExternal : ∀ slot, RootRef.local slot ∉ func.roots.results[0]?.getD []
  contentTypes : ∀ index ceiling, func.roots.contents.find? (·.1 == index) = some (index,ceiling) →
    (func.params[index]?).any Ty.isRefSlice = true
  resultNotHolder : ∀ type ∈ func.results, ∀ mutability payload,
    type = .ref mutability payload → payload.isRefLike = false

structure CallSiteFacts (module : Module) (func : Func) (vt : Array (Option VTy))
    (provenance : Prov) (fn : FnId) (args : List ValueId) where
  callee : Func
  calleeAt : module.funcs[fn]? = some callee
  contracts : ∀ index, RootsRefine func (mapRawContentRoots provenance args [.param index])
    (mapRawContentRoots provenance args (callee.parameterRoots index))
  arguments : ∀ index, index < callee.params.length →
    ∃ argument, args[index]? = some argument ∧ argument < func.numValues
  references : ∀ (index : Nat) (outer : Mutability) (payload : Ty),
    callee.params[index]? = some (.ref outer payload) →
    ∃ argument actualMutability, args[index]? = some argument ∧
      vt[argument]? = some (some (.data (.ref actualMutability payload))) ∧ argument < func.numValues
  observed : ∀ (index : Nat) (argument : ValueId), args[index]? = some argument →
    (callee.params[index]?).any Ty.isRefSlice = true →
    (callee.roots.contents.find? (·.1 == index)).isSome = true →
    ∀ receiver, RootRef.param receiver ∈ rootsAt provenance.vals argument →
      (func.params[receiver]?).any Ty.isRefSlice = true →
      (func.roots.contents.find? (·.1 == receiver)).isSome = true

inductive InstructionTyping (module : Module) (func : Func) (vt : Array (Option VTy)) : Inst → Prop
  | definition (value : ValueId) (op : Op) (type : VTy)
      (typed : op.resultTy {module.tyEnv func with vals := vt} = .ok type)
      (canonical : vt[value]? = some (some type)) : InstructionTyping module func vt (.def value op)
  | slotInit (slot : SlotId) (value : ValueId) (origin : Option OriginId) (storage : Slot)
      (row : func.slots[slot]? = some storage) (canonical : vt[value]? = some (some (.data storage.ty))) :
      InstructionTyping module func vt (.eff (.slotInit slot value origin))
  | store (address value : ValueId) (origin : Option OriginId) (mutability : Mutability) (payload : Ty)
      (addressType : vt[address]? = some (some (.data (.ref mutability payload))))
      (valueType : vt[value]? = some (some (.data payload))) :
      InstructionTyping module func vt (.eff (.store address value origin))
  | branch (target : BlockId) (args : List ValueId) (block : Block)
      (targetAt : func.blocks[target]? = some block)
      (types : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
        vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
      (bounds : ∀ parameter ∈ block.params, parameter.1 < func.numValues) :
      InstructionTyping module func vt (.term (.br target args))
  | conditional (condition : ValueId) (thenTarget elseTarget : BlockId) (thenArgs elseArgs : List ValueId)
      (thenBlock elseBlock : Block) (thenAt : func.blocks[thenTarget]? = some thenBlock)
      (elseAt : func.blocks[elseTarget]? = some elseBlock)
      (thenTypes : ∀ parameter argument, (parameter,argument) ∈ thenBlock.params.zip thenArgs →
        vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
      (elseTypes : ∀ parameter argument, (parameter,argument) ∈ elseBlock.params.zip elseArgs →
        vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
      (thenBounds : ∀ parameter ∈ thenBlock.params, parameter.1 < func.numValues)
      (elseBounds : ∀ parameter ∈ elseBlock.params, parameter.1 < func.numValues) :
      InstructionTyping module func vt (.term (.condbr condition thenTarget thenArgs elseTarget elseArgs))
  | returned (value : ValueId) (origin : Option OriginId) (type : Ty)
      (result : func.results = [type]) (canonical : vt[value]? = some (some (.data type))) :
      InstructionTyping module func vt (.term (.ret [value] origin))
  | effect (effect : Effect) (ordinary : ∀ slot value origin, effect ≠ .slotInit slot value origin)
      (nonstore : ∀ address value origin, effect ≠ .store address value origin) :
      InstructionTyping module func vt (.eff effect)
  | terminal (term : Term) (nonbranch : ∀ target args, term ≠ .br target args)
      (nonconditional : ∀ condition thenTarget thenArgs elseTarget elseArgs,
        term ≠ .condbr condition thenTarget thenArgs elseTarget elseArgs)
      (nonreturned : ∀ value origin, term ≠ .ret [value] origin) :
      InstructionTyping module func vt (.term term)

structure FunctionCanonicalFacts (module : Module) (func : Func) (vt : Array (Option VTy))
    (provenance : Prov) (results : Array (List RootRef)) : Prop where
  roots : FunctionRootFacts func
  valuesShape : ValueTypeShapes vt
  globalStorage : ∀ (index : Nat) (type : Ty) (kind : VarKind),
    (module.tyEnv func).globals[index]? = some (type,kind) → type.isRefLike = false
  fields : ∀ (index : Nat) (descriptor : StructDef), (module.tyEnv func).structs[index]? = some descriptor →
    ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true
  valuesSize : provenance.vals.size = func.numValues
  slotsSize : provenance.slots.size = func.slots.size
  parameters : ∀ entry : Block, func.blocks[0]? = some entry →
    ∀ pair index, (pair,index) ∈ entry.params.zipIdx →
      ∃ type, pair.2 = .data type ∧ vt[pair.1]? = some (some (.data type)) ∧
        func.params[index]? = some type
  seeds : ∀ entry : Block, func.blocks[0]? = some entry →
    ∀ pair index, (pair,index) ∈ entry.params.zipIdx → valRefLike vt pair.1 = true →
      RootRef.param index ∈ rootsAt provenance.vals pair.1
  typing : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, InstructionTyping module func vt inst
  uses : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, ∀ value ∈ inst.uses, value < func.numValues
  definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts → value < func.numValues
  quiet : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
    func.provStep results vt (provenance,false) inst = (provenance,false)
  admitted : func.checkAdmittedRegions module vt provenance = .ok ()
  loadObserved : ∀ block ∈ func.blocks.toList, ∀ value source, Inst.def value (.load source) ∈ block.insts →
    valRefLike vt value = true → ∀ index, RootRef.param index ∈ rootsAt provenance.vals source →
      (func.params[index]?).any Ty.isRefSlice = true →
      (func.roots.contents.find? (·.1 == index)).isSome = true
  calls : ∀ block ∈ func.blocks.toList, ∀ value fn args origin, Inst.def value (.call fn args origin) ∈ block.insts →
    Nonempty (CallSiteFacts module func vt provenance fn args)
  callResults : ∀ block ∈ func.blocks.toList, ∀ value fn args origin,
    Inst.def value (.call fn args origin) ∈ block.insts → ∀ callee, module.funcs[fn]? = some callee →
      (callee.results = [] ∧ vt[value]? = some (some (.data .unit))) ∨
        ∃ type, callee.results = [type] ∧ vt[value]? = some (some (.data type))

structure ModuleCanonicalFacts (module : Module) (types : Array (Array (Option VTy)))
    (provenances : Array Prov) (results : Array (List RootRef)) : Prop where
  functions : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func →
    FunctionCanonicalFacts module func (types[index]?.getD #[])
      (provenances[index]?.getD ⟨#[],#[]⟩) results
  resultFloors : ∀ (index : Nat) (func : Func), module.funcs[index]? = some func →
    (func.results[0]?).any Ty.isRefLike = true →
    func.roots.results[0]?.getD [] ⊆ rootsAt results index

def ModuleCanonicalWithin (module : Module) (types : Array (Array (Option VTy)))
    (provenances : Array Prov) (states : Array State) : Prop :=
  states.size = module.funcs.size ∧ ∀ (index : Nat) (func : Func), module.funcs[index]? = some func →
    ∃ state : State, states[index]? = some state ∧
      state.CanonicalWithin func (types[index]?.getD #[]) (provenances[index]?.getD ⟨#[],#[]⟩)

end Goose.GIR.ReplacementContentFlow.Model
