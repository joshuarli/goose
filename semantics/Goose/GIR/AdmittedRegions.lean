import Goose.GIR.Effects
import Goose.GIR.RootSeeds

namespace Goose.GIR

open Goose.Core

def Module.hasDeclaredRegions (m : Module) : Bool :=
  m.funcs.any (·.roots.slots.isSome) || m.globals.any (·.init.roots.slots.isSome)

def Func.admittedSlots (f : Func) (p : Prov) : Bool :=
  (f.roots.slots.getD #[]).toList.all fun (slot, ceiling) =>
    (f.slots[slot]?).any fun storage =>
      storage.ty.isRefLike && (rootsAt p.slots slot).all ceiling.contains

def Func.receiverContentCeiling (f : Func) (p : Prov) (root : RootRef) : List RootRef :=
  let roots := match root with
    | .local slot => rootsAt p.slots slot
    | .param parameter =>
        if (f.params[parameter]?).any Ty.isRefSlice then f.contentRoots parameter else []
    | .global global => [.global global]
  roots.flatMap f.expandParameterRoot

def Func.admittedCallReceiver (f : Func) (p : Prov) (value : ValueId)
    (mapped : List RootRef) : Bool :=
  (rootsAt p.vals value).all fun root =>
    mapped.all (f.receiverContentCeiling p root).contains

def Func.admittedInstruction (m : Module) (vt : Array (Option VTy))
    (f : Func) (p : Prov) : Inst → Bool
  | .term (.ret values _) =>
      values.zipIdx.all fun (value, index) =>
        !valRefLike vt value ||
          (rootsAt p.vals value).all (f.roots.results[index]?.getD []).contains
  | .eff (.store address value _) =>
      !valRefLike vt value || (rootsAt p.vals address).all fun
        | .param parameter =>
            !(f.params[parameter]?).any Ty.isRefSlice ||
              (f.roots.contents.find? (·.1 == parameter)).any fun (_, ceiling) =>
                let actual := (rootsAt p.vals value).flatMap f.expandParameterRoot
                let declared := ceiling.flatMap f.expandParameterRoot
                actual.all declared.contains
        | _ => true
  | .def _ (.call fn args _) =>
      match m.funcs[fn]? with
      | none => true
      | some callee => callee.roots.contents.toList.all fun (parameter, ceiling) =>
          !(callee.params[parameter]?).any Ty.isRefSlice ||
            let actual := argumentContents f p args[parameter]!
            let mapped := mapContentRoots f p args ceiling
            actual.all mapped.contains && mapped.all actual.contains &&
              f.admittedCallReceiver p args[parameter]! mapped
  | _ => true

def Func.checkAdmittedRegions (m : Module) (vt : Array (Option VTy))
    (f : Func) (p : Prov) : Except String Unit := do
  unless f.admittedSlots p do
    throw s!"{f.name} slot root info does not cover its reference-like storage"
  unless (f.blocks.toList.flatMap (·.insts)).all (f.admittedInstruction m vt p) do
    throw s!"{f.name} root info does not bound a stored, returned, or passed region"

theorem Func.checkAdmittedRegions_instruction {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ())
    {block : Block} (blockMember : block ∈ f.blocks.toList)
    {inst : Inst} (instMember : inst ∈ block.insts) :
    f.admittedInstruction m vt p inst = true := by
  have all : (f.blocks.toList.flatMap (·.insts)).all (f.admittedInstruction m vt p) = true := by
    cases slotCase : f.admittedSlots p <;>
      cases instCase : (f.blocks.toList.flatMap (·.insts)).all (f.admittedInstruction m vt p) <;>
      simp_all [Func.checkAdmittedRegions, bind, Except.bind, throw]
  exact (List.all_eq_true.mp all) inst (List.mem_flatMap.mpr ⟨block, blockMember, instMember⟩)

theorem Func.checkAdmittedRegions_slots {m : Module} {vt : Array (Option VTy)}
    {f : Func} {p : Prov} (checked : f.checkAdmittedRegions m vt p = .ok ()) :
    f.admittedSlots p = true := by
  cases slotCase : f.admittedSlots p <;>
    cases instCase : (f.blocks.toList.flatMap (·.insts)).all (f.admittedInstruction m vt p) <;>
    simp_all [Func.checkAdmittedRegions, bind, Except.bind, throw]

def Module.checkRegionGlobalTypes (m : Module) : Except String Unit := do
  for global in m.globals do
    unless global.ty.storable && !global.ty.isRefLike do
      throw s!"global {global.name} has a type no source module may have"

def Module.checkAdmittedRegions (m : Module) (types : Array (Array (Option VTy)))
    (results : Array (List RootRef)) (nRoots : Nat) : Except String Unit := do
  if !m.hasDeclaredRegions then return ()
  m.checkRegionGlobalTypes
  for (f, index) in m.funcs.toList.zipIdx do
    let vt := types[index]?.getD #[]
    f.checkAdmittedRegions m vt (f.provenance results vt nRoots)
  for global in m.globals do
    let f := global.init
    let vt := f.valueTypes m
    f.checkAdmittedRegions m vt (f.provenance results vt nRoots)

end Goose.GIR
