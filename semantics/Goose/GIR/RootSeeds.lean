import Goose.Core.Roots
import Goose.GIR.Typing

namespace Goose.GIR

open Goose.Core

def Func.slotRootSeeds (f : Func) : Array (List RootRef) :=
  f.slots.mapIdx fun slot _ =>
    (f.roots.slots.getD #[]).foldl (fun roots row =>
      if row.1 == slot then unionRoots roots row.2 else roots) []

def Func.valueRootSeeds (f : Func) : Array (List RootRef) :=
  (Array.replicate f.numValues ([] : List RootRef)).mapIdx fun value _ =>
    (f.roots.values.getD #[]).foldl (fun roots row =>
      if row.1 == value then unionRoots roots row.2 else roots) []

def Module.declaredResultRoots (m : Module) : Array (List RootRef) :=
  m.funcs.map fun f =>
    match f.results with
    | [type] => if f.roots.slots.isSome && type.isRefLike then f.roots.results[0]?.getD [] else []
    | _ => []

end Goose.GIR
