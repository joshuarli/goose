import Goose.Core.Demand

namespace Goose.Lower.Validation

open Goose.Core

structure ReplacementDemandLocation (root node : DemandNode) where
  path : List Nat
  source : DemandNodeAt root path node

def ReplacementDemandLocation.here (node : DemandNode) : ReplacementDemandLocation node node :=
  ⟨[], .here node⟩

def ReplacementDemandLocation.child {root parent : DemandNode}
    (location : ReplacementDemandLocation root parent) (index : Nat) (child : DemandNode)
    (row : parent.child? index = some child) : ReplacementDemandLocation root child :=
  ⟨location.path ++ [index], location.source.snoc index row⟩

def ReplacementDemandLocations (root : DemandNode) (project : α → DemandNode) (items : List α) : Type :=
  ∀ (index : Nat) (item : α), items[index]? = some item → ReplacementDemandLocation root (project item)

def ReplacementDemandLocations.head {root : DemandNode} {project : α → DemandNode} {head : α} {tail : List α}
    (locations : ReplacementDemandLocations root project (head :: tail)) : ReplacementDemandLocation root (project head) :=
  locations 0 head rfl

def ReplacementDemandLocations.tail {root : DemandNode} {project : α → DemandNode} {head : α} {tail : List α}
    (locations : ReplacementDemandLocations root project (head :: tail)) : ReplacementDemandLocations root project tail :=
  fun index item row => locations (index + 1) item (by simpa using row)

def ReplacementDemandLocation.expressionChildren {root parent : DemandNode}
    (location : ReplacementDemandLocation root parent) (items : List Expr)
    (children : parent.children = items.map (some ∘ DemandNode.expression)) :
    ReplacementDemandLocations root DemandNode.expression items := by
  intro index item row
  exact location.child index _ (by simp [DemandNode.child?, children, List.getElem?_map, row])

def replacementDemandArgumentNode : Arg → DemandNode
  | .byVal expression => .expression expression
  | .byRef _ place => .place place

def ReplacementDemandLocation.arguments {root : DemandNode} {context : ContextId} {args : List Arg}
    {origin : OriginId}
    (location : ReplacementDemandLocation root (.expression (.call context args origin))) :
    ReplacementDemandLocations root replacementDemandArgumentNode args := by
  intro index arg row
  cases arg <;> exact location.child index _ (by simp [DemandNode.child?, DemandNode.children, replacementDemandArgumentNode, List.getElem?_map, row])

def ReplacementDemandPrintLocations (root : DemandNode) (args : List PrintArg) : Type :=
  ∀ (index : Nat) (expression : Expr), args[index]? = some (.expr expression) → ReplacementDemandLocation root (.expression expression)

def ReplacementDemandPrintLocations.tail {root : DemandNode} {head : PrintArg} {tail : List PrintArg}
    (locations : ReplacementDemandPrintLocations root (head :: tail)) : ReplacementDemandPrintLocations root tail :=
  fun index expression row => locations (index + 1) expression (by simpa using row)

def ReplacementDemandLocation.printArguments {root : DemandNode} {args : List PrintArg} {origin : OriginId}
    (location : ReplacementDemandLocation root (.statement (.print args origin))) :
    ReplacementDemandPrintLocations root args := by
  intro index expression row
  exact location.child index _ (by simp [DemandNode.child?, DemandNode.children, replacementDemandArgumentNode, List.getElem?_map, row])

def ReplacementDemandLocation.statements {root : DemandNode} {scope : Nat}
    {statements : List Stmt} {value : Option Expr}
    (location : ReplacementDemandLocation root (.block (.mk scope statements value))) :
    ReplacementDemandLocations root DemandNode.statement statements := by
  intro index statement row
  have bound := (List.getElem?_eq_some_iff.mp row).1
  exact location.child index _ (by
    simp only [DemandNode.child?, DemandNode.children]
    rw [List.getElem?_append_left (by simpa using bound)]
    simp [List.getElem?_map, row])

def ReplacementDemandLocation.blockValue {root : DemandNode} {scope : Nat}
    {statements : List Stmt} {value : Expr}
    (location : ReplacementDemandLocation root (.block (.mk scope statements (some value)))) :
    ReplacementDemandLocation root (.expression value) :=
  location.child statements.length _ (by simp [DemandNode.child?, DemandNode.children, List.getElem?_append])

end Goose.Lower.Validation
