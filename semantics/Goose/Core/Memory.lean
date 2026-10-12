import Std.Data.HashMap
import Goose.Core.Syntax

/-!
The memory model: root instances, locations, values and the store.

A root instance is a variable's storage for one activation and one entry of
its scope, so two calls of one function, or two iterations of one loop, never
share a root. A location is a root and a path of element selectors into the
object stored there. Every access is partial: a root that is absent (its scope
ended) or a path that leaves the object is reported as a fault kind, which is
what the safety theorem shows validated programs never meet.
-/

namespace Goose.Core

abbrev ActId := Nat
abbrev ScopeInst := Nat

inductive RootInst
  | global (g : GlobalId)
  | local (act : ActId) (scope : ScopeInst) (x : VarId)
  deriving DecidableEq, Repr

/-- Plain arithmetic on the ids rather than the runtime's opaque hash mixer, so
that nothing `eval` depends on is opaque. -/
instance : Hashable RootInst where
  hash
    | .global g => UInt64.ofNat (g + 2 ^ 40)
    | .local act sc x => UInt64.ofNat ((act * 1000003 + sc) * 1000033 + x)

instance : LawfulHashable RootInst where
  hash_eq a b h := by
    have := eq_of_beq h
    subst this
    rfl

structure Loc where
  root : RootInst
  path : List Nat
  deriving DecidableEq, Repr

/-- Runtime values and the objects the store holds are one type: an object is
the value its root was last given. `fixed` and `resizable` hold elements;
`ref` and `slice` occur only as the whole value of a variable, a parameter, a
result or an operand, never as an element. -/
inductive Val
  | int (t : IntTy) (n : Int)
  | bool (b : Bool)
  | unit
  | fixed (elems : Array Val)
  /-- The element type is part of the value, so growing an empty array cannot
  change which array type it has. -/
  | resizable (elem : Ty) (elems : Array Val)
  | ref (l : Loc)
  /-- A run of `len` elements starting at element `start` of the array at `l`. -/
  | slice (l : Loc) (start len : Nat)
  deriving Repr, Inhabited

/-- Why an access or an operation is meaningless. Each kind is raised by one
family of helpers in the evaluator (see `Goose.Core.Eval`). -/
inductive FaultKind
  | danglingRoot
  | pathRange
  | shape
  | unbound
  | arity
  | flow
  deriving DecidableEq, Repr

def FaultKind.tag : FaultKind → String
  | .danglingRoot => "dangling_root"
  | .pathRange => "path_range"
  | .shape => "shape"
  | .unbound => "unbound"
  | .arity => "arity"
  | .flow => "flow"

/-- The elements of an array object. -/
def Val.elems? : Val → Option (Array Val)
  | .fixed es => some es
  | .resizable _ es => some es
  | _ => none

/-- The value at `path` inside a value. -/
def Val.get? : Val → List Nat → Option Val
  | v, [] => some v
  | v, i :: rest =>
    match v.elems? with
    | none => none
    | some es =>
      match es[i]? with
      | none => none
      | some e => e.get? rest

/-- Rebuild a value with the sub-value at `path` replaced by `f` of it. -/
def Val.modifyAt? : Val → List Nat → (Val → Option Val) → Option Val
  | v, [], f => f v
  | .fixed es, i :: rest, f =>
    if h : i < es.size then
      match es[i].modifyAt? rest f with
      | some e => some (.fixed (es.set i e))
      | none => none
    else none
  | .resizable E es, i :: rest, f =>
    if h : i < es.size then
      match es[i].modifyAt? rest f with
      | some e => some (.resizable E (es.set i e))
      | none => none
    else none
  | _, _ :: _, _ => none

/-- The store: the object of every live root instance. Never iterated, so the
hash map's order is unobservable. -/
structure Store where
  roots : Std.HashMap RootInst Val

def Store.empty : Store := ⟨{}⟩

def Store.read (s : Store) (l : Loc) : Except FaultKind Val :=
  match s.roots[l.root]? with
  | none => .error .danglingRoot
  | some v =>
    match v.get? l.path with
    | none => .error .pathRange
    | some x => .ok x

/-- Replace the sub-value at an existing location by `f` of it; `f` refusing
is a wrong-shape fault. The old object is released before it is rebuilt so an
unshared array is updated in place. -/
def Store.modify (s : Store) (l : Loc) (f : Val → Option Val) : Except FaultKind Store :=
  match s.roots[l.root]? with
  | none => .error .danglingRoot
  | some old =>
    match old.get? l.path with
    | none => .error .pathRange
    | some _ =>
      let roots := s.roots.erase l.root
      match old.modifyAt? l.path f with
      | some new => .ok ⟨roots.insert l.root new⟩
      | none => .error .shape

def Store.write (s : Store) (l : Loc) (v : Val) : Except FaultKind Store :=
  s.modify l (fun _ => some v)

/-- Append elements to a resizable array value. -/
def Val.appendAll (vs : Array Val) : Val → Option Val
  | .resizable E es => some (.resizable E (es ++ vs))
  | _ => none

/-- The length of the resizable array at `l`. -/
def Store.length (s : Store) (l : Loc) : Except FaultKind Nat :=
  match s.read l with
  | .error k => .error k
  | .ok (.resizable _ es) => .ok es.size
  | .ok _ => .error .shape

/-- Append elements to the resizable array at `l`; yields the index of the first. -/
def Store.append (s : Store) (l : Loc) (vs : Array Val) : Except FaultKind (Store × Nat) :=
  match s.length l with
  | .error k => .error k
  | .ok n =>
    match s.modify l (Val.appendAll vs) with
    | .ok s' => .ok (s', n)
    | .error k => .error k

/-- Bind a root to an object, replacing any earlier binding. -/
def Store.introduce (s : Store) (r : RootInst) (v : Val) : Store :=
  ⟨s.roots.insert r v⟩

/-- Remove a root. Absent roots are left absent. -/
def Store.release (s : Store) (r : RootInst) : Store :=
  ⟨s.roots.erase r⟩

end Goose.Core
