import Goose.Core.Syntax
import Goose.Share.Rename
import Goose.Share.Equal

/-!
How a call resolves, and when two modules run the same program.

A call names a context; the context names an implementation; the
implementation's body runs. `Simulates m m' ρ` says that `m'` resolves every
call the way `m` does, except that the body of implementation `g` has its
callees renamed by `ρ g`, and that globals and entry agree. It is exactly what
`eval` reads of a module, so it is the hypothesis of the proof that results
agree.
-/

namespace Goose.Share

open Goose.Core

/-- The module with every context's declaration key and root annotations
removed. -/
def eraseRoots (m : Module) : Module :=
  { m with contexts := m.contexts.map fun c =>
      { impl := c.impl, decl := "", varRoots := [], resultRoots := [] } }

/-- The implementation that a call naming context `c` runs. A missing context
and a context naming a missing implementation both make the call unbound. -/
def resolve (m : Module) (c : ContextId) : Option Impl :=
  (m.contexts[c]?).bind fun ctx => m.impls[ctx.impl]?

/-- As `resolve`, with the index of the implementation. -/
def resolveIndexed (m : Module) (c : ContextId) : Option (ImplId × Impl) :=
  (m.contexts[c]?).bind fun ctx => (m.impls[ctx.impl]?).map fun i => (ctx.impl, i)

/-- Calling `c` in `m'` runs what calling `c'` runs in `m`, once the body of
each implementation `g` has its callees renamed by `ρ g`. -/
def Resolves (m m' : Module) (ρ : ImplId → CtxMap) (c' c : ContextId) : Prop :=
  resolve m' c' = (resolveIndexed m c).map fun gi => renImpl (ρ gi.1) gi.2

/-- `m'` runs `m`'s program: a context means the same in both (`ids`), a call
in a body renamed by `ρ g` means what it did before the renaming (`bodies`),
and globals and entry are the same. -/
structure Simulates (m m' : Module) (ρ : ImplId → CtxMap) : Prop where
  ids : ∀ c, Resolves m m' ρ c c
  bodies : ∀ g c, Resolves m m' ρ (ρ g c) c
  entry : m'.entry = m.entry
  globals : m'.globals = m.globals

/-- `m'` is the quotient of `m` by `q`, a map on implementation indices, where
the body of implementation `f` has its callees renamed by `ρ f`.

* The header tables, the entry, the globals and the contexts' indices are
  unchanged, including the artifact profile and struct descriptors; each
  context of `m'` is the context of `m` with its implementation index mapped
  by `q`. The root annotations are kept.
* Every implementation a context of `m` names is, in `m`, the body that `m'`
  holds at `q` of its index, with callees renamed by `ρ`. Two implementations
  that `q` identifies therefore have equal bodies once their callees are
  renamed. A renaming sends a context to one that `m'` maps to the same
  implementation (`callees`). Implementations no context names cannot be
  reached by a run, so nothing is demanded of them. -/
structure Quotient (m m' : Module) (q : ImplId → ImplId) (ρ : ImplId → CtxMap) : Prop where
  files : m'.files = m.files
  types : m'.types = m.types
  origins : m'.origins = m.origins
  profile : m'.profile = m.profile
  structs : m'.structs = m.structs
  entry : m'.entry = m.entry
  globals : m'.globals = m.globals
  contextCount : m'.contexts.size = m.contexts.size
  contexts : ∀ (c : ContextId) (ctx : Context), m.contexts[c]? = some ctx →
    m'.contexts[c]? = some { ctx with impl := q ctx.impl }
  impls : ∀ (c : ContextId) (ctx : Context), m.contexts[c]? = some ctx →
    m'.impls[q ctx.impl]? = (m.impls[ctx.impl]?).map (renImpl (ρ ctx.impl))
  callees : ∀ (f : ImplId) (c : ContextId),
    (m'.contexts[ρ f c]?).map Context.impl = (m'.contexts[c]?).map Context.impl

/-! ### The executable check -/

/-- Pairwise comparison of two lists of equal length. -/
def allZip {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && allZip f as bs
  | _, _ => false

def eqOptImpl : Option Impl → Option Impl → Bool
  | none, none => true
  | some a, some b => eqImpl a b
  | _, _ => false

/-- Header tables, profile, descriptors, entry and globals: unchanged. -/
def headerOk (m m' : Module) : Bool :=
  m'.files == m.files && m'.types == m.types && m'.origins == m.origins &&
  m'.profile == m.profile && m'.structs == m.structs &&
  m'.entry == m.entry && allZip eqGlobal m.globals.toList m'.globals.toList

/-- Contexts: those of `m` with their implementation index mapped by `q`. -/
def contextsOk (m m' : Module) (q : ImplId → ImplId) : Bool :=
  allZip (fun ctx ctx' => ctx' == { ctx with impl := q ctx.impl })
    m.contexts.toList m'.contexts.toList

/-- Whether the shared body at `q f` is the body of `f` as it stands. -/
def keepsBody (m m' : Module) (q : ImplId → ImplId) (f : ImplId) : Bool :=
  eqOptImpl (m'.impls[q f]?) (m.impls[f]?)

/-- The callee renaming of the body of `f`: none if the shared body is `f`'s as
it stands, otherwise the witness `rt`. -/
def bodyRenaming (m m' : Module) (q : ImplId → ImplId) (rt : Array ContextId)
    (f : ImplId) : CtxMap :=
  if keepsBody m m' q f then id else fun c => rt.getD c c

/-- Bodies: each implementation a context of `m` names reappears in `m'` at its
mapped index, as it stands or with callees renamed by `rt`. -/
def implsOk (m m' : Module) (q : ImplId → ImplId) (rt : Array ContextId) : Bool :=
  m.contexts.toList.all fun ctx =>
    keepsBody m m' q ctx.impl ||
      eqOptImpl (m'.impls[q ctx.impl]?)
        ((m.impls[ctx.impl]?).map (renImpl fun c => rt.getD c c))

/-- Callee map: a table over the contexts of `m`, sending each to a context
that `m'` maps to the same implementation. -/
def calleesOk (m m' : Module) (rt : Array ContextId) : Bool :=
  rt.size == m.contexts.size &&
  (List.range m.contexts.size).all fun c =>
    (m'.contexts[rt.getD c c]?).map Context.impl == (m'.contexts[c]?).map Context.impl

/-- Accepts exactly when `m'` is the quotient of `m` by the index map `qt`
(an index outside the table maps to itself) where each body is kept or has its
callees renamed by the context map `rt` (likewise). `qt` and `rt` are
untrusted witnesses: a wrong one makes the check fail, never succeed. -/
def checkQuotient (m m' : Module) (qt : Array ImplId) (rt : Array ContextId) : Bool :=
  headerOk m m' &&
  contextsOk m m' (fun f => qt.getD f f) &&
  implsOk m m' (fun f => qt.getD f f) rt &&
  calleesOk m m' rt

/-- Why `checkQuotient` rejects, as the first failing condition. Diagnostic
only: nothing relies on it. -/
def explainQuotient (m m' : Module) (qt : Array ImplId) (rt : Array ContextId) : String :=
  if !headerOk m m' then
    "the header tables, artifact profile, struct descriptors, globals or entry differ"
  else if !contextsOk m m' (fun f => qt.getD f f) then
    "a context of the shared module is not the unshared context with its implementation mapped"
  else if !calleesOk m m' rt then
    "a callee is renamed to a context that runs a different implementation"
  else if !implsOk m m' (fun f => qt.getD f f) rt then
    "a shared implementation is not equal to the unshared implementation, kept or with its callees renamed"
  else "accepted"

end Goose.Share
