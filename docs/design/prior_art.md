# Prior art: the nearest memory models, and what is new

<details>
<summary>Table of contents</summary>

- [1. What is being compared](#1-what-is-being-compared)
- [2. The closest matches, ranked](#2-the-closest-matches-ranked)
- [3. Multiple stacks put to other uses](#3-multiple-stacks-put-to-other-uses)
- [4. Relatives of the lifetime rule](#4-relatives-of-the-lifetime-rule)
- [5. What no precedent was found for](#5-what-no-precedent-was-found-for)
- [6. How the survey was done](#6-how-the-survey-was-done)

</details>

A survey, made in October 2026, of the languages, libraries and papers whose
memory management comes closest to Goose's: all dynamic data on a
compiler-counted set of stacks, with one growable value on top of each. No
language or paper was found that combines Goose's ingredients. Each
ingredient has prior art, and this note ranks it by how much of the model it
shares, says precisely where each candidate differs, and lists what remains
without precedent. Scores are out of ten and are a judgement, not a
measurement.

## 1. What is being compared

Goose's model, in the parts that a candidate can share or lack:

1. **Stacks, not a heap.** A program's dynamic data lives on N data stacks,
   each a large address-space reservation committed on touch, with a bump
   pointer and a guard gap; values are pushed in lifetime order and popped
   en masse at scope exit ([spec §1.2](../goose_spec.md#12-memory-model),
   [§10.4](../goose_spec.md#104-runtime-environment)).
2. **One growable value per stack, on top.** At most one resizable value is
   live per stack and it is always the topmost, so growth is a pointer bump,
   nothing moves, and interior references stay valid across growth
   ([§1.3](../goose_spec.md#13-the-stack-invariant)).
3. **N is a compile-time constant.** The whole-program compiler assigns each
   growable local a stack index: simultaneously live values get distinct
   stacks, sequentially live ones reuse one, like register allocation over
   stacks ([§10.3](../goose_spec.md#103-stack-assignment-deterministic-recipe)).
4. **Static, annotation-free safety.** Every reference has a compile-time
   root, the variable that bounds its target's lifetime; a reference may not
   outlive its root, a store is checked by scope nesting, and functions are
   specialized per root in place of lifetime parameters
   ([§9.1](../goose_spec.md#91-the-one-rule),
   [§9.2](../goose_spec.md#92-roots-and-the-depth-check),
   [§10.2](../goose_spec.md#102-monomorphization)). An array shrinks only
   where the compiler sees that nothing refers into it
   ([§5](../goose_spec.md#5-the-resizableshrink-rules)).
5. **Results built at their destination.** A variable-size result is
   constructed on the stack of the value that receives it, through any depth
   of calls, the callee knowing the destination stack
   ([§4.3](../goose_spec.md#43-the-in-place-construction-guarantee),
   [§7.3](../goose_spec.md#73-return-values-and-result-placement)).
6. **Nested data inline.** An array of strings is one contiguous block, and a
   struct may end in one growable tail
   ([§3.3](../goose_spec.md#33-the-array-family),
   [§3.4](../goose_spec.md#34-placement-rules-what-may-contain-what)).
7. **Recursion keeps N constant.** No growable local may be in scope across
   a call into a recursive cycle, so recursion costs native stack only
   ([§7.8](../goose_spec.md#78-recursion)).

The question for each candidate is the same: is its region a contiguous
stack whose top value grows in place with stable interior references, or an
arena of separately allocated objects; is the number of regions a
compile-time constant or one per activation; and is safety static, and at
what annotation cost.

## 2. The closest matches, ranked

| Rank | Candidate | Shares | Lacks | Score |
|---|---|---|---|---|
| 1 | ML Kit region inference | 1, 4, 5, the shrink rule's ancestor | 2, 3, 6, 7 | 6 |
| 2 | GNU obstacks | 2, 5 as convention | 3, 4, 6, 7; growing object may move | 6 |
| 3 | ParaSail | 1 in spirit, 5, no-pointer safety | 2, 3, 6, 7; regions are local heaps | 6 |
| 4 | Ada and GNAT without allocators | 1 with two stacks, 4's depth check, 5 | 2, 3, 6, 7; nothing grows | 5 |
| 5 | Arena idioms in C | 1, 2, 5 as convention | 3 by hand, 4, 6, 7 | 5 |
| 6 | Xhebraj et al., ECOOP 2022 | 5 on a single stack, static modes | 2, 3, 6, 7 | 5 |
| 7 | Cyclone LIFO arenas | 1 in part, 5 | 2, 3, 6, 7; annotated | 5 |
| 8 | OxCaml stack allocation | a second data stack, static escape check | 2, 3, 5 beyond one level, 6, 7 | 5 |
| 9 | Ruggieri and Murtagh, 1988 | 4's placement by enclosing scope | everything else | 4 |
| 10 | Automatic pool allocation | 3's static set of areas | 2, 4, 5, 6, 7 | 4 |
| 11 | Fels | 4's depth check by zone | 2, 3, 5, 6, 7 | 4 |
| 12 | RTSJ scoped memory and its static typings | 1's LIFO areas, 4's store rule | 2, 3, 5, 6, 7 | 3 |

### 2.1 Tofte and Talpin's region inference, and the ML Kit

The closest match on the static side. In the region calculus the store "consisted
of a stack of regions"; `letregion` is the only way to make or drop a region,
"hence regions were allocated and de-allocated in a stack-like manner"
([Tofte, Birkedal, Elsman, Hallenberg, "A retrospective on region-based
memory management", HOSC 2004](https://elsman.com/mlkit/pdf/retro.pdf);
[Tofte and Talpin, POPL 1994](https://dl.acm.org/doi/10.1145/174675.177855)).
Region inference is fully automatic, with no annotations; a region-polymorphic
function takes the regions for its results as parameters, so a callee allocates
into storage the caller chose, which is point 5 by a runtime handle. Region
representation inference ([Birkedal, Tofte, Vejlstrup, POPL
1996](https://www.cs.tufts.edu/~nr/cs257/archive/mads-tofte/knormal-final.pdf))
places "finite" regions, those holding one value, in the activation record, and
the storage mode analysis of the [ML Kit
manual](https://elsman.com/mlkit/pdf/mlkit-4.3.0.pdf) resets a region in place
(`atbot`) where the compiler proves it holds nothing live at that allocation,
with `resetRegions` as the checked programmer-visible form: the ancestor of
Goose's shrink rule, applied to a whole region.

What differs: an "infinite" region "consisted of a linked list of fixed-size
region pages, allocated from a free-list of region pages", holding many boxed,
fixed-size values, so nothing is contiguous and nothing grows in place. The
number of live regions is dynamic, one per `letregion` evaluation and so per
recursion level. Region parameters are passed at run time rather than
specialized. The retrospective judges infinite regions to "give fragmentation
problems" and the storage mode analysis "complicated and vulnerable to program
changes", and the ML Kit later added a garbage collector for the leaks region
inference leaves.

### 2.2 GNU obstacks

The one earlier design that states Goose's per-stack invariant as a rule. An
obstack ([glibc manual](https://sourceware.org/glibc/manual/latest/html_node/Obstacks.html))
is a stack of objects: "the last object allocated must always be the first one
freed", and `obstack_free` of an object frees it "along with everything
allocated in obstack-ptr since object". One object at a time may be grown
incrementally with `obstack_grow`; while it grows, the obstack cannot allocate
anything else, and `obstack_finish` closes it, after which another may grow.
C code passes an obstack to a callee that builds its result there, which is
point 5 as a convention. The ECOOP 2022 paper of §2.6 lowers its shadow stack
to this API.

What differs: obstacks are a run-time library, the programmer chooses how many
and which object goes where, and nothing is checked. Storage is chunked, so a
growing object is copied when it outgrows its chunk ("its address will
change"): interior pointers into the growing object are not stable until it is
finished, which is the property Goose's reservations exist to give.

### 2.3 ParaSail

Tucker Taft's pointer-free language has no global heap and no collector. "All
of the objects declared in a given scope are associated with a storage region,
essentially a local heap. As an object grows, all new storage for it is
allocated out of this region. As an object shrinks, the old storage can be
immediately released back to this region. When a scope is exited, the entire
region is reclaimed." Results go where they are needed: "when a function is
called, the region in which the result object should be allocated is passed
as an implicit parameter. This target region is determined by how the function
result is used", so "there is no copying at the call site upon function
return" ([Taft, "ParaSail: A Pointer-Free Pervasively-Parallel Language for
Irregular Computations", Programming 2019, §3.3](https://arxiv.org/abs/1902.00525)).
That is Goose's destination placement, decided at run time. Safety follows
from the absence of pointers: objects are values, and assignment between
regions copies or moves.

What differs: a region is a local heap with reuse inside it, not a bump stack;
an expandable object grows by linking new pieces, with "pointers still used
behind the scenes", so growth is not contiguous and nothing like point 2
holds; regions are created one per scope entry at run time, so their count is
dynamic; and every object carries its region's identity at run time.

### 2.4 Ada, and GNAT without allocators

An Ada program under `pragma Restrictions (No_Allocators)` has two stacks per
task. GNAT's secondary stack ([`s-secsta.ads`](https://gnu.googlesource.com/gcc.git/+/refs/heads/master/gcc/ada/libgnat/s-secsta.ads))
is "part of the runtime support for functions that return results of
caller-unknown size", such as a `String`: the callee pushes the result, the
caller uses it in place or copies it, and compiler-inserted `SS_Mark` and
`SS_Release` pairs release it en masse at scope boundaries. Build-in-place
([RM 7.6](https://ada-lang.io/docs/arm/AA-7/AA-7.6)) constructs a limited
result directly in the caller's object, the callee receiving the destination
through hidden extra formals. Accessibility levels ([RM
3.10.2](https://ada-lang.io/docs/arm/AA-3/AA-3.10)) are a static scope-depth
rule with no annotations, "in most cases enforced at compile time by Legality
Rules", with run-time checks where a level arrives as an implicit parameter:
the direct ancestor of Goose's depth check.

What differs: no Ada array can change its bounds after creation, so there is
no growth and nothing for point 2 to say; `Bounded_Vectors` ([RM
A.18.19](https://www.adaic.org/resources/add_content/standards/12rm/html/RM-A-18-19.html))
have a fixed capacity, like Goose's `T[..k]`; the stack count is two, not
computed; an unconstrained non-limited result is built on the secondary stack
and then copied; and an array of variable-length strings needs access types,
which need the heap.

### 2.5 The arena idioms of modern C

The substrate is the same. [Ryan Fleury's "Untangling Lifetimes: The Arena
Allocator"](https://www.rfleury.com/p/untangling-lifetimes-the-arena-allocator)
reserves "a massive upper-bound of contiguous virtual address space, then
commit[s] physical pages as needed" without relocating anything, marks and
releases positions like a stack, and has the caller choose the arena a callee
builds its result in, which is point 5. His scratch-arena conflict, where a
function's result arena is also its scratch arena so "the result memory is
actually freed before returning to the caller", is the dynamic form of Goose's
rule that two live growables never share a stack, and his conclusion that two
scratch arenas suffice is N computed by hand. [Chris Wellons's "Arena
allocator tips and tricks"](https://nullprogram.com/blog/2023/09/27/) passes a
scratch arena by value so a callee's allocations are freed on return, and his
[dynamic arrays](https://nullprogram.com/blog/2023/10/05/) extend in place
exactly when the array ends at the arena's next allocation, which is point 2's
"the growable is topmost". [Our Machinery's "Virtual Memory
Tricks"](https://ruby0x1.github.io/machinery_blog_archive/post/virtual-memory-tricks/index.html)
grows arrays in reserved address space so that "the array never moves".
Varnish's [workspace](https://github.com/varnishcache/varnish-cache/blob/master/bin/varnishd/cache/cache_ws.c)
is a production case: one reservation at a time hands the caller all
remaining space to grow into, a release keeps the used prefix, and snapshots
reset LIFO.

What differs: all of it is convention. The number of arenas, which value lives
where and whether a reference outlives its arena are the programmer's
responsibility, and an array of strings is an array of pointers.

### 2.6 "What If We Don't Pop the Stack?"

[Xhebraj, Bračevac, Wei and Rompf, ECOOP
2022](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.15)
is the one paper that frames Goose's problem as its own: since every return
pops the stack, "it is difficult to return stack-allocated data from a callee
upwards to its caller — especially variable-size data", and the known fixes
are boxing, reserving space in the parent frame, or "stacks of resizable
regions (with overall increased complexity and loss of performance
predictability)". Their answer is to delay the pop: a callee returning a
stack value leaves its frame in place until an ancestor returns a heap value,
with a type system of storage modes keeping heap objects from pointing at
stack ones. Results such as a filtered list are built incrementally on the
stack, and the implementation, in Scala Native, is a shadow stack that
"resembles Obstacks". On p. 15:16 they write that "it would be an interesting
extension to map individual storage levels to separate physical runtime
stacks", which is the design Goose takes.

What differs: one stack, a delayed pop in place of a destination stack, no
in-place growth as a rule, and lightweight annotations where Goose has none.
The destination-passing-style line of work is the other half of this paper's
neighbourhood: [Shaikhha, Fitzgibbon, Peyton Jones and Vytiniotis, FHPC
2017](https://www.microsoft.com/en-us/research/publication/using-destination-passing-style-compile-functional-language-efficient-low-level-code)
have the caller supply every array's output buffer, sized ahead by shape
inference, and note that this "enables highly-efficient stack-like memory
allocation discipline"; [Minamide, POPL
1998](https://dl.acm.org/doi/10.1145/268946.268967) and [Bagrel and
Spiwack, OOPSLA 2025](https://arxiv.org/abs/2503.07489) type the holes
and destinations. Goose needs no size ahead of time, since the result grows at
the stack top.

### 2.7 Cyclone's LIFO arenas

Cyclone ([Grossman et al., PLDI
2002](https://www.cs.tufts.edu/comp/150BUGS/cyclone-2002.pdf)) has stack
regions for blocks, lexically scoped dynamic regions that allow unlimited
allocation and die at block exit, and a heap; a LIFO discipline on region
lifetimes gives the "outlives" relation its region subtyping uses, and a
callee allocates into a region handle the caller passes. Their experience
report ([Hicks, Morrisett, Grossman, Jim, ISMM
2004](https://homes.cs.washington.edu/~djg/papers/cyclone_ismm04.pdf)) found
LIFO arenas "useful when callers know object lifetimes but only callees can
determine object sizes", which is Goose's thesis, and found them "not suited"
to servers and event loops, which is why Cyclone added unique pointers,
reference counting and keyed dynamic regions.

What differs: a dynamic region is a linked list of pages, each twice the size
of the last, with no in-place growth; pointer types carry region annotations
with inference inside functions only; region handles are run-time values and
their number is dynamic ("when throwing an exception, the number of regions to
deallocate is not known statically").

### 2.8 OxCaml's stack allocation

Jane Street's OCaml ([reference](https://oxcaml.org/documentation/stack-allocation/reference/))
allocates local values on "a separately-allocated stack that follows the same
layout as the OCaml minor heap", distinct from the control stack, one per
domain; a region is a function body or loop body, entering one records the
stack pointer and leaving resets it; and "the type-checker guarantees that
local values do not escape their region", with modes inferred inside a
compilation unit. `exclave_` ends the current region early so a result is
built in the caller's region, in tail position.

What differs: one such stack, with the collected heap still the default; no
value grows; "mutable fields and array elements require their contents to be
global", a restriction Goose's root tracking avoids; and the result trick
reaches one level.

### 2.9 Ruggieri and Murtagh, 1988

["Lifetime analysis of dynamically allocated objects", POPL
1988](https://dl.acm.org/doi/10.1145/73560.73585) is the earliest static
placement of heap objects by lifetime: each object goes into a local heap
attached to the activation record of the procedure whose lifetime encloses
it, found by an interprocedural analysis of which allocations a procedure
returns. The placement is root-based as Goose's is; the heaps are per
activation, there is no growth and no safety claim beyond the placement.

### 2.10 Automatic pool allocation

[Lattner and Adve, PLDI 2005](https://llvm.org/pubs/2005-05-21-PLDI-PoolAlloc.html)
partition a C program's heap objects into a statically determined set of
pools, created and destroyed at the entry and exit of the function in which
each non-escaping data structure lives. It is the nearest precedent for a
compiler computing a fixed set of allocation areas with scope-bound lifetimes;
the assignment is by data-structure identity from a points-to analysis rather
than by liveness, the pools hold separately allocated objects, and the
transformation adds no safety.

### 2.11 Fels

A 2025 hobby language ([repository](https://github.com/fels-lang/fels),
[design post](https://dev.to/chrischtel/checking-at-compile-time-that-arena-memory-cant-escape-its-block-1jie))
with named, block-tied bump zones freed at block exit and a checker that tags
every value with its zone's nesting depth, rejecting an assignment to an outer
variable, a return, or a store of a zone value, with `borrow` on parameters as
the only marker. It has Goose's depth check by zone rather than by variable;
the zone count is the programmer's, a result cannot leave its zone, which is
the opposite of point 5, and there is no in-place growth rule.

### 2.12 Real-time Java's scoped memory, and its static typings

The RTSJ's [`ScopedMemory`](https://www.rtsj.org/specjavadoc/javax/realtime/ScopedMemory.html)
areas are entered and left on a scope stack, reclaimed en masse, and bound by
the rule that an object in an outer, longer-lived area may not reference one
in an inner area: Goose's store rule, checked at run time on every
assignment. [Scoped Types (Zhao, Noble, Vitek, RTSS
2004)](https://janvitek.org/pubs/rtss04.pdf) make the check static at the
granularity of Java packages, and [Boyapati, Sălcianu, Beebee and Rinard, PLDI
2003](https://people.csail.mit.edu/rinard/techreport/MIT-LCS-TR-869.pdf) do so
with ownership and region parameters on classes, whose "last in first out"
region lifetimes give an outlives relation. None has growth, inline nesting or
destination placement.

## 3. Multiple stacks put to other uses

Several systems have more than one stack, or a stack where objects are freed
en masse, without any of them being used as Goose uses its data stacks.

* **Forth** keeps a data stack, a return stack and a floating-point stack,
  which hold operands, one cell each. Its dictionary is the Goose-like part:
  `HERE` is the next free address, `ALLOT` and `,` extend the one region
  under construction contiguously, a negative `ALLOT` or `MARKER` releases
  LIFO, and addresses below `HERE` never move ([Forth-2012
  §3.3.3](https://forth-standard.org/standard/usage),
  [`MARKER`](https://forth-standard.org/standard/core/MARKER)). One region,
  nothing checked.
* **Prolog's WAM** has a global stack on which structures are built, a local
  stack of environments and choice points, a trail and a push-down list.
  Choice points save the global stack's top so that failure reclaims "all the
  structures and variables constructed during the failed attempt" at once
  ([Aït-Kaci, "Warren's Abstract Machine: A Tutorial
  Reconstruction"](https://wambook.sourceforge.io/)). Reclamation comes
  from backtracking, not scope exit; terms are immutable; deterministic
  programs need a collector.
* **PostScript's `save` and `restore`** snapshot virtual memory and reset it
  to the snapshot, nested, with `invalidrestore` where a newer object is
  still referenced ([PostScript Language Reference
  Manual](https://www.adobe.com/jp/print/postscript/pdfs/PLRM.pdf)): a
  dynamic version of "a reference may not outlive its root" over one stack
  of levels, with fixed-size objects.
* **Turbo Pascal's `Mark` and `Release`** made the early heap a stack: `New`
  bumped the heap top and `Release` cut it back to a mark, freeing everything
  above at once. No growth, no checks.
* **Icon's string region** is one contiguous bump region for all strings, and
  concatenation appends in place when the left operand ends at the region's
  free pointer, because it "was the last string allocated and need not be
  re-allocated" ([`ocat.r`](https://github.com/gtownsend/icon/blob/master/src/runtime/ocat.r)).
  Point 2 for one data type, under a compacting collector.
* **Odin, Zig, Jai and C3** offer bump arenas and temporary allocators chosen
  by the programmer. Odin's
  [`virtual.Arena`](https://pkg.odin-lang.org/core/mem/virtual/) reserves
  address space and commits in steps, and both it and Zig's
  [`ArenaAllocator`](https://github.com/ziglang/zig/blob/master/lib/std/heap/arena_allocator.zig)
  resize an allocation in place only when it is the most recent one; C3's
  [`@pool`](https://c3-lang.org/language-common/memory/) frees a scope's
  temporaries at its exit. All dynamic, none checked.
* **PL/I's `AREA` and `OFFSET`** types are a copyable storage pool and a
  reference relative to it, so an area moved as a whole keeps its links
  valid ([IBM PL/I language
  reference](https://www.ibm.com/docs/SSY2V3_5.3.0/lr/ofda.html)): a
  precedent for Goose's pool-relative references
  ([§3.9](../goose_spec.md#39-relative-references)) only; areas are not
  stacks.

## 4. Relatives of the lifetime rule

Goose's lifetime rule, that a reference may not outlive the variable owning
its target, checked by scope nesting with no annotations, has relatives that
say nothing about where data lives.

* Algol 68's scope rule, that the scope of an assignment's left side may not
  exceed that of its right, was the first static check of this shape over
  stack-allocated (`loc`) objects, with a run-time check where the static one
  did not decide ([Berry, 1970](https://cs.uwaterloo.ca/~dberry/FTP_SITE/reprints.journals.conferences/Berry1970ImpleModelsA68.pdf)).
  Ada's accessibility levels (§2.4) are its descendant.
* Second-class values ([Osvald, Essertel, Wu, González-Alayón, Rompf, OOPSLA
  2016](https://www.cs.purdue.edu/homes/rompf/papers/osvald-oopsla16.pdf))
  may be passed down but never stored or returned, giving "stack-bounded
  lifetimes" by a first-class/second-class marker. Reachability types
  ([Bao, Wei, Bračevac, Jiang, He, Rompf, OOPSLA
  2021](https://www.cs.purdue.edu/homes/rompf/papers/bao-oopsla21.pdf))
  carry in each type the set of variables a value may reach, which is a
  type-level form of Goose's roots. Capturing types in Scala ([Boruch-Gruszecki
  et al., TOPLAS 2023](https://plg.uwaterloo.ca/~olhotak/pubs/toplas23.pdf))
  do the same for capabilities.
* [Chapel's lifetime checker](https://chapel-lang.org/docs/technotes/lifetimeChecking.html)
  rejects a borrow that would outlive its owner by lexical scope, with
  optional `lifetime` clauses; classes stay on the heap.
* [Hylo](https://docs.hylo-lang.org/language-tour/bindings) keeps references
  second-class as parameter conventions and projections, checked by an
  abstract interpreter "with no need for lifetime annotations"; growable
  collections are heap-backed.
* [Brandon, Driscoll, Dai, Ragan-Kelley, Milano and Aiken, OOPSLA
  2026](https://doi.org/10.1145/3798221) infer borrows and lifetimes with no
  annotations in a pure language, inserting reference counts where inference
  fails; the heap remains.
* D's [DIP1000](https://github.com/dlang/DIPs/blob/master/DIPs/other/DIP1000.md)
  `scope` keeps a reference inside its lexical scope, inferred for parameters
  and checked in `@safe` code, over the native stack.
* Replacing lifetime parameters by specialization per root appears outside
  the literature only, in [Fernando Borretti's essay on type systems for
  memory safety](https://borretti.me/article/type-systems-memory-safety) and
  Sean Baxter's [P3444R0, "Memory Safety without Lifetime
  Parameters"](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2024/p3444r0.html).

The escape-analysis literature marks the gap from the other side: stack
allocation of objects in Java compilers stops at variable-sized arrays
because a frame's size is fixed ([Kotzmann and Mössenböck, VEE
2005](https://www.usenix.org/legacy/events/vee05/full_papers/p111-kotzmann.pdf);
[OpenJ9's optimistic stack allocation, 2024](https://dl.acm.org/doi/10.1145/3656389)),
which is what a growable value's own stack removes.

## 5. What no precedent was found for

* Assigning growable values to a compile-time number of stacks by liveness,
  as registers are assigned, with sequentially live values sharing a stack.
* "Exactly one resizable per stack, always on top, interior references stable
  across growth" as a language invariant rather than a library convention:
  obstacks state the rule and relocate, the arena idioms keep addresses and
  leave the rule to the programmer.
* Specialization per reference root in place of lifetime parameters, as a
  published technique.
* A restriction on recursion whose purpose is to keep the stack count a
  constant.
* Variable-size data nested inline, an array of strings in one block, on
  stacks of this kind.

Their combination, with destination placement through any depth of calls and
the shrink rule, is what the survey did not find elsewhere.

## 6. How the survey was done

Five parallel web searches in October 2026, each over a group of candidates:
dynamic arena and obstack-like designs; static region systems; Ada, OCaml,
ParaSail and real-time Java; a sweep of production, hobby and research
languages (Austral, Verona, Cogent, Wuffs, Ivory, occam, Oberon, Mesa, CLU,
Scopes, Myrddin, Hare, Inko, Carp, Mojo, Koka, Lobster, Nim, V, Bosque, Pony,
Jakt, Roc, Gleam, Sing#, Deca, Vault, BitC, ATS, Mezzo, SPARK, June, Mercury,
Ante, Bone Lisp, Hike, Dyon, Vale, Zest, Hume, Virgil, Cone, among others);
and the academic record under multi-stack allocation, stack allocation of
variable-sized data, lifetime inference without annotations, destination
passing and frame-based heaps. The quotations from the ParaSail, ML Kit
retrospective and ECOOP 2022 papers were checked against the papers' text.
The [Hacker News discussion of Goose](https://news.ycombinator.com/item?id=49748954)
surfaced no candidate beyond these. Everything in the sweep not named above
either allocates on a collected or manually managed heap, allocates nothing
at all, or is fully static with no recursion, and so shares at most one point
of §1.
