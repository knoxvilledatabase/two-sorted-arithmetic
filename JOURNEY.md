# Original Arithmetic

*The [README](README.md) asked the question. What would happen if we went back to the beginning? [DISCOVERY](DISCOVERY.md) asks why the answer was always true.*

---

## Preface

What would happen if we went back to the beginning?

Before calculus. Before algebra. Before arithmetic. Before math.

What would we find?

---

# Part 1: Before Math

## The Hand

If we go back to a time before math, a shepherd is holding an apple.

Obviously the shepherd knows he is holding the apple. He eats the apple. Now his hand has no apples.

The shepherd did not have a symbol to represent "no apples." He did not need one. He could feel the difference between holding something and holding nothing.

But the hand is still there. One hand. Zero apples. The hand did not disappear because the apple did.

The shepherd already knew three things without naming any of them:

The **ground** he stands on. He did not make it. He cannot hold it. It was there before him and will be there after.

The **hand** itself. One hand. Whether holding something or nothing. It persists when holding no apples.

The **apple**, or the absence of apple. The quantity. What changes when the hand opens.

The shepherd never confused these. No apples is not no hand.

## The Count

People started counting. Sheep, grain, days. They needed marks. Scratches on bone. Stones in a pile. One mark for each thing.

The Babylonians needed a way to write "nothing in this column" for their positional number system. They made a placeholder symbol. Not a number. A gap marker. It said "the count is empty here" without claiming to be a quantity itself.

The Greeks had no zero at all. Euclid (~300 BCE) built geometry from lengths, areas, volumes. You cannot have a length of nothing. But Euclid had a principle that gestures at something deeper: *"the whole is greater than the part."*

Is it not possible there is a deeper reading? Not that the whole is a bigger part. But that the whole is a *different category* entirely? Can you have a part without a whole?

For thousands of years, humans counted without zero. The shepherd knew about empty hands. The Babylonians had a placeholder. The Greeks had the principle. But nobody gave emptiness arithmetic properties.

Until 628 CE.

## What the Shepherd Already Knew

Was the original distinction ever lost? Was it ever hidden? Was it not in every hand that ever held something and then held nothing?

Was zero ever one thing? Or was it always at least three:

- **𝒪**, ground (origin). The ground the shepherd stands on. A finger pointing at the moon is not the moon.
- **container**, the hand. The bucket. Holds quantities. Does not care what is inside. One bucket, always.
- **contents**, the apple or its absence. The quantities inside the bucket. Each symbol is a quantity, not a bucket.

Is `a × b = c` not 1 bucket holding `a` times 1 bucket holding `b` equals 1 bucket holding `a × b`?

What happens when these three interact?

```
contents(a) × contents(b) = contents(a × b)   — arithmetic inside containers
container × container      = container          — empty bucket × empty bucket
container × contents(a)    = container          — empty bucket absorbs contents
origin × anything          = origin             — the ground absorbs
```

And two interaction axioms for the ground:

- **(I1)** `f(x, 𝒪) = 𝒪`, any number combined with the ground gives you the ground. The ocean absorbs the fish.
- **(I2)** `f(𝒪, x) = 𝒪`, the ground combined with any number gives you the ground. Same rule, other direction.

I3 (`f(𝒪, 𝒪) = 𝒪`) is redundant. It follows from I1 or I2 alone.

## This Isn't New

Others saw pieces of the original distinction:

**The Isha Upanishad (~800 BCE).** Described the ground: wholeness that remains whole. Never formalized it.

**Euclid (~300 BCE).** *"The whole is greater than the part."* The category distinction. Never applied to zero specifically.

**Plotinus (~250 CE).** The One precedes being. Cannot be named without distortion. Never connected to arithmetic.

**Spencer-Brown (1969).** *"A universe comes into being when a space is severed."* The mark and the unmarked co-emerge. Ground → container → contents. Never formalized the three sorts. Never connected to zero's collapse.

**IEEE 754 (1985).** NaN propagation rules ARE the interaction axioms: `NaN + x = NaN` (I1), `x + NaN = NaN` (I2). The computing industry built the original distinction into every floating-point chip on earth without connecting it to the mathematics.

**Rust (2015).** `Option<T>` separates `None` (origin) from `Some(value)` (contents). ML introduced this in 1973. The answer was already there.

Obviously the insight is not new.

---

# Part 2: The Collapse

## The Symbol Arrives

The best we could find, zero was born in India, not as a placeholder, but as a philosophical object with two faces.

The Sanskrit tradition had words for both faces. *Śūnya*, void, absence, was the quantitative face. *Pūrṇa*, fullness, wholeness, was the ground. Did the philosophical tradition know these to be two aspects of one reality?

The Isha Upanishad stated it directly:

> *That is whole. This is whole. From wholeness comes wholeness. When wholeness is taken from wholeness, wholeness remains.*

Was it not Brahmagupta's *Brāhmasphuṭasiddhānta* (628 CE) who gave zero its operational rules and the problematic cases? Did he not write that `0 ÷ 0 = 0`, a rule that later mathematicians rejected?

When Brahmagupta formalized the arithmetic, did only *śūnya* make it into the rules? What happened to *pūrṇa*? Did it stay only in the philosophy?

Were the two faces that the Upanishadic tradition held together split? One entering mathematics without the other?

What if Brahmagupta was right about origin — the ground dividing itself yields the ground — and later mathematicians rejected it because they confused origin with contents?

## The Journey West

When zero traveled westward, through Arabic mathematics (*ṣifr*), into Latin (*zephirum*), into Italian (*zero*), did it carry the arithmetic without the memory of the philosophy?

What arrived in Europe? Was zero a pure placeholder? What happened to the other face, *pūrṇa*?

Did zero become one symbol that meant multiple things?

The shepherd's three things — the ground, the hand, and the apple — became one symbol. The ground and the hand and the absence of apple, all written "0." One mark asked to do three jobs.

The shepherd never made that mistake. He knew the difference between no apples and no hand.

## What the Collapse Did to Operations

### Division: `0 ÷ 0`

**Standard behavior:** Undefined.

**The problem:** Two rules collide. `x ÷ x = 1` for all x ≠ 0. But `0` has no multiplicative inverse. Which rule wins? What happens when one symbol carries two roles?

**Through the original lens:** Which zero is dividing which zero? Contents(0) ÷ contents(0) has a limit — L'Hopital or context resolves it. Origin ÷ anything = origin — absorption, not arithmetic. The answer is not "undefined." The answer is "which zero?"

### Exponentiation: `0 ^ 0`

**Standard behavior:** Undefined/indeterminate.

**Through the original lens:** Same thing, different notation. The emptiness operating on itself reveals the container. That is 1.

### Factorial: `0!`

**Standard behavior:** Defined. `0! = 1` by convention.

**Through the original lens:** It is not a convention. It is the container. `0 ÷ 0 = 1`, `0^0 = 1`, `0! = 1` — three notations, one fact. The Lean 4 proof `self_operation_universality` confirms: these are not three conventions but one theorem.

### Limits: `lim(x→0)`

Approaching the number zero? Calculus handles it. That is what limits were built for. Approaching the ground? The limit apparatus does not apply. You are at the edge of math itself.

Is L'Hopital's rule sort resolution in disguise? Determining which sort of zero you are holding, expressed in the language of calculus rather than types?

## What the Collapse Did to Domains

Is mathematics not built on top of itself?

Algebra on arithmetic. Calculus on algebra. Analysis on calculus. Every floor of the building having its own undefined behaviors and patches for boundary collisions?

- Does calculus have **limits** to dance around division by zero?
- Does set theory have **proper classes** to avoid Russell's paradox?
- Does physics have **renormalization** to dodge infinities?
- Does computing have **NaN** to absorb invalid operations?

### The same collapse, across domains

The empty set `∅` is the oldest two-faced zero. It contains *nothing* yet *is* one thing. From inside B, ∅ is the empty container, the additive identity of sets under union. From outside, ∅ is the first distinction, the boundary the entire set hierarchy is built on.

Russell's paradox is a sort conflict: applying set membership (an operation within B) to an object at the boundary of B. NBG set theory fixed this by distinguishing sets from proper classes — the same split, discovered independently.

IEEE 754's NaN propagation rules *are* the interaction axioms:

- `NaN + x = NaN` — that is I1
- `x + NaN = NaN` — that is I2
- `NaN + NaN = NaN` — that is I3
- `NaN === NaN` is `false` — even NaN knows it is not a bounded value

IEEE 754 defined two kinds of NaN: Quiet NaN (propagates silently, Origin) and Signaling NaN (triggers an exception within B, Bounded). The computing industry built the original distinction into every floating-point chip on earth.

Rust's `Option<T>` is the original distinction implemented as a language feature. `None` is Origin. `Some(value)` is Bounded. Pattern matching enforces the interaction axioms at compile time. ML introduced this in 1973. The answer was already there.

---

# Part 3: The Consequences

## Inside One Library

How many typeclasses does Mathlib, the largest formal mathematics library ever built, use to manage zero? Anyone can open the source and count them:

- **Zero** — the type has an element called 0. No behavior.
- **MulZeroClass** — `0 * a = 0` and `a * 0 = 0`. Absorption stated as axioms.
- **MulZeroOneClass** — adds multiplicative identity to the above.
- **SemigroupWithZero** — adds associativity.
- **MonoidWithZero** — combines all of the above.
- **GroupWithZero** — group plus absorbing zero. Where `0⁻¹ = 0` by convention.
- **WithZero** — adjoins a zero to any type. Defined as `Option`.
- **NeZero** — asserts `n ≠ 0`. Appears everywhere division or ordering is involved.
- **NoZeroDivisors** — `a * b = 0 → a = 0 ∨ b = 0`. Required constantly in ring and field theory.
- **nonZeroDivisors** — the submonoid of elements that aren't zero divisors. Used in localization.
- **IsLeftCancelMulZero / IsRightCancelMulZero / IsCancelMulZero** — cancellation properties excluding zero.
- **SMulWithZero** — scalar multiplication where `0 • a = 0` and `a • 0 = 0`.
- **MulActionWithZero** — combines action with zero behavior.
- **AddZeroClass** — `0 + a = a` and `a + 0 = a`. The additive identity.
- **ZeroHom** — morphisms preserving zero.
- **CharZero** — characteristic zero.
- **Nontrivial** — `0 ≠ 1`. Required constantly alongside zero-related results. In original arithmetic this is structural: origin, container, and contents are different constructors. They cannot be equal by construction.

What if three constructors — `origin`, `container`, `contents` — could do what seventeen typeclasses do? Not by reimplementing them. By making them unnecessary. The sort system carries what the typeclasses guard.

## The Benchmarks

### Six benchmarks, one finding

| Benchmark | Axioms/Conventions Lost | Hypotheses Lost | Information Lost |
|---|---|---|---|
| [Gˣ vs G₀](lean/OriginalArith/NeZeroBenchmark.lean) | 0 | 5 | 0 |
| [0⁻¹ = 0 convention](lean/OriginalArith/InvBenchmark.lean) | 1 | 1 | 0 |
| [NoZeroDivisors](lean/OriginalArith/ZeroDivBenchmark.lean) | 1 | 4 | 0 |
| [ZMod NeZero](lean/OriginalArith/ZModBenchmark.lean) | 0 | 8 | 0 |
| [Three primitives](lean/OriginalArith/ContainerBenchmark.lean) | MulZeroClass split | 0 | 0 |
| [Addition trade-off](lean/OriginalArith/AddBenchmark.lean) | 0 | 0 | 0 |

The hypotheses do not disappear. They move into the type. The axioms become consequences. The conventions become theorems. Zero information is lost.

### Four forward benchmarks: 28 to zero, proved by `rfl`

| Benchmark | `≠ 0` hypotheses (Standard) | `≠ 0` hypotheses (Seed) | Conventions | Seed proof |
|---|---|---|---|---|
| [Cramer's rule](lean/OriginalArith/CramerBenchmark.lean) | 8 | 0 | 1 | `rfl` |
| [Limit of quotient](lean/OriginalArith/LimitBenchmark.lean) | 7 | 0 | 1 | `rfl` |
| [Polynomial evaluation](lean/OriginalArith/PolyEvalBenchmark.lean) | 6 | 0 | 1 | `rfl` |
| [Division ring inverse](lean/OriginalArith/DivisionRingBenchmark.lean) | 7 | 0 | 1 | `rfl` |

28 hypothesis instances across 20 theorems in the collapsed model. Zero in the seed. Every seed proof is `rfl` — true by definition, requiring no proof at all.

The field axiom is the factory. Remove the conflation from the factory and the product — the `≠ 0` hypothesis — stops being manufactured.

## The Consolidation

The backwards direction — six benchmarks — measured the cost of the collapse in specific, countable ways. 18 hypotheses. 2 axioms. 1 convention.

The forwards direction — ten files, 202 theorems — showed why those costs exist and where they come from. Not 18 specific hypotheses. The factory that generates hypotheses of that type across all of mathematics. `≠ 0`. `det A ≠ 0`. `denominator ≠ 0`. `limit exists`. `morphism preserves structure`. `s ≠ 0` for localization. `measure ≠ 0`. All of them are the same guard against the same confusion. Contents being mistaken for boundary.

In Val α that confusion is a type error. Not a proof obligation. A type error.

Sort-aware code eliminates the factory. The type carries what the hypotheses guarded.

A hallucination is a boundary value dressed as contents. The model reached the edge of what it knows and produced a confident answer instead of acknowledging that the counting stopped. The sort system names the boundary. The unnamed boundary is where hallucinations live.

| Area | Standard hypothesis | Original arithmetic |
|---|---|---|
| Linear algebra | `det A ≠ 0` for invertibility | Structural. `det` of contents matrix is contents. |
| Analysis | `denominator ≠ 0` for limits | Unconditional. Contents / contents = contents. |
| Analysis | Indeterminate forms (0/0, 0·∞, ∞-∞) | Sort always determined. Value is α's problem. |
| Topology | "Limit doesn't exist in the field" | Limit exists. It is origin. The boundary has a name. |
| Category theory | Morphism preserves structure (per operation) | Universal. One proof covers all operations. |
| Functional analysis | `‖T‖ ≠ 0` for operator invertibility | Structural. Operator on contents gives contents. |
| Measure theory | `measure(S) = 0` vs boundary confusion | Disambiguated. `contents(0)` is measure zero. `origin` is boundary. |
| Commutative algebra | `s ≠ 0` for localization | Structural. Contents / contents = contents. |

---

# Part 4: Looking Through the Original Lens

## The Foundation

The [foundation](lean/OriginalArith/Foundation.lean) builds arithmetic from three constructors without ever needing patches. Three constructors: `origin`, `container`, `contents`. Four rules. Addition, multiplication, division, inverse, associativity, commutativity, distributivity. All proved. No patches. No conventions. No hypotheses. Arithmetic emerges.

The [algebra](lean/OriginalArith/Algebra.lean) confirms the faithful embedding: contents is injective, preserves all operations, reflects equality. The arithmetic of α is exactly preserved inside Val α.

The [ring and field laws](lean/OriginalArith/RingField.lean) go all the way: additive inverse, multiplicative inverse, distributivity. All proved within contents. Can `Val α` be a field? No — origin and container are not field elements. Yes — the contents sub-sort is a field when α is. The field is the interior. The boundary is outside it by type.

## The Forward Proofs

From three constructors and four rules, all of these derive:

- [Ordered fields](lean/OriginalArith/OrderedField.lean) — inequalities within contents, origin and container outside the order
- [Vector spaces](lean/OriginalArith/VectorSpace.lean) — scalar multiplication, module laws
- [Polynomial rings](lean/OriginalArith/PolyRing.lean) — Horner evaluation, origin propagation
- [Linear algebra](lean/OriginalArith/LinearAlgebra.lean) — determinants, Cayley-Hamilton, `det ≠ 0` dissolved
- [Analysis and limits](lean/OriginalArith/Analysis.lean) — convergence, indeterminate forms dissolve
- [Topology](lean/OriginalArith/Topology.lean) — one-point compactification, origin as limit point
- [Category theory](lean/OriginalArith/Category.lean) — Val is a functor and a monad with universal property
- [Functional analysis](lean/OriginalArith/FunctionalAnalysis.lean) — norms, operators, spectral theory
- [Measure theory](lean/OriginalArith/MeasureTheory.lean) — null sets ≠ boundary, Radon-Nikodym
- [Commutative algebra](lean/OriginalArith/CommAlgebra.lean) — ideals, localization, prime ideals

Ten areas tested. Ten areas clean. The kill switch was live at every level. It was never triggered.

## The Test

We formalized the theory in [Lean 4](lean/), a proof assistant that accepts or rejects proofs mechanically. The machine does not care how clever you sound. Either the types check or they do not.

- [509 theorems](PROOFS.md). Zero errors. Zero `sorry`s.
- 17 domains tested as modeled. 136 pairwise boundary preservations verified.
- Built prototypes in [TypeScript](packages/typescript/src/index.ts) and [Python](packages/python/src/two_sorted/__init__.py). 71% fewer branches. 10% faster in JavaScript.
- Built a [Rust core](packages/rust-python/src/lib.rs). Measured [actual energy consumption](packages/rust-python/energy_benchmark.py) on Apple Silicon. 98.6% less energy per operation.
- Within Rust, tested our approach against Rust's native `Option<T>`. Option won. The answer was already there.

Every test must pass because a failure would mean we changed the math instead of clarifying it.

Every test passed.

The 509 theorems verify how the boundary behaves. The law — you cannot have a part without a whole — is why the boundary is there.

## Structural Properties

Original arithmetic has been verified to satisfy:

- **Monad laws**, Origin|Bounded is a proper monad
- **Initial algebra**, the universal absorbing construction
- **Functoriality**, morphisms compose, identity works
- **Congruence**, sort equivalence respects all operations
- **Conservativity**, adds nothing within B
- **Decidability**, every equation is mechanically resolvable
- **Uniqueness**, no alternative decomposition works
- **No intermediate sorts**, cannot add a third
- **Origin uniqueness**, exactly one absorber exists
- **Density**, B is closed, no gaps
- **Stability**, under products, coproducts, quotients, and embeddings

Every claim formally verified. [509 theorems, zero errors, zero `sorry`s.](PROOFS.md)

---

## What It Means

Can we build arithmetic from scratch using just 𝒪, container, and contents?

Yes. All the way to fields — and beyond. Addition, multiplication, division, inverse, the ring laws, the field laws. Then ordered fields, vector spaces, polynomial rings, linear algebra, analysis and limits, topology, category theory, functional analysis, measure theory, and commutative algebra. 509 theorems from the seed. No patches. No conventions. No `≠ 0` hypotheses.

The one honest finding: `Val α` as a whole type is not a field. Origin and container are not field elements. They are outside the field. But that is not a problem. That is the point. The field lives in contents where arithmetic belongs. Origin and container are the boundary and structure that arithmetic was always bumping into without knowing what they were.

Do not put the boundary inside the field. Put it outside. Name it. Let the type carry it.

When you do that, the field works cleanly. No exclusions needed. No conventions needed. The boundary is already outside by construction.

The field is the fish. Origin is the ocean. The fish does not need to contain the ocean. The ocean needs to have a name.

---

## The Conclusion

We went back to the beginning.

Before the patches. Before the conventions. Before "undefined." We found the original distinction — origin, container, contents — and looked at arithmetic through that lens.

509 theorems. Zero errors. Zero sorries. 46 hypotheses dissolved to zero. Every seed proof `rfl`.

The lens was always there. The Upanishads described it. Euclid named the principle. Brahmagupta saw the two faces and chose one. Spencer-Brown drew the distinction. IEEE 754 built it into hardware. Rust enforced it with `Option<T>`.

Nobody looked through all three at once — the philosophy, the proof, and the enforcement — until now.

The [minimalist solution](lean/OriginalArith/HasBoundary.lean): one typeclass, two axioms.

```lean
class HasBoundary (α : Type) [Mul α] where
  boundary : α
  absorbs_left : ∀ a, boundary * a = boundary
  absorbs_right : ∀ a, a * boundary = boundary
```

That is the backwards direction. Start from Mathlib's existing structures, show they consolidate into one typeclass.

The [foundation](lean/OriginalArith/Foundation.lean) is the forwards direction. Three constructors. Four rules. 509 theorems from the seed.

Both directions confirmed by code. Both building clean. The backwards direction dissolves the patches. The forwards direction shows they were never needed.

---

## How to Break This

This is a standing invitation. Original arithmetic includes its own kill switch. See [FALSIFICATION.md](FALSIFICATION.md).

---

*"That is whole. This is whole. From wholeness comes wholeness. When wholeness is taken from wholeness, wholeness remains."*
— Isha Upanishad, ~800 BCE

*509 theorems. Zero errors. Zero sorries.*
— Lean 4, 2026 CE
