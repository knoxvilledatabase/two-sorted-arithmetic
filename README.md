# Original Arithmetic: A Proof of Concept for the Unification of Undefined within AI

---

## The Problem

If your daughter came to you and said "Daddy, AI is drinking too much water!" What would you do? 

Obviously, AI is growing like crazy and using a lot of energy that needs cooling.

## What's already being done?

The industry answer is better cooling hardware. Closed-loop systems. Liquid cooling. A $48 billion market projected by 2034. These are valid solutions, but they all accept the heat as a given.

But what's causing all this heat in the first place?

## Could the DRY Principle help in this situation?

You already know the DRY principle simply means Don't Repeat Yourself and applying it causes a reduction in code and better performance.

Is it possible the DRY Principle could help with the AI water consumption problem?

After looking at the problem through this lens, we saw an opportunity. We noticed the same boundary check is being written independently across math, computation, and physics.

If your codebase needed the same function, would you write it 97 different ways?

A stop sign, a red traffic light, and a "road closed" barrier have different causes but the same interface, don't proceed. Would you write a separate handler for each one?

## The Journey

**1.** We traced zero back through antiquity and found it's at least three things collapsed into one symbol.

**2.** We developed a [proof of concept](PROOF_OF_CONCEPT.md) to see what happens when we uncollapse them.

**3.** Claude [prototyped it](packages/typescript/src/comparison.ts). 71% fewer branches.

**4.** Claude [tested it against Rust](packages/rust-python/energy_benchmark.py). Rust already had the answer.

## Did Rust already solve this?

Yes. It's called `Option<T>`. We measured 98.6% less energy per operation on Apple Silicon.

| | Python | Rust |
|---|---|---|
| Energy per operation | 17.81 µJ | 0.25 µJ |
| Operations in 5 seconds | 1.17M | 93.65M |

But moving to Rust is the immediate band-aid fix for computation. It's still a patch for one field.

---

## What happens when you consolidate all 97 functions into one method?

When AI does math, simulates physics, reasons about logic, isn't it doing all of that in code?

What would happen if AI understood the boundary across all fields and stopped running siloed boundary patches?

---

## Every row in this table is a separate workaround for undefined behavior.

---

### Computation

| Domain | Undefined Behavior | Workaround | Year |
|---|---|---|---|
| ALGOL W | Null reference | null pointer | 1965 |
| C | Null pointer dereference | NULL macro, manual checks | 1972 |
| SQL | Missing values | NULL, three-valued logic | 1974 |
| C++ | Null pointer dereference | nullptr, manual checks | 1979 |
| Objective-C | Nil messaging | nil returns nil | 1984 |
| IEEE 754 | Invalid float operation | Quiet NaN propagation | 1985 |
| IEEE 754 | Invalid float diagnostic | Signaling NaN exception | 1985 |
| IEEE 754 | Division by zero | ±Infinity | 1985 |
| IEEE 754 | Negative zero | -0.0 distinct from +0.0 | 1985 |
| Python | Missing value | None | 1991 |
| Python | Invalid float | float('nan') | 1991 |
| Java | Null reference | null, NullPointerException | 1995 |
| JavaScript | Missing value | null | 1995 |
| JavaScript | Uninitialized variable | undefined | 1995 |
| JavaScript | Invalid number | NaN | 1995 |
| JavaScript | Type coercion | Number(null) = 0 | 1995 |
| JavaScript | Type coercion | Number("") = 0 | 1995 |
| Ruby | Missing value | nil | 1995 |
| Java | Empty container | Optional.empty() | 2014 |
| C# | Null reference | null, nullable types | 2000 |
| C# | Null safety | nullable reference types | 2019 |
| Go | Missing value | nil | 2009 |
| Go | Zero values | zero value masking absence | 2009 |
| Dart | Null reference | null, null safety | 2011 |
| TypeScript | Strict null | strictNullChecks | 2016 |
| Kotlin | Null safety | T? nullable types | 2016 |
| Pandas | Missing data | NaN, pd.NA, None (three systems) | 2008 |
| R | Missing value | NA | 1993 |
| R | Missing value variants | NA_integer_, NA_real_, NA_complex_, NA_character_ | 1993 |
| Lua | Missing value | nil | 1993 |
| PHP | Missing value | null | 1995 |
| Perl | Missing value | undef | 1987 |
| Swift | Null reference | nil (within Optional) | 2014 |
| Erlang | Missing value | undefined atom | 1986 |
| Elixir | Missing value | nil | 2012 |
| Julia | Missing value | nothing, missing (two systems) | 2012 |
| Zig | Null pointer | optional types, null | 2016 |

### Languages that resolved the ambiguity of zero

| Language | Solution | Year |
|---|---|---|
| ML | option = SOME \| NONE | 1973 |
| Standard ML | formalized option | 1983 |
| Haskell | Maybe = Just \| Nothing | 1990 |
| OCaml | option = Some \| None | 1996 |
| Scala | Option = Some \| None | 2004 |
| F# | Option = Some \| None | 2005 |
| Swift | Optional = .some \| .none | 2014 |
| Rust | Option\<T\> = Some \| None | 2015 |

---

### What about mathematics?

| Domain | Undefined Behavior | Workaround | Year |
|---|---|---|---|
| Arithmetic | 0/0 | "indeterminate" label | ancient |
| Arithmetic | n/0 | "undefined" label | ancient |
| Arithmetic | 0^0 | convention: equals 1 | ancient |
| Arithmetic | 0! | convention: equals 1 (empty product) | ancient |
| Geometry | parallel postulate failure | non-Euclidean geometries | 1830s |
| Analysis | division by zero in limits | epsilon-delta limits | 1821 |
| Analysis | indeterminate forms 0/0 | L'Hôpital's rule | 1696 |
| Analysis | indeterminate form 0·∞ | rewrite and apply L'Hôpital | 1696 |
| Analysis | indeterminate form ∞-∞ | rewrite and apply L'Hôpital | 1696 |
| Analysis | indeterminate form ∞/∞ | L'Hôpital's rule | 1696 |
| Analysis | indeterminate form 0^0 | logarithmic limits | 1696 |
| Analysis | indeterminate form 1^∞ | logarithmic limits | 1696 |
| Analysis | indeterminate form ∞^0 | logarithmic limits | 1696 |
| Set theory | set of all sets | restricted comprehension (ZF) | 1908 |
| Set theory | Russell's paradox | proper classes (NBG) | 1925 |
| Set theory | Burali-Forti paradox | ordinal restrictions | 1897 |
| Set theory | Cantor's paradox | class/set distinction | 1899 |
| Measure theory | non-measurable sets | restrict to σ-algebras | 1905 |
| Measure theory | Banach-Tarski paradox | restrict axiom of choice | 1924 |
| Topology | indiscrete topology | separation axioms (T0-T4) | 1914 |
| Algebra | division in rings | restrict to fields/division rings | ancient |
| Algebra | zero divisors | integral domain restriction | ancient |
| Algebra | trivial ring (0=1) | require 0 ≠ 1 as axiom | ancient |
| Category theory | initial object boundary | structural axiom | 1945 |
| Category theory | empty category | convention handling | 1945 |
| Proof theory | cut-requiring proofs | cut elimination restrictions | 1935 |

---

### What about logic?

| Domain | Undefined Behavior | Workaround | Year |
|---|---|---|---|
| Logic | Liar paradox | hierarchy of truth predicates | ~400 BCE |
| Logic | self-reference | Tarski's undefinability theorem | 1936 |
| Formal systems | true but unprovable statements | Gödel's incompleteness | 1931 |
| Computability | undecidable problems | halting problem proof | 1936 |
| Type theory | Type : Type paradox | universe hierarchy (Type₀:Type₁:...) | 1972 |
| Type theory | Girard's paradox | universe polymorphism | 1972 |
| Linear logic | resource boundary | ! exponential modality | 1987 |
| Modal logic | frame boundary | Kripke frame axioms | 1959 |
| Topos theory | internal object boundary | subobject classifier | 1963 |
| HoTT | univalence boundary | universe levels | 2006 |
| Three-valued logic | truth value gaps | third value (unknown/null) | 1920 |
| Paraconsistent logic | contradictions | restrict explosion principle | 1910 |

---

### What about physics? (speculative, not formally verified)

| Domain | Undefined Behavior | Workaround | Year |
|---|---|---|---|
| Classical mechanics | singularities in potential | regularization techniques | 1800s |
| Electrodynamics | self-energy of point charge | renormalization | 1930s |
| QED | ultraviolet divergences | renormalization | 1947 |
| QED | infrared divergences | soft photon resummation | 1937 |
| QFT | vacuum energy divergence | normal ordering | 1930s |
| QFT | high-energy divergences | regularization (cutoff) | 1930s |
| QFT | dimensional divergences | dimensional regularization | 1972 |
| QFT | lattice artifacts | continuum limit | 1974 |
| QCD | confinement | lattice QCD, effective theories | 1973 |
| General relativity | Schwarzschild singularity (r=0) | assume resolution by quantum gravity | 1916 |
| General relativity | coordinate singularity | coordinate transformation | 1916 |
| General relativity | Big Bang singularity (t=0) | assume pre-Big Bang physics | 1927 |
| General relativity | cosmic censorship | Penrose conjecture | 1969 |
| Quantum mechanics | measurement problem | Copenhagen interpretation | 1927 |
| Quantum mechanics | measurement problem | many-worlds interpretation | 1957 |
| Quantum mechanics | measurement problem | decoherence | 1970 |
| Quantum mechanics | wave function collapse | "shut up and calculate" | 1964 |
| Thermodynamics | absolute zero | third law (unattainable) | 1906 |
| Cosmology | dark energy | cosmological constant | 1998 |
| Cosmology | initial conditions | inflationary models | 1981 |
| Planck scale | all theories break | "unknown" | — |
| String theory | landscape problem | anthropic principle | 2000s |
| Quantum gravity | non-renormalizable | "unsolved" | — |

---

### What's the total count?

| Field | Patches |
|---|---|
| Computation (with null) | 36 |
| Computation (solved) | 8 |
| Mathematics | 26 |
| Logic | 12 |
| Physics | 23 |
| **Total patches** | **97** |
| **Solutions** | **8** |

97 independent workarounds. 8 solutions. All 8 in computation.

---

### What we measured

- Computation alone (Python → Rust): 98.6% less energy per operation
- Within one language (NaN propagation vs traditional): 10% fewer cycles
- Branch reduction: 71% fewer branches

Every row in the table above is a branch instruction on silicon. A null check, a NaN propagation, an "undefined" handler — each one is a conditional branch that costs energy. 97 independent branch patterns means 97 independent energy costs at every inference.

The 98.6% reduction came from fixing ONE patch (Python → Rust's `Option<T>`). The table has 97.

### What we haven't measured

When AI reasons, does it not cross field boundaries? Does a physics simulation not use math which uses logic which runs in computation? What if unified handling eliminated those transitions?

A model trained on all 97 patches holds all 97 simultaneously as weights. Every inference potentially runs redundant boundary handling in the same forward pass. The DRY principle here is not about code elegance. It is about what gets baked into the model and whether that redundancy costs compute at every single inference.

Would fewer boundary confusions mean fewer hallucinations? Would learning one pattern instead of 97 reduce training compute? Would the savings compound across layers?

We don't know. Nobody does. Nobody's tested it. That's the $48 billion cooling market question stated as a testable hypothesis.

---

Obviously Claude helped to identify the workarounds and build the proof of concept. 

This is only a proof of concept. I am not a scientist, engineer or mathematician. 

I am only a programmer and a dad who wondered what would happen if we applied the DRY Principle to the AI water consumption problem.

---

## What We Built

Does the [Lean 4 formalization](lean/OriginalArith/) prove it formally? 509 theorems, zero errors, zero `sorry`s. 17 domains verified. 136 pairwise boundary preservations.

Is that math sound enough?

The [Origin](https://github.com/knoxvilledatabase/origin-lang) crate makes it a compiler error, available today in Rust and Python.

```bash
pip install origin-lang
cargo add origin-lang
```

`Result` tells you the operation failed. `Value` tells you where you ended up.

---

## Repository Map

| Path | What it does |
|---|---|
| [README.md](README.md) | The problem, the 97 patches, the DRY argument |
| [PROOF_OF_CONCEPT.md](PROOF_OF_CONCEPT.md) | The proof of concept: zero's three jobs, axioms, cross-domain pattern |
| [DISCOVERY.md](DISCOVERY.md) | Why the answer was always true: the philosophy behind the proof |
| [PROOFS.md](PROOFS.md) | 509 Lean 4 theorems, annotated |
| [FALSIFICATION.md](FALSIFICATION.md) | How to break it: the kill switch |
| [PREDICTIONS.md](PREDICTIONS.md) | Novel predictions the theory makes |
| [NEXT.md](NEXT.md) | What remains to be done |
| **The seed** | |
| `lean/OriginalArith/Foundation.lean` | Three primitives, four rules. Arithmetic from scratch. |
| `lean/OriginalArith/Algebra.lean` | Faithful embedding + algebraic laws (semigroup, monoid, three behaviors) |
| `lean/OriginalArith/RingField.lean` | Ring and field laws. The field lives inside contents. |
| **The forwards direction** | |
| `lean/OriginalArith/OrderedField.lean` | Ordered fields and inequalities within contents |
| `lean/OriginalArith/VectorSpace.lean` | Scalar multiplication and module laws |
| `lean/OriginalArith/PolyRing.lean` | Polynomial evaluation, origin propagation |
| `lean/OriginalArith/LinearAlgebra.lean` | 2×2 determinants, Cayley-Hamilton, `det ≠ 0` dissolved |
| `lean/OriginalArith/Analysis.lean` | Limits, convergence, indeterminate forms dissolve |
| `lean/OriginalArith/Topology.lean` | One-point compactification, origin as limit point |
| `lean/OriginalArith/Category.lean` | Functor, monad, universal property |
| `lean/OriginalArith/FunctionalAnalysis.lean` | Norms, operators, completeness, spectral theory |
| `lean/OriginalArith/MeasureTheory.lean` | Measures, null sets, Radon-Nikodym, integration |
| `lean/OriginalArith/CommAlgebra.lean` | Ideals, localization, prime ideals, integral domains |
| **The backwards direction** | |
| `lean/OriginalArith/HasBoundary.lean` | One typeclass. Five Mathlib concepts derived from it. |
| `lean/OriginalArith/*Benchmark.lean` | Ten benchmarks: 46 hypotheses → 0, all seed proofs `rfl` |
| **Other** | |
| `lean/*.lean` | Original working proofs (4,125 lines, standalone for live.lean-lang.org) |
| `packages/typescript/` | TypeScript prototype: 71% fewer branches |
| `packages/python/` | Python prototype |
| `packages/rust-python/` | Rust core + energy benchmark: 98.6% less energy per operation |
| [Origin](https://github.com/knoxvilledatabase/origin-lang) | The compiler that enforces it (separate repo) |

## The Foundation

[Foundation.lean](lean/OriginalArith/Foundation.lean) builds arithmetic from three primitives: `origin` (the whole), `container` (the bucket), and `contents` (quantities, 0 through infinity). Four rules govern how they interact. Addition, multiplication, division, inverse, identities, associativity, commutativity, and distributivity all emerge from those rules without patches, conventions, or hypotheses. No `NeZero`. No `NoZeroDivisors`. No `0⁻¹ = 0` convention. The type prevents the pathologies that Mathlib spends twelve typeclasses managing.

The forwards direction extends the seed through ordered fields, vector spaces, polynomial rings, linear algebra, analysis, topology, category theory, functional analysis, measure theory, and commutative algebra — 509 theorems from three constructors and four rules. The backwards direction benchmarks the seed against standard mathematics: 46 hypothesis instances across ten benchmarks, zero on the seed side, every seed proof `rfl`. Everything proved in Lean 4. Nothing broke.

