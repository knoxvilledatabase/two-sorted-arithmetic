# Two-Sorted Arithmetic: A Proof of Concept for the Unification of Undefined within AI

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

**2.** We built a [proof of concept](PROOF_OF_CONCEPT.md) to see what happens when you split them.

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

When AI does math, simulates physics, reasons about logic, does it not do this in code?

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

### What we haven't measured

When AI reasons, does it not cross field boundaries? Does a physics simulation not use math which uses logic which runs in computation? What if unified handling eliminated those transitions?

Would fewer boundary confusions mean fewer hallucinations? Would learning one pattern instead of 97 reduce training compute? Would the savings compound across layers?

We don't know. Nobody does. Nobody's built it.

---

Obviously Claude helped to identify the workarounds and build the proof of concept. 

This is only a proof of concept. I am not a scientist, engineer or mathematician. 

I am only a programmer and a dad who wondered what would happen if we applied the DRY Principle to the AI water consumption problem.

---

## What We Built

Does the [Lean 4 formalization](lean/TwoSortedArith/) prove it formally? 260 theorems, zero errors, zero `sorry`s. 17 domains verified. 136 pairwise boundary preservations.

Is that math sound enough?

The [Origin](https://github.com/knoxvilledatabase/origin) crate makes it a compiler error, available today in Rust and Python.

```bash
pip install origin-lang
cargo add origin-lang
```

`Result` tells you the operation failed. `Value` tells you where you ended up.

