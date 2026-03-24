# Proof of Concept: A Two-Sorted Arithmetic

*The [README](README.md) asked the question. This is the formal system we built to answer it.*

---

## Where Zero Came From

Zero was born in India, not as a placeholder, but as a philosophical object with two faces.

The Sanskrit tradition had words for both faces. *Śūnya*, void, absence, was the quantitative face. *Pūrṇa*, fullness, wholeness, was the ground. The philosophical tradition knew these were two aspects of one reality.

The Isha Upanishad states it directly:

> *That is whole. This is whole. From wholeness comes wholeness. When wholeness is taken from wholeness, wholeness remains.*

Brahmagupta's *Brāhmasphuṭasiddhānta* (628 CE) gave zero its operational rules, and the problematic cases. He wrote that `0 ÷ 0 = 0`, a rule that later mathematicians rejected. But the collapse started here. When Brahmagupta formalized the arithmetic, only *śūnya* made it into the rules. *Pūrṇa* stayed in the philosophy. The two faces that the Upanishadic tradition held together were split: one entered mathematics, the other did not.

When zero traveled westward, through Arabic mathematics (*ṣifr*), into Latin (*zephirum*), into Italian (*zero*), it carried the arithmetic but lost even the memory of the philosophy. What arrived in Europe was a pure placeholder. The other face, the wholeness, the ground, had been left behind twice. First by Brahmagupta. Then by translation.

Did zero get confused? One symbol. Three jobs. Did anyone notice that the loss happened in translation, 1,400 years ago?

---

## The Oldest Evidence

Euclid's first common notion, ~300 BCE: *the whole is greater than the part.*

Most people read that as "the whole is bigger." But there's a deeper reading: the whole isn't a bigger part, it's a *different category*. You can't have the part without the whole. The whole is prior.

If that reading is right, arithmetic has been treating zero and its categorical origin as the same thing for a very long time.

---

## The Big Question

Can you have a part without a whole?

Every formal system in mathematics starts with parts, elements, sets, numbers.

If you cannot have a part without a whole, then every bounded domain presupposes something it is bounded *within*. 

That something has no name in standard mathematics. Every time a formal system hits its own boundary, division by zero, Russell's paradox, renormalization infinities, GR singularities, it is encountering the whole it never named.

To argue against the whole being a necessary precondition, you must construct an argument. An argument has parts. Parts presuppose a whole. Is the denial not self-defeating?

Is this a theorem? Theorems are proven within systems. Can this be proven within a system, or is it the precondition for systems to exist?

We used the symbol **𝒪** to represent the whole or *categorical origin* to make it thinkable.

A finger pointing at the moon is not the moon. 

---

## The Order of Emergence

This concept operates at two levels. Steps 1–2 are *metatheoretic* or "undefined."

1. **𝒪**, the undifferentiated whole or categorical origin of zero. 

2. **The first distinction**, not a step that follows 𝒪, but the single act in which three things co-emerge simultaneously and inseparably:
   - **0**, the empty contents, absence represented
   - **1**, the container, the boundary that makes a symbol possible
   - **B**, the bounded domain, the space membership requires

   These are not sequential. You cannot have any one without the other two. 0 is not an element that arrives into an already-existing B. 0 is a co-founder of B. This is why "0 ∈ B" is pedagogically useful but logically incomplete, membership implies arrival after the domain existed. 0 did not arrive. 0 constituted.

3. **Algebraic axioms**, the choices that structure B. The first structure requiring both 0 and 1 is the ring. Collapse them back together, the trivial ring where 0 = 1, and meaning disappears. Is that a coincidence? Or is it the original distinction, undone?

4. **Number systems**, ℤ, ℚ, ℝ, ℂ, finite fields, p-adic numbers. Each a different realization of B under different axioms.

5. **Operations**, division, limits, and others defined within each number system.

6. **Expressions**, `0/0`, where categorical confirmation asks *which* `0` is present.

Steps 3–6 are what formal mathematical systems can see and describe.

𝒪 sits below arithmetic as the precondition for symbols. And 0 sits at the boundary, not fully inside B, not outside it, but the act by which inside became possible.

---

## The Three Aspects of Zero

Picture a zero in your mind. How many symbols are you holding? Where did the symbols come from?

Was zero ever one thing? Or was it always at least three:

- **𝒪**, ground (origin). The whole or nature. Before symbols. Before distinction. 
- **1**, container. The part. The symbol exists. The boundary that makes it one thing.
- **0**, contents. The symbol's quantity is empty.

Are the container and the contents complementary opposites, needing each other to exist, but needing to be different to be useful? Neither can exist without a categorical origin.

`a × b = c` is 1 container times 1 container equals 1 container.

---

## Definitions

- **𝒪:** The ground or origin. The whole that has to exist before any number can. Not a number itself.

- **B:** The bounded domain. Standard mathematical objects. 0 co-constitutes B rather than belonging to it as a later member.

**Axioms:**

- **(𝒪1)** 𝒪 is not a number. You can't put the entire ocean in a fish.
- **(𝒪2)** Every formal system hits 𝒪 (the origin) at its boundary. Every one.
- **(𝒪3)** The ground (origin) divided by the ground (origin) is still the ground (origin).

**Interaction rules**, what happens when the ground touches a number:

- **(I1)** `f(x, 𝒪) = 𝒪`, any number combined with the ground gives you the ground. The ocean absorbs the fish.
- **(I2)** `f(𝒪, x) = 𝒪`, the ground combined with any number gives you the ground. Same thing, other direction.
- **(I3)** `f(𝒪, 𝒪) = 𝒪`, the ground combined with the ground is still the ground.

I3 is redundant, it follows from I1 or I2 alone. You only need two rules: the ground absorbs everything it touches, from either side.

**Two-sorted division.** `0_B ÷ 0_B` (contents by contents) → **1**, the container is revealed. Either argument involves 𝒪 → **𝒪** by I1–I3.

**Consistency.** Two-sorted arithmetic is consistent with standard arithmetic. 𝒪 models as an absorbing element outside the number line. Strictly more expressive: `x ÷ 𝒪` is well-formed here, has no interpretation in standard arithmetic. Nothing inside B changes. The bounded domain keeps its zero, its operations, its results.

What if we just gave it the right zero?

---

## Why It Cascades

Mathematics is built on top of itself. Algebra on arithmetic. Calculus on algebra. Analysis on calculus. Every floor of the building has its own undefined behaviors, its own patches for boundary collisions:

- Calculus has **limits** to dance around division by zero
- Set theory has **proper classes** to avoid Russell's paradox
- Physics has **renormalization** to dodge infinities
- Computing has **NaN** to absorb invalid operations

Each floor independently re-solving the same leak in the foundation. Each patch is code. Each line of code is an operation. Each operation is energy. Each unit of energy is heat. Each unit of heat is water. 97 independent patches across four fields, all for the same boundary.

---

## What a Symbol Cannot Do

Is every patch a symbol trying to handle something that sits outside the symbolic system? Is that why there are 97 of them?

Can you fit grass in a symbol about grass? No. The word "grass" contains no chlorophyll. The symbol is weightless, odorless, has never bent in wind. There is an absolute gulf between the sign and the thing it points to.

Can a symbol be "undefined"? Every symbol is a definition. The moment you write it, you've drawn a boundary, created a container, made one symbol.

Can a symbol remove the boundary that defines it? No. The boundary is what makes it exist. Remove it and you don't have a symbol, you have nothing recognizable at all. 

This is why every formal system that tries to reach past its own edge,`Type : Type`, the set of all sets, the program that halts on itself, doesn't break through. It breaks.

Can symbols generate anything other than symbols? No. Every proof is symbols. Every number is symbols. Every equation is symbols verifying other symbols. Math is sealed inside a completely closed system.

Can you have a concept without representation?

But the seeing came first. The symbols came after. That's the ground.

> **𝒪 is not a new formal object.** It is a name for the limit of formalizability. Naming it does not formalize it. It makes it *thinkable*.

---

## The Operations

### Division: `0 ÷ 0`

**Standard behavior:** Undefined.

**The problem:** Two rules collide. `x ÷ x = 1` for all x ≠ 0. But `0` has no multiplicative inverse. Which rule wins? What happens when one symbol carries two roles?

**Two-sorted resolution:** You're dividing the emptiness by the emptiness. What's left is the container it was sitting in. That's 1. If the ground is involved, the ground absorbs.

### Exponentiation: `0 ^ 0`

**Standard behavior:** Undefined/indeterminate.

**The problem:** `x^0 = 1` meets `0^n = 0`. Same collision as division, same collapsed union.

**Two-sorted resolution:** Same thing, different notation. The emptiness operating on itself reveals the container. That's 1.

### Factorial: `0!`

**Standard behavior:** Defined. `0! = 1` by convention.

**The problem:** Standard math gets the right answer but calls it a convention. Why does the empty product give the multiplicative identity?

**Two-sorted resolution:** It's not a convention. It's the container. `0 ÷ 0 = 1`, `0^0 = 1`, `0! = 1`, three notations, one fact. The Lean 4 proof `self_operation_universality` confirms these are not three conventions but one theorem.

### Multiplication: `0 × 0`

**Standard behavior:** Defined. `0 × 0 = 0`. No indeterminacy.

**The problem:** Not undefined, but which zero? If the ground touches it, it absorbs. If it's just numbers, it stays a number.

### Logarithm: `log(0)`

**Standard behavior:** Undefined. The limit gives −∞.

**Two-sorted resolution:** What power produces zero? That's a math question, calculus handles it. What power produces the whole? That's not a math question. The conflation made them look like the same problem.

### Division by zero: `1 ÷ 0`

**Standard behavior:** Undefined.

**Two-sorted resolution:** Which zero is the divisor? If it's the number zero, calculus handles it, the limit approaches ±∞. If it's the ground, you're dividing by the whole. The ocean absorbs the fish.

### Limits: `lim(x→0)`

Approaching the number zero? Calculus handles it, that's what limits were built for. Approaching the ground? The limit apparatus doesn't apply. You're at the edge of math itself.

L'Hôpital's rule may be sort resolution in disguise: determining which sort of zero you're holding, expressed in the language of calculus rather than types. 

When L'Hôpital resolves an indeterminate form, it is performing categorical confirmation, determining whether the zeros involved are the same sort, without having the vocabulary to say so.

---

## The Cross-Domain Pattern

### The empty set `∅`

The oldest two-faced zero, it contains *nothing* yet *is* one thing. From inside B, ∅ is the empty container, the additive identity of sets under union. From outside, ∅ is the first distinction, the boundary the entire set hierarchy is built on.

Russell's paradox is a sort conflict: applying set membership (an operation within B) to an object at the boundary of B. NBG set theory fixed this by distinguishing sets from proper classes, the same `Origin | Bounded` split, discovered independently sixty years before this framework named it.

### IEEE 754 `NaN`

NaN's propagation rules *are* the interaction axioms:

- `NaN + x = NaN`, that's I1
- `x + NaN = NaN`, that's I2
- `NaN + NaN = NaN`, that's I3
- `NaN === NaN` is `false`, even NaN knows it's not a bounded value

IEEE 754 defined two kinds of NaN: Quiet NaN (propagates silently, Origin) and Signaling NaN (triggers an exception within B, Bounded). The computing industry built the `Origin | Bounded` split into every floating-point chip on earth.

### Rust's `Option<T>`

The two-sorted distinction implemented as a language feature. `None` is Origin. `Some(value)` is Bounded. Pattern matching enforces the interaction axioms at compile time. Zero runtime cost. Zero null checks.

ML introduced this in 1973. Rust, Haskell, and Swift prove it works at the language level. What about the languages that didn't? Which ones are running most of the world's AI inference workloads? How long has the answer been available?

### JavaScript's `Number()`

The sort conflation lives in the language spec. `Number(undefined)` returns `NaN`, correct, that's Origin. But `Number(null)` returns `0`, treating Origin as Bounded. Null is not an empty container. Null is *no container*. `Number("")` returning `0` is actually correct, an empty string is an empty container, and an empty container's numeric value is zero. The real conflation is `null → 0`.

### The computational topology

Origin-handling strategy is topology-dependent. Inside a single scope, early termination is optimal, one branch buys exit from all remaining work. Across compositional boundaries, propagation is optimal, each boundary pays one check instead of coordinating an exit signal across scopes. The switch point is the sort boundary: the moment computation crosses from one bounded scope into another, propagation becomes the correct strategy.

---

## The Isomorphism Claim

The claim is isomorphism of the absorbing element structure, not of the full domains. Division by zero and Russell's paradox are not the same problem. They have the same *boundary shape*, an operation leaving its domain and hitting an absorber that satisfies I1-I3.

**Kill switch:** Prove any two of these boundaries have structurally different absorbing behavior. One counterexample kills the claim.

| Case | Operation | Domain | Boundary | Standard Response |
|---|---|---|---|---|
| Arithmetic | Division | Field ℝ | Zero as divisor | Mark undefined |
| Computation | Halting | Turing machines | Self-reference | Undecidability |
| Set Theory | Set membership | Naive set theory | All sets | Categorical restriction |
| Logic/Provability | Provability | Formal systems | Gödel sentence | Incompleteness |
| Truth Values | Truth predicate | Propositions | Liar sentence | Paradox |
| Category Theory | Hom-functor | Objects with morphisms | Initial object | Structural axiom |
| Modal Logic | Modal evaluation | Possible worlds | Kripke frame | Frame axiom |
| Topos Theory | Internal evaluation | Internal objects | The topos itself | Containment axiom |
| HoTT | Universe membership | Types in a universe | Type : Type | Universe tower |
| Linear Logic | Resource consumption | Linear resources | ! modality | ! promotion |
| IEEE 754 | Float arithmetic | Binary ℝ | Invalid operations | Two-sorted NaN |
| SQL NULL | Any operation | Relational databases | NULL value | Three-valued logic |
| Lambda Calculus | Application | λ-terms | Non-termination (Ω) | Divergence |
| Measure Theory | Measure assignment | σ-algebra | Non-measurable sets | Restrict domain |
| Game Theory | Equilibrium solving | Strategic games | No pure equilibrium | Mixed strategies |
| Topology | Separation | Topological spaces | Indiscrete topology | Weaken axioms |
| Proof Theory | Cut elimination | Formal proofs | Cut-requiring proofs | Restrict rules |

Seventeen domains tested as modeled by the two-sorted type system. Zero non-isomorphic pairs found. 136 pairwise boundary preservations verified. Five novel predictions confirmed. The kill switch has not been triggered.

*Physics candidates (renormalization, GR singularities) are structurally motivated analogies, not formally verified. See [NEXT.md](NEXT.md).*

One person, Girard, found 𝒪 twice, once in type theory in 1972, once in resource logic in 1987, without connecting them. The boundary is invisible even to the person standing closest to it.

---

## Level Invariance

The boundary reappears at every level of abstraction sufficient to encounter it.

Set theory hits 𝒪 through proper classes. Topos theory, which *contains* set theory, hits the same boundary from above. HoTT built an infinite tower of universes because 𝒪 cannot be internalized at any level. Linear logic redesigned the rules of logic itself, resources consumed by use, and the boundary reappeared as the ! modality.

The boundary does not dissolve when you climb above it, and it does not dissolve when you change the rules of the game entirely.

---

## Structural Properties

The two-sorted system has been verified to satisfy:

- **Monad laws**, Origin|Bounded is a proper monad
- **Initial algebra**, the universal absorbing construction
- **Functoriality**, morphisms compose, identity works
- **Congruence**, sort equivalence respects all operations
- **Conservativity**, adds nothing within B
- **Decidability**, every equation is mechanically resolvable
- **Uniqueness**, no alternative decomposition works
- **No intermediate sorts**, can't add a third
- **Origin uniqueness**, exactly one absorber exists
- **Density**, B is closed, no gaps
- **Stability**, under products, coproducts, quotients, and embeddings

Every claim formally verified. [260 theorems, zero errors, zero `sorry`s.](PROOFS.md)

---

## This Isn't New

The ground/container/contents distinction has been seen before, across philosophy, mathematics, and contemplative traditions. 

**George Spencer-Brown,*Laws of Form* (1969).** He starts with the void, unmarked space, and says the first act is "draw a distinction." The mark and the unmarked co-emerge. His entire calculus is built on one act: distinction from the void. That's ground → container → contents. He wrote: *"A universe comes into being when a space is severed."* That's step 2.

**Heidegger, the ontological difference.** Being (Sein) vs beings (Seiendes). Being is the ground that makes beings possible but isn't itself a being. That's 𝒪. He spent his whole career saying philosophy forgot the ground.

**Zen Buddhism, pointing at the moon.** The finger pointing at the moon is not the moon. The symbol pointing at the ground is not the ground. The impossibility of containing 𝒪 in a symbol is the oldest observation in this tradition.

**Plotinus, The One.** Beyond being, beyond number. Everything emanates from it but it can't be captured by what comes from it.

**Peirce, Firstness.** Quality before distinction. The raw undifferentiated ground before categories.

**The Isha Upanishad.** *"That is whole. This is whole. From wholeness comes wholeness. When wholeness is taken from wholeness, wholeness remains."* That's 𝒪 ÷ 𝒪 = 𝒪, written down millennia before formal mathematics existed.

Obviously the insight isn't new.

---

## The Test

We formalized the theory in [Lean 4](lean/), a proof assistant that accepts or rejects proofs mechanically. The machine doesn't care how clever you sound. Either the types check or they don't.

- [260 theorems](PROOFS.md). Zero errors. Zero `sorry`s.
- 17 domains tested as modeled. 136 pairwise boundary preservations verified.
- Built prototypes in [TypeScript](packages/typescript/src/index.ts) and [Python](packages/python/src/two_sorted/__init__.py). 71% fewer branches. 10% faster in JavaScript.
- Built a [Rust core](packages/rust-python/src/lib.rs). Measured [actual energy consumption](packages/rust-python/energy_benchmark.py) on Apple Silicon. 98.6% less energy per operation.
- Within Rust, tested our approach against Rust's native `Option<T>`. Option won. The answer was already there.

Every test must pass because a failure would mean we changed the math instead of clarifying it.

Every test passed.

The 260 theorems verify how the boundary behaves. The law, you can't have a part without a whole, is why the boundary is there. 

---

## The Conclusion

We built this theory to reduce water consumption in AI. We formalized it, proved it, prototyped it, and benchmarked it. Rust's `Option<T>` beat us, born from ML's `option` type in 1973. The theory explains *why*, collapsing Origin and Bounded into a single symbol forces null checks that Option types eliminate at the type level. The [energy benchmarks](packages/rust-python/energy_benchmark.py) measure *how much* that efficiency matters in practice: 98.6% less energy per operation (Rust vs Python, not the theory alone).

For computation, the call to action is clear: move AI inference pipelines from Python to Rust. The theory is here. The proof is here. The measurements are here. The rest is engineering.

But `Option<T>` solved computation. It didn't unify it with math, logic, or physics. Those three fields are still running hundreds of separate functions for the same boundary. The unification, the base class that connects all four fields, is what this proposal is. What would happen if all four fields stopped running siloed boundary patches?

---

*"That is whole. This is whole. From wholeness comes wholeness."*
— Isha Upanishad
