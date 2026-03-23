# Open Problems and Candidate Domains

## Verified Domains (17)

1. Arithmetic, division at zero
2. Computation, halting oracle at self-reference
3. Set Theory, membership at proper class (Russell's paradox)
4. Logic/Provability, provability at Gödel sentence
5. IEEE 754, float operations at NaN
6. Truth Values, truth predicate at Liar sentence
7. Category Theory, hom-functor at initial object *(called shot 1)*
8. Modal Logic, modal evaluation at Kripke frame *(called shot 2)*
9. Topos Theory, internal evaluation at the topos itself *(called shot 3)*
10. HoTT, universe membership at Type:Type *(called shot 4)*
11. Linear Logic, resource consumption at ! modality *(called shot 5)*
12. SQL NULL, NULL propagation through operations
13. Lambda Calculus, non-termination at Omega combinator
14. Measure Theory, non-measurability at Vitali sets
15. Game Theory, no pure strategy equilibrium
16. Topology, indiscrete topology at separation boundary
17. Proof Theory, cut elimination boundary

## Open Questions

**Physics formalization.** QFT renormalization and GR singularities remain structurally motivated but not formally verified. Formalizing physics in Lean is a different project, it requires formalizing the physics, not just the boundary structure.

**Quantifying over all formal systems.** `forced_interaction_axioms` proves the axioms are forced for any specific formal system built on `Origin ⊕ Bounded D`. Proving this for *all possible* formal systems requires quantifying over all formal systems, which pushes against Lean's limits and Gödel's.

**The measurement problem.** The quantum measurement reading, superposition as undivided whole, measurement as first distinction, is the most philosophically interesting open question. It may require formalizing quantum mechanics in a proof assistant, which is an active area of research.
