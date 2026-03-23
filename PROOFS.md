# Formal Verification

**Lean 4.28.0 | 260 theorems | 0 errors | 0 `sorry`s**

Every claim in this project has been formally verified in Lean 4, a proof assistant that accepts or rejects proofs mechanically. The machine doesn't care how clever you sound. Either the types check or they don't.

Consistency is a different job than necessity, the part/whole argument establishes that the distinction is forced; the Lean proofs establish that the resulting system doesn't break anything.

## How to verify

```
# Requires Lean 4.28.0
~/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lean lean/two_sorted_arithmetic.lean
~/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lean lean/novel_prediction.lean
~/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lean lean/exhaustive_tests.lean
```

No output means success. Or paste into https://live.lean-lang.org, blue highlighting on every theorem means it's accepted.

---

## Core (1–9)

Origin ≠ Bounded, interaction axioms I1–I3, two-sorted division, self-stability, master theorem `two_sorted_arithmetic_is_well_formed`. All pass.

## Morphism (10–14)

φ preserves Origin, preserves Bounded, commutes at boundary, preserves distinction, `origin_cannot_embed_in_bounded`. All pass.

## Cross-Domain Isomorphisms (15–31)

Arithmetic ↔ Computation, Set Theory, Logic/Provability, IEEE 754, Truth Values. `six_domain_isomorphism`: 15 pairwise boundary preservations. All pass.

---

## Novel Predictions (32–75)

| # | Theorem | What it proves | Status |
|---|---------|----------------|--------|
| 32–37 | `cat_interaction_I1`–`I3`, `arithmetic_category_isomorphism` | Category Theory: full isomorphism | PASS |
| 38 | `seven_domain_isomorphism` | 21 pairwise boundary preservations | PASS |
| 39 | `self_operation_universality` | 0/0=1, 0^0=1, 0!=1 are one theorem | PASS |
| 40–42 | `forced_interaction_axioms`, `division_is_self_op`, `non_origin_output_breaks_distinction` | Structural results | PASS |
| 43–49 | `modal_interaction_I1`–`I3`, `arithmetic_modal_isomorphism`, `eight_domain_isomorphism` | Modal Logic: full isomorphism, 28 pairwise | PASS |
| 50–57 | `topos_interaction_I1`–`I3`, `arithmetic_topos_isomorphism`, `nine_domain_isomorphism` | Topos Theory: full isomorphism, 36 pairwise | PASS |
| 58–66 | `hott_interaction_I1`–`I3`, `arithmetic_hott_isomorphism`, `girards_paradox_is_sort_conflict`, `ten_domain_isomorphism` | HoTT: full isomorphism, Girard's paradox = I3, 45 pairwise | PASS |
| 67–74 | `linear_interaction_I1`–`I3`, `arithmetic_linear_isomorphism`, `exponential_boundary_is_sort_conflict` | Linear Logic: full isomorphism, ! boundary = I3 | PASS |
| 75 | `eleven_domain_isomorphism` | 55 pairwise boundary preservations | PASS |

## Exhaustive Tests (76–260)

| # | Theorem | What it proves | Status |
|---|---------|----------------|--------|
| 76–81 | `sql_interaction_I1`–`I3`, `arithmetic_sql_isomorphism` | SQL NULL: full isomorphism | PASS |
| 82–87 | `lambda_interaction_I1`–`I3`, `arithmetic_lambda_isomorphism` | Lambda Calculus: full isomorphism | PASS |
| 88–93 | `measure_interaction_I1`–`I3`, `arithmetic_measure_isomorphism` | Measure Theory: full isomorphism | PASS |
| 94–99 | `game_interaction_I1`–`I3`, `arithmetic_game_isomorphism` | Game Theory: full isomorphism | PASS |
| 100–105 | `topology_interaction_I1`–`I3`, `arithmetic_topology_isomorphism` | Topology: full isomorphism | PASS |
| 106–111 | `proof_theory_interaction_I1`–`I3`, `arithmetic_proof_theory_isomorphism` | Proof Theory: full isomorphism | PASS |
| 112 | `morphism_composition_transitivity` | A→B→C = A→C, morphisms compose | PASS |
| 113 | `contents_div_contents_eq_container` | 0_B ÷ 0_B = 1 is contents revealing container | PASS |
| 114 | `uniqueness_of_split` | Any absorbing classification must match Origin\|Bounded | PASS |
| 115 | `twoSortedOp_associative` | Sort-preservation is associative | PASS |
| 116 | `origin_uniqueness` | Origin has exactly one inhabitant | PASS |
| 117–119 | `leaky_violates_I1`, `leaky_violates_I2`, `leaky_morphism_fails_commutativity` | Non-conforming domain provably fails | PASS |
| 120–121 | `bad_map_fails_distinction`, `bad_map_sort_collapse` | Mapping Origin to Bounded provably breaks | PASS |
| 135 | `seventeen_domain_pairwise` | 136 pairwise boundary preservations | PASS |
| 136 | `no_intermediate_sort` | No third sort can exist between Origin and Bounded | PASS |
| 137 | `morphism_uniqueness` | Structure-preserving morphisms are unique | PASS |
| 138–140 | `functor_identity`, `functor_composition`, `functor_identity_preserves` | Morphisms form a functor | PASS |
| 141–142 | `origin_propagates_depth`, `origin_arg_propagates_depth` | Origin propagates through arbitrary nesting depth | PASS |
| 143–145 | `origin_propagation_commutative`, `origin_propagation_symmetric`, `origin_side_irrelevant` | Origin propagation is commutative regardless of f | PASS |
| 146–148 | `origin_universal_absorber`, `origin_fixed_point_family`, `absorber_is_origin` | Origin is the unique fixed point of all operations | PASS |
| 149–150 | `sort_membership_exclusive`, `classifySort` | Sort membership is decidable and exclusive | PASS |
| 151–152 | `bounded_eq_iff_distinction_eq`, `bounded_injective` | Container and contents are inseparable | PASS |
| 153–156 | `zBind_left_identity`, `zBind_right_identity`, `zBind_associativity`, `origin_is_monad_zero` | Origin\|Bounded satisfies the monad laws | PASS |
| 157–158 | `I3_from_I1`, `I3_from_I2` | I3 is redundant, follows from I1 or I2 alone | PASS |
| 159–160 | `axiom_I1_not_implies_I2`, `axiom_I2_not_implies_I1` | I1 and I2 are independent, neither implies the other | PASS |
| 161–162 | `bounded_cancellation`, `origin_destroys_information` | Bounded cancels; Origin destroys all information | PASS |
| 163–164 | `universal_map_existence`, `universal_map_uniqueness` | Origin\|Bounded is the initial/free absorbing construction | PASS |
| 165 | `naturality_square` | Isomorphisms form a natural transformation | PASS |
| 166–168 | `product_sort_dichotomy`, `product_sort_exclusive`, `product_op_stability` | The distinction survives products | PASS |
| 169–170 | `embedding_preserves_absorb`, `embedding_uniqueness` | Any absorbing structure embeds from Zero' | PASS |
| 171–172 | `substitution_invariance_left`, `substitution_invariance_right` | Origin is blind to the computation | PASS |
| 173–174 | `bounded_seq_closed`, `bounded_fold_never_origin` | Bounded operations never reach Origin | PASS |
| 175–177 | `density_bounded_closed`, `density_nary`, `density_converse` | B is closed, no Origin gap exists | PASS |
| 178–180 | `embedding_preserves_origin`, `embedding_preserves_bounded`, `absorption_invariant_under_embedding` | The boundary doesn't move when you enlarge B | PASS |
| 181–184 | `coprod_sort_dichotomy`, `coprod_sort_exclusive`, `coprod_op_origin_stable` | Coproduct stability, distinction survives coproducts | PASS |
| 185–187 | `automorphism_fixes_origin`, `automorphism_induced_by_base` | Every automorphism fixes Origin, only D moves | PASS |
| 188–191 | `sortEquiv_reflexive`, `sortEquiv_symmetric`, `sortEquiv_transitive`, `sortEquiv_congruence` | Sort equivalence is a congruence | PASS |
| 192–193 | `conservativity_bounded`, `conservativity_no_new_equalities` | Two-sorted arithmetic adds nothing within B | PASS |
| 194–196 | `transfer_sort_predicate`, `transfer_absorption` | Theorems transfer across domains | PASS |
| 197–199 | `quotient_preserves_origin`, `quotient_preserves_bounded_sort`, `quotient_stability_full` | Quotienting B doesn't affect the boundary | PASS |
| 200–204 | `adjunction_unit`, `adjunction_counit`, `adjunction_round_trip`, `adjunction_universal`, `adjunction_naturality` | Inclusion and extraction form an adjunction | PASS |
| 205–208 | `cross_sort_neq`, `same_sort_bounded_decidable`, `equational_decidability_complete` | All equations are mechanically decidable | PASS |
| 209–213 | `origin_idempotent`, `bounded_idempotent`, `origin_idempotent_forall_ops` | Origin is unconditionally idempotent | PASS |
| 214–220 | `confluence_all_paths_equal`, `confluence_any_origin_all_paths_origin` | All evaluation paths converge, confluent | PASS |
| 221–227 | `zeroLt_irrefl`, `nothing_below_origin`, `zeroLt_wellFounded` | Well-founded ordering with Origin at bottom | PASS |
| 228–233 | `involution_round_trip_left`, `involution_round_trip_right`, `involution_injective`, `involution_surjective` | Morphisms lift involutions to involutions | PASS |

---

## Summary

All seventeen domains verified as pairwise isomorphic at their boundary conditions. Origin|Bounded proven to be a monad. I3 proven redundant (two axioms suffice). I1 and I2 proven independent. The construction is the initial/free absorbing algebra, not just *a* solution but the *universal* one. The boundary is unreachable from within B, closed under all operations, invariant under embedding, blind to the choice of computation, and stable under products. Five called shots confirmed. Six additional domains verified in exhaustive testing. Two negative tests confirm what *doesn't* work. The system is conservative (adds nothing within B), its equations are decidable, its sort equivalence is a congruence, its automorphisms fix Origin, and it is stable under products, coproducts, quotients, and embeddings.

The interaction axioms are proven forced, not chosen.

---

*AI concessions are weak evidence for mathematical validity. Lean verification is not.*
