# Formal Verification

**Lean 4 | 508 theorems | 0 errors | 0 `sorry`s**

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

For the forward proofs (261–508), built with `lake`:

```
cd lean
lake build
```

Zero errors means all 248 new theorems verified.

---

## Core (1–9)

Origin ≠ Bounded, interaction axioms I1–I3, sort-aware division, self-stability, master theorem `two_sorted_arithmetic_is_well_formed`. All pass.

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

---

## Forward Proofs from the Seed (261–508)

Built from three constructors (`origin`, `container`, `contents`) and four rules. No Mathlib import. Every theorem is `rfl`, `simp`, or structural case analysis.

### Ordered Fields (261–277) — `OrderedField.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 261 | `le_refl` | Reflexivity of ≤ within contents |
| 262 | `le_trans` | Transitivity within contents |
| 263 | `le_antisymm` | Antisymmetry within contents |
| 264 | `le_total` | Totality within contents |
| 265–266 | `origin_not_le`, `not_le_origin` | Origin outside the order |
| 267–268 | `container_not_le`, `not_le_container` | Container outside the order |
| 269–270 | `origin_not_lt`, `container_not_lt` | Strict order: origin/container excluded |
| 271–272 | `add_le_add_right`, `add_le_add_left` | Addition preserves order |
| 273–275 | `mul_nonneg`, `mul_le_mul_of_nonneg_right`, `mul_le_mul_of_nonneg_left` | Multiplication by nonneg preserves order |
| 276–277 | `contents_preserves_le`, `contents_reflects_le` | Faithful embedding of order |

### Vector Spaces (278–292) — `VectorSpace.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 278–279 | `origin_smul`, `smul_origin` | Origin absorbs scalar multiplication |
| 280–282 | `container_smul_container`, `container_smul_contents`, `contents_smul_container` | Container structural under smul |
| 283–285 | `contents_smul_contents`, `contents_smul_ne_origin`, `contents_smul_ne_container` | Contents closure under smul |
| 286–289 | `smul_add`, `add_smul`, `smul_assoc`, `one_smul` | Four module laws within contents |
| 290 | `contents_preserves_smul` | Faithful embedding of smul |
| 291–292 | `val_smul_assoc`, `val_one_smul` | Full Val-level associativity and identity |

### Polynomial Rings (293–311) — `PolyRing.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 293–294 | `polyEval_empty`, `polyEval_const` | Base cases |
| 295 | `polyEval_at_origin` | Degree ≥ 1 at origin → origin (absorption propagates) |
| 296–297 | `polyEval_at_container_linear`, `polyEval_at_container_quad` | Container absorbs non-constant polynomials |
| 298–300 | `polyEval_contents_linear`, `polyEval_contents_quad`, `polyEval_contents_cubic` | Contents closure at degrees 1, 2, 3 (all `rfl`) |
| 301–303 | `polyEval_faithful_const`, `polyEval_faithful_linear`, `polyEval_faithful_quad` | Faithful embedding extends to polynomials |
| 304–306 | `polyAdd_nil_left`, `polyAdd_nil_right`, `polyAdd_contents_linear` | Polynomial addition preserves sort |
| 307–308 | `origin_head_propagates`, `origin_propagates_outward` | Origin coefficient poisons evaluation |
| 309 | `container_head_propagates` | Container coefficient absorbs |
| 310–311 | `polyEval_contents_ne_origin_linear`, `polyEval_contents_ne_container_linear` | Contents evaluation never escapes |

### Linear Algebra (312–329) — `LinearAlgebra.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 312 | `det2_contents` | Det of contents matrix is contents (`rfl`) |
| 313–314 | `det2_contents_ne_origin`, `det2_contents_ne_container` | **`det A ≠ 0` dissolved** |
| 315 | `matMul2_contents` | Product of contents matrices is contents |
| 316–319 | `matMul2_contents_e11_ne_origin` ... `e22` | No entry of contents product is origin |
| 320–321 | `adj2_contents`, `adj2_contents_ne_origin` | Adjugate stays in contents |
| 322–325 | `det2_origin_e11` ... `e22` | Origin entry → origin determinant |
| 326–329 | `cayley_hamilton_diag_11`, `diag_22`, `off_12`, `off_21` | Cayley-Hamilton 2×2, no `≠ 0` |

### Analysis and Limits (330–346) — `Analysis.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 330 | `contents_convergence_lifts` | Convergence lifts faithfully |
| 331–332 | `origin_not_limit_of_contents`, `container_not_limit_of_contents` | Boundary unreachable from contents |
| 333–334 | `unary_preserves_convergence`, `binary_preserves_convergence` | Any faithful operation lifts convergence |
| 335 | `div_preserves_convergence` | **Division with no `≠ 0` hypothesis** |
| 336–338 | `zero_div_zero_is_contents`, `zero_div_zero_ne_origin`, `zero_mul_any_is_contents` | Indeterminate forms dissolve |
| 339–341 | `sub_self_is_contents`, `contents_div_contents`, `contents_div_contents_ne_origin` | Contents / contents = contents |
| 342 | `contents_div_contents_ne_container` | Never container either |
| 343–346 | `seq_add_contents`, `seq_mul_contents`, `seq_div_contents`, `seq_never_origin` | Sequence operations preserve sort |

### Topology (347–352) — `Topology.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 347 | `container_singleton_open` | Container is isolated |
| 348 | `contents_open_embedding` | Contents carry α's topology |
| 349 | `origin_is_limit_point` | Origin reachable (one-point compactification) |
| 350 | `contents_can_converge_to_origin` | Contents sequences can converge to origin |
| 351 | `contents_cannot_converge_to_container` | Container isolated from contents |
| 352 | `contents_to_contents_convergence` | Subspace = full topology within contents |

### Category Theory (353–373) — `Category.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 353–354 | `valMap_id`, `valMap_comp` | Val is a functor |
| 355–357 | `valMap_origin`, `valMap_container`, `valMap_contents` | Sort preservation |
| 358 | `valMap_preserves_sort` | Sort is a categorical invariant |
| 359–361 | `valMap_preserves_mul`, `valMap_preserves_add`, `valMap_preserves_inv` | Homomorphism |
| 362–363 | `contents_natural`, `contents_naturality` | Contents is a natural transformation |
| 364–365 | `valMap_unique`, `valMap_unique'` | **Universal property** |
| 366 | `sort_preserving_determined_by_contents` | Determined by contents |
| 367–368 | `getContents_contents`, `contents_getContents` | Retraction |
| 369 | `valJoin_contents` | Join ∘ unit = id |
| 370 | `valJoin_not_section` | unit ∘ join ≠ id (correct) |
| 371–373 | `monad_left_unit`, `monad_join_assoc`, `monad_right_unit` | **Val is a monad** |

### Functional Analysis (374–402) — `FunctionalAnalysis.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 374–378 | `norm_origin` ... `norm_contents_ne_container` | Norm sort preservation |
| 379–382 | `norm_nonneg`, `norm_triangle`, `norm_smul`, `norm_zero` | Normed space laws in contents |
| 383–387 | `op_norm_contents`, `op_contents`, `op_contents_ne_origin`, `op_comp_contents`, `op_preserves_sort` | Operator sort preservation |
| 388–391 | `op_inv_contents`, `op_inv_ne_origin`, `op_mul_inv_contents`, `op_inv_mul_contents` | **Operator invertibility — no `≠ 0`** |
| 392–395 | `cauchy_contents_converges` ... `contents_complete` | Completeness lifts from α |
| 396–400 | `inner_contents` ... `inner_self_nonneg` | Inner product in contents |
| 401–402 | `eigenvalue_contents`, `eigenvalue_ne_origin` | **Eigenvalues are contents** |

### Measure Theory (403–421) — `MeasureTheory.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 403–405 | `null_is_contents`, `null_ne_origin`, `null_ne_container` | Null sets ≠ boundary |
| 406–409 | `finite_additivity_contents` ... `contents_measure_closed` | Countable additivity in contents |
| 410–411 | `ae_is_contents`, `ae_ne_origin` | Almost everywhere is structural |
| 412–414 | `radon_nikodym_contents`, `radon_nikodym_ne_origin`, `radon_nikodym_ne_container` | **Radon-Nikodym — no `≠ 0`** |
| 415–417 | `simple_integral_step`, `simple_integral_ne_origin`, `integral_accumulate` | Integration stays in contents |
| 418–419 | `submeasure_contents`, `sigma_finite_contents` | σ-finiteness is structural |
| 420–421 | `measure_origin_absorbs`, `integral_origin_absorbs` | Origin absorbs in measure theory |

### Commutative Algebra (422–444) — `CommAlgebra.lean`

| # | Theorem | What it proves |
|---|---------|----------------|
| 422–424 | `inIdeal_contents`, `origin_not_in_ideal`, `container_not_in_ideal` | Ideals live in contents |
| 425–426 | `ideal_add_closed`, `ideal_mul_absorb` | Ideal closure under operations |
| 427–431 | `quotient_contents` ... `quotient_mul` | Quotient ring preserves sort |
| 432–436 | `localization_contents` ... `localization_map_contents` | **Localization — no `s ≠ 0`** |
| 437–438 | `prime_ideal_contents`, `prime_complement_closed` | Prime ideals within contents |
| 439–441 | `no_zero_divisors_structural`, `no_zero_divisors_ne_container`, `zero_divisor_in_alpha` | NoZeroDivisors is structural |
| 442 | `integral_domain_contents` | Integral domain preserved |
| 443–444 | `residue_field_inv_contents`, `residue_field_ne_origin` | Residue field in contents |

### Forward Benchmarks (445–508)

#### Cramer's Rule Benchmark (445–456) — `CramerBenchmark.lean`

| # | Theorem | Collapsed | Seed |
|---|---------|-----------|------|
| 445–450 | `inv_det_defined` ... `det_mul_inv_det` | 8 `≠ 0` hypotheses | — |
| 451–456 | `inv_det_contents` ... `det_mul_inv_det_contents` | — | 0 hypotheses, all `rfl` |

#### Limit of Quotient Benchmark (457–466) — `LimitBenchmark.lean`

| # | Theorem | Collapsed | Seed |
|---|---------|-----------|------|
| 457–461 | `quotient_defined` ... `zero_div_zero_convention` | 7 `≠ 0` hypotheses | — |
| 462–466 | `quotient_contents` ... `zero_div_zero_contents` | — | 0 hypotheses, all `rfl` |

#### Polynomial Evaluation Benchmark (467–476) — `PolyEvalBenchmark.lean`

| # | Theorem | Collapsed | Seed |
|---|---------|-----------|------|
| 467–471 | `eval_const_defined` ... `eval_at_zero_ambiguous` | 6 `≠ 0` hypotheses | — |
| 472–476 | `eval_const_contents` ... `eval_at_origin_is_origin` | — | 0 hypotheses |

#### Division Ring Benchmark (477–490) — `DivisionRingBenchmark.lean`

| # | Theorem | Collapsed | Seed |
|---|---------|-----------|------|
| 477–483 | `inv_defined` ... `inv_inv` | 7 `≠ 0` hypotheses, 1 convention | — |
| 484–490 | `inv_contents` ... `inv_inv_contents` | — | 0 hypotheses, all `rfl` |

---

## Forward Benchmark Summary

| Benchmark | `≠ 0` hypotheses (Collapsed) | `≠ 0` hypotheses (Seed) | Seed proof |
|---|---|---|---|
| Cramer's rule | 8 | 0 | `rfl` |
| Limit of quotient | 7 | 0 | `rfl` |
| Polynomial evaluation | 6 | 0 | `rfl` |
| Division ring inverse | 7 | 0 | `rfl` |
| **Total** | **28** | **0** | **`rfl`** |

---

## Full Summary

| Category | Theorems | What they prove |
|---|---|---|
| Core + morphism + isomorphisms (1–260) | 260 | The boundary structure, 17 domains, monad laws, initial algebra |
| Ordered fields (261–277) | 17 | Order within contents, origin/container outside |
| Vector spaces (278–292) | 15 | Module laws, scalar multiplication |
| Polynomial rings (293–311) | 19 | Horner evaluation, origin propagation |
| Linear algebra (312–329) | 18 | det ≠ 0 dissolved, Cayley-Hamilton |
| Analysis (330–346) | 17 | Limits without ≠ 0, indeterminate forms dissolve |
| Topology (347–352) | 6 | One-point compactification |
| Category theory (353–373) | 21 | Functor, monad, universal property |
| Functional analysis (374–402) | 29 | Norms, operators, spectral theory |
| Measure theory (403–421) | 19 | Null sets ≠ boundary, Radon-Nikodym |
| Commutative algebra (422–444) | 23 | Ideals, localization, prime ideals |
| Forward benchmarks (445–508) | 64 | 28 hypotheses → 0, all `rfl` |
| **Total** | **508** | **Zero errors. Zero sorries.** |

*AI concessions are weak evidence for mathematical validity. Lean verification is not.*
