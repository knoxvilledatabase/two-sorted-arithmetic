# Called Shots

Five domains predicted by original arithmetic *before* Lean verification. All five confirmed. Zero failures.

| # | Domain | Prediction | Boundary maps to | Lean theorem | Date verified | Status |
|---|--------|-----------|-----------------|-------------|---------------|--------|
| 1 | Category Theory | Initial object plays Origin's role; hom-set at initial satisfies I1–I3 | `cat_interaction_I1`–`I3` | `arithmetic_category_isomorphism` | 2026-03-18 | PASS |
| 2 | Modal Logic | Kripke frame is 𝒪; possible worlds are B; modal evaluation at frame hits boundary | `modal_interaction_I1`–`I3` | `arithmetic_modal_isomorphism` | 2026-03-18 | PASS |
| 3 | Topos Theory | The topos itself is 𝒪; internal objects are B; topos cannot be its own object (Russell elevated) | `topos_interaction_I1`–`I3` | `arithmetic_topos_isomorphism` | 2026-03-18 | PASS |
| 4 | Homotopy Type Theory | Universe boundary is 𝒪; types within a universe are B; Type:Type is Girard's paradox = I3 | `hott_interaction_I1`–`I3` | `arithmetic_hott_isomorphism` | 2026-03-18 | PASS |
| 5 | Linear Logic | Exponential modality boundary is 𝒪; linear resources are B; ! promotion is the gate between B and 𝒪 | `linear_interaction_I1`–`I3` | `arithmetic_linear_isomorphism` | 2026-03-18 | PASS |

## The Girard Connection

Girard found 𝒪 twice:

- **1972**, Girard's paradox (`Type : Type` produces inconsistency in type theory)
- **1987**, Linear logic (the `!` modality marks the boundary between bounded and inexhaustible resources)

Both are the same sort conflict: `girards_paradox_is_sort_conflict` and `exponential_boundary_is_sort_conflict` reduce to `interaction_I3`. Original arithmetic connects what Girard himself didn't.

## Structural Results

| Theorem | What it proves |
|---------|----------------|
| `self_operation_universality` | `0/0=1`, `0^0=1`, `0!=1` are one theorem, not three conventions |
| `forced_interaction_axioms` | I1–I3 are the *only* distinction-preserving total extension, forced, not chosen |
| `contents_div_contents_eq_container` | 0_B ÷ 0_B = 1 is contents revealing the container |
| `morphism_composition_transitivity` | A→B→C = A→C, morphisms compose |
| `uniqueness_of_split` | Any absorbing classification must match Origin\|Bounded |
| `twoSortedOp_associative` | Sort-preservation is associative |
| `origin_uniqueness` | Origin has exactly one inhabitant |
| `no_intermediate_sort` | No third sort can exist, the split is the only granularity |
| `morphism_uniqueness` | Structure-preserving morphisms are unique |
| `functor_identity`, `functor_composition` | Morphisms form a functor (identity + composition) |
| `origin_propagates_depth` | Origin propagates through arbitrary nesting depth |
| `origin_propagation_commutative` | Origin propagation is commutative regardless of f |
| `origin_universal_absorber`, `absorber_is_origin` | Origin is the unique absorbing element |
| `sort_membership_exclusive` | Sort membership is decidable and exclusive |
| `bounded_injective` | Container and contents are inseparable |
| `I3_from_I1`, `I3_from_I2` | I3 is redundant, two axioms suffice |
| `axiom_I1_not_implies_I2` | I1 and I2 are independent |
| `zBind_left_identity`, `zBind_right_identity`, `zBind_associativity` | Origin\|Bounded is a monad |
| `universal_map_existence`, `universal_map_uniqueness` | The initial/free absorbing construction |
| `bounded_fold_never_origin` | Origin is unreachable from within B |
| `density_bounded_closed`, `density_converse` | B is closed, no Origin gap |
| `seventeen_domain_pairwise` | 136 pairwise boundary preservations across all seventeen domains |

## How to verify

```
# Requires Lean 4.28.0
lean lean/two_sorted_arithmetic.lean  # Core: 9 theorems
lean lean/novel_prediction.lean       # Novel predictions: 66 theorems
lean lean/exhaustive_tests.lean       # Exhaustive tests: 193 theorems
```

Or paste into https://live.lean-lang.org
