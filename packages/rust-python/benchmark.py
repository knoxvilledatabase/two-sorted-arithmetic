"""
Benchmark: Pure Python vs Rust — full pipeline, no boundary crossing.

Both implementations process the same financial records with missing values.
The Rust version uses NaN-as-Origin with hardware propagation.
The traditional Rust version uses explicit checks at every step.
"""

import time
import sys
sys.path.insert(0, "../python/src")

import two_sorted as py_ts
from two_sorted_rs import run_pipeline, run_pipeline_n, run_traditional_n

# ---------------------------------------------------------------------------
# Test data — financial records with missing values
# ---------------------------------------------------------------------------

records = [
    (1000.0, 600.0, 0.15),        # normal
    (5000.0, 3200.0, 0.20),       # normal
    (None, 400.0, 0.10),          # null revenue
    (0.0, 200.0, 0.15),           # zero revenue (div by zero)
    (2000.0, None, 0.12),         # null cost
    (800.0, 500.0, float("nan")), # NaN tax
    (None, None, None),           # all null
    (3000.0, 1800.0, 0.22),       # normal
    (750.0, 750.0, 0.10),         # zero profit margin
    (1500.0, 900.0, 0.18),        # normal
    (4000.0, 2500.0, 0.25),       # normal
    (None, 100.0, 0.05),          # null revenue
]

# ---------------------------------------------------------------------------
# Pure Python pipeline
# ---------------------------------------------------------------------------

def python_pipeline(records):
    results = []
    for rev_raw, cost_raw, tax_raw in records:
        rev = py_ts.from_nullable(rev_raw)
        cost = py_ts.from_nullable(cost_raw)
        tax = py_ts.from_nullable(tax_raw)

        if rev is py_ts.Origin or cost is py_ts.Origin or tax is py_ts.Origin:
            results.append(py_ts.Origin)
            continue
        if rev == 0:
            results.append(py_ts.Origin)
            continue

        margin = (rev - cost) / rev
        after_tax = margin * (1 - tax)
        results.append(after_tax)

    valid = [r for r in results if r is not py_ts.Origin]
    if not valid:
        return 0, 0.0, 0.0
    s = sum(valid)
    return len(valid), s, s / len(valid)

# ---------------------------------------------------------------------------
# Verify all three produce same results
# ---------------------------------------------------------------------------

py_count, py_sum, py_avg = python_pipeline(records)
rust_result = run_pipeline(records)
trad_result = run_traditional_n(records, 1)

print("=" * 70)
print("  RESULTS VERIFICATION")
print("=" * 70)
print(f"  Python:      count={py_count}, sum={py_sum:.4f}, avg={py_avg:.4f}")
print(f"  Rust (NaN):  count={rust_result.valid_count}, sum={rust_result.sum:.4f}, avg={rust_result.average:.4f}")
print(f"  Rust (trad): count={trad_result.valid_count}, sum={trad_result.sum:.4f}, avg={trad_result.average:.4f}")
print(f"  Match:       {'YES' if abs(py_avg - rust_result.average) < 1e-10 else 'NO'}")
print()

# ---------------------------------------------------------------------------
# Benchmark
# ---------------------------------------------------------------------------

ITERATIONS = 1_000_000

print("=" * 70)
print("  BENCHMARK")
print("=" * 70)
print(f"  Iterations:  {ITERATIONS:,} ({len(records)} records each = {ITERATIONS * len(records):,} total)")
print("-" * 70)

# Python
start = time.perf_counter()
for _ in range(ITERATIONS):
    python_pipeline(records)
py_time = time.perf_counter() - start
print(f"  Python:              {py_time * 1000:.1f}ms")

# Rust — full pipeline, NaN propagation, no Python callbacks
start = time.perf_counter()
run_pipeline_n(records, ITERATIONS)
rust_time = time.perf_counter() - start
print(f"  Rust (NaN-as-Origin):{rust_time * 1000:.1f}ms")

# Rust — traditional checks
start = time.perf_counter()
run_traditional_n(records, ITERATIONS)
trad_time = time.perf_counter() - start
print(f"  Rust (traditional):  {trad_time * 1000:.1f}ms")

print("-" * 70)

# Rust NaN vs Python
if rust_time < py_time:
    print(f"  Rust NaN vs Python:      {(1 - rust_time / py_time) * 100:.1f}% faster")
else:
    print(f"  Python vs Rust NaN:      {(1 - py_time / rust_time) * 100:.1f}% faster")

# Rust NaN vs Rust traditional
if rust_time < trad_time:
    print(f"  Rust NaN vs Rust trad:   {(1 - rust_time / trad_time) * 100:.1f}% faster")
else:
    print(f"  Rust trad vs Rust NaN:   {(1 - trad_time / rust_time) * 100:.1f}% faster")

# Rust traditional vs Python
if trad_time < py_time:
    print(f"  Rust trad vs Python:     {(1 - trad_time / py_time) * 100:.1f}% faster")

print("=" * 70)
