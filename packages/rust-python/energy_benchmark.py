"""
Energy benchmark: Measure actual power consumption.

Uses macOS powermetrics to measure CPU/GPU/ANE power in milliwatts.
Runs each workload for a fixed duration, captures power readings.

Must be run with: sudo .venv/bin/python energy_benchmark.py
"""

import subprocess
import time
import os
import sys
import re
import threading

sys.path.insert(0, "../python/src")
import two_sorted as py_ts
from two_sorted_rs import run_pipeline_n, run_traditional_n, run_cross_boundary_nan_n, run_cross_boundary_trad_n

# ---------------------------------------------------------------------------
# Test data
# ---------------------------------------------------------------------------

records = [
    (1000.0, 600.0, 0.15),
    (5000.0, 3200.0, 0.20),
    (None, 400.0, 0.10),
    (0.0, 200.0, 0.15),
    (2000.0, None, 0.12),
    (800.0, 500.0, float("nan")),
    (None, None, None),
    (3000.0, 1800.0, 0.22),
    (750.0, 750.0, 0.10),
    (1500.0, 900.0, 0.18),
    (4000.0, 2500.0, 0.25),
    (None, 100.0, 0.05),
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
# Power measurement
# ---------------------------------------------------------------------------

def measure_power_during(label, workload_fn, duration_seconds=5):
    """Run workload while capturing powermetrics output."""

    power_readings = []

    # Start powermetrics — text output, sample every 200ms
    pm = subprocess.Popen(
        ["powermetrics",
         "--samplers", "cpu_power",
         "-i", "200",
         "-n", str(duration_seconds * 5 + 2)],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True
    )

    # Collect output in a thread so it doesn't block
    output_lines = []
    def read_output():
        for line in pm.stdout:
            output_lines.append(line)
    reader = threading.Thread(target=read_output, daemon=True)
    reader.start()

    time.sleep(0.3)  # let powermetrics start

    # Run workload
    iterations = 0
    start = time.perf_counter()
    while time.perf_counter() - start < duration_seconds:
        workload_fn()
        iterations += 1
    elapsed = time.perf_counter() - start

    # Wait for powermetrics to finish
    pm.terminate()
    pm.wait()
    reader.join(timeout=2)

    # Parse power readings from output
    # Look for lines like "CPU Power: 1234 mW" or "Package Power: 1234 mW"
    # or "Combined Power (CPU + GPU + ANE): 1234 mW"
    for line in output_lines:
        # Try multiple patterns Apple Silicon uses
        for pattern in [
            r"CPU Power:\s+([\d.]+)\s*mW",
            r"Package Power:\s+([\d.]+)\s*mW",
            r"Combined Power.*?:\s+([\d.]+)\s*mW",
            r"ANE Power:\s+([\d.]+)\s*mW",
            r"GPU Power:\s+([\d.]+)\s*mW",
            r"E-Cluster Power:\s+([\d.]+)\s*mW",
            r"P-Cluster Power:\s+([\d.]+)\s*mW",
        ]:
            m = re.search(pattern, line)
            if m:
                power_readings.append((pattern.split(":")[0].replace(r"\s+", " "), float(m.group(1))))

    # Group by type
    power_by_type = {}
    for ptype, val in power_readings:
        ptype_clean = ptype.replace("\\", "").strip()
        if ptype_clean not in power_by_type:
            power_by_type[ptype_clean] = []
        power_by_type[ptype_clean].append(val)

    # Get average CPU/package power
    avg_power = 0
    power_label = ""
    for key in ["CPU Power", "Package Power", "Combined Power.*?"]:
        clean = key.replace("\\", "").replace(".*?", "").strip()
        for k, vals in power_by_type.items():
            if clean.lower() in k.lower() or k.lower() in clean.lower():
                avg_power = sum(vals) / len(vals)
                power_label = k
                break
        if avg_power > 0:
            break

    # If we still don't have power, just sum all readings
    if avg_power == 0 and power_readings:
        all_vals = [v for _, v in power_readings]
        avg_power = sum(all_vals) / len(all_vals)
        power_label = "all sensors"

    total_energy_mj = avg_power * elapsed  # mW * s = mJ

    return {
        "label": label,
        "iterations": iterations,
        "elapsed_s": elapsed,
        "avg_power_mw": avg_power,
        "power_label": power_label,
        "total_energy_mj": total_energy_mj,
        "energy_per_iter_uj": (total_energy_mj * 1000 / iterations) if iterations > 0 else 0,
        "power_types": {k: f"{sum(v)/len(v):.1f} mW ({len(v)} samples)" for k, v in power_by_type.items()},
        "raw_sample_count": len(power_readings),
    }

# ---------------------------------------------------------------------------
# Check for root
# ---------------------------------------------------------------------------

if os.geteuid() != 0:
    print("This benchmark requires root for powermetrics.")
    print("Run with: sudo .venv/bin/python energy_benchmark.py")
    sys.exit(1)

# ---------------------------------------------------------------------------
# Run benchmarks
# ---------------------------------------------------------------------------

DURATION = 5
RUST_BATCH = 10000

print()
print("=" * 70)
print("  ENERGY BENCHMARK — Actual power consumption")
print("  macOS powermetrics on Apple Silicon")
print("=" * 70)
print(f"  Duration: {DURATION}s per workload")
print(f"  Records:  {len(records)} per iteration")
print()

# Idle baseline
print("  Measuring idle baseline...")
idle = measure_power_during("Idle", lambda: time.sleep(0.01), DURATION)

print("  Measuring Python...")
py = measure_power_during("Python", lambda: python_pipeline(records), DURATION)

print("  Measuring Rust (NaN-as-Origin)...")
rn = measure_power_during("Rust NaN", lambda: run_pipeline_n(records, RUST_BATCH), DURATION)
rn["iterations"] *= RUST_BATCH

print("  Measuring Rust (traditional)...")
rt = measure_power_during("Rust trad", lambda: run_traditional_n(records, RUST_BATCH), DURATION)
rt["iterations"] *= RUST_BATCH

print("  Measuring Rust cross-boundary (NaN propagation)...")
cn = measure_power_during("Cross NaN", lambda: run_cross_boundary_nan_n(records, RUST_BATCH), DURATION)
cn["iterations"] *= RUST_BATCH

print("  Measuring Rust cross-boundary (traditional checks)...")
ct = measure_power_during("Cross trad", lambda: run_cross_boundary_trad_n(records, RUST_BATCH), DURATION)
ct["iterations"] *= RUST_BATCH

print()

# Show power types detected
print("  Power sensors detected:")
for ptype, info in (idle.get("power_types", {}) or py.get("power_types", {})).items():
    print(f"    {ptype}: {info}")
print()

# Recalculate energy per iteration with correct iteration counts
py_uj = (py['total_energy_mj'] * 1000 / py['iterations']) if py['iterations'] > 0 else 0
rn_uj = (rn['total_energy_mj'] * 1000 / rn['iterations']) if rn['iterations'] > 0 else 0
rt_uj = (rt['total_energy_mj'] * 1000 / rt['iterations']) if rt['iterations'] > 0 else 0
cn_uj = (cn['total_energy_mj'] * 1000 / cn['iterations']) if cn['iterations'] > 0 else 0
ct_uj = (ct['total_energy_mj'] * 1000 / ct['iterations']) if ct['iterations'] > 0 else 0

print()
print("  TIGHT LOOP (single scope — early exit vs propagation)")
print("-" * 70)
print(f"  {'':30s} {'Idle':>10s} {'Python':>10s} {'Rust NaN':>10s} {'Rust trad':>10s}")
print("-" * 70)
print(f"  {'Iterations':30s} {'—':>10s} {py['iterations']:>10,d} {rn['iterations']:>10,d} {rt['iterations']:>10,d}")
print(f"  {'Avg power (mW)':30s} {idle['avg_power_mw']:>10.1f} {py['avg_power_mw']:>10.1f} {rn['avg_power_mw']:>10.1f} {rt['avg_power_mw']:>10.1f}")
print(f"  {'Total energy (mJ)':30s} {idle['total_energy_mj']:>10.1f} {py['total_energy_mj']:>10.1f} {rn['total_energy_mj']:>10.1f} {rt['total_energy_mj']:>10.1f}")
print(f"  {'Energy per iter (µJ)':30s} {'—':>10s} {py_uj:>10.2f} {rn_uj:>10.4f} {rt_uj:>10.4f}")
print("-" * 70)

if rt_uj > 0 and rn_uj > 0:
    diff = (1 - rn_uj / rt_uj) * 100
    if diff > 0:
        print(f"  Tight loop: NaN propagation uses {diff:.1f}% less energy")
    else:
        print(f"  Tight loop: Traditional uses {-diff:.1f}% less energy (early exit wins)")

print()
print("  CROSS-BOUNDARY (6 function boundaries — guards vs propagation)")
print("-" * 70)
print(f"  {'':30s} {'Cross NaN':>10s} {'Cross trad':>10s}")
print("-" * 70)
print(f"  {'Iterations':30s} {cn['iterations']:>10,d} {ct['iterations']:>10,d}")
print(f"  {'Avg power (mW)':30s} {cn['avg_power_mw']:>10.1f} {ct['avg_power_mw']:>10.1f}")
print(f"  {'Total energy (mJ)':30s} {cn['total_energy_mj']:>10.1f} {ct['total_energy_mj']:>10.1f}")
print(f"  {'Energy per iter (µJ)':30s} {cn_uj:>10.4f} {ct_uj:>10.4f}")
print("-" * 70)

if ct_uj > 0 and cn_uj > 0:
    diff = (1 - cn_uj / ct_uj) * 100
    if diff > 0:
        print(f"  Cross-boundary: NaN propagation uses {diff:.1f}% less energy")
    else:
        print(f"  Cross-boundary: Traditional uses {-diff:.1f}% less energy")

print()
print("  SUMMARY")
print("-" * 70)
if py_uj > 0 and cn_uj > 0:
    print(f"  Python → Rust cross-boundary NaN: {(1 - cn_uj / py_uj) * 100:.1f}% less energy per op")

print("=" * 70)
print()
