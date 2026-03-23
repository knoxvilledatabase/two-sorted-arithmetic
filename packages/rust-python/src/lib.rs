use pyo3::prelude::*;

/// Two-sorted arithmetic: Origin | Bounded — implemented in Rust.
/// One check instead of four. Fewer cycles. Less energy. Less heat. Less water.
#[pymodule]
mod two_sorted_rs {
    use super::*;

    /// A financial record with optional fields.
    #[pyclass]
    #[derive(Clone)]
    struct Record {
        revenue: f64,  // NaN = Origin
        cost: f64,     // NaN = Origin
        tax: f64,      // NaN = Origin
    }

    #[pymethods]
    impl Record {
        #[new]
        fn new(revenue: f64, cost: f64, tax: f64) -> Self {
            Record { revenue, cost, tax }
        }
    }

    /// Result of processing a pipeline.
    #[pyclass]
    #[derive(Clone)]
    struct PipelineResult {
        #[pyo3(get)]
        valid_count: usize,
        #[pyo3(get)]
        sum: f64,
        #[pyo3(get)]
        average: f64,
    }

    /// Convert an optional f64 to NaN-as-Origin.
    /// None → NaN. NaN stays NaN. Values pass through.
    #[pyfunction]
    fn to_origin(value: Option<f64>) -> f64 {
        match value {
            None => f64::NAN,
            Some(v) => v,
        }
    }

    /// Process a single record. All Origin checks are NaN propagation — zero branches.
    #[inline(always)]
    fn process_record(revenue: f64, cost: f64, tax: f64) -> f64 {
        // NaN propagates through all arithmetic automatically.
        // No if statements. No null checks. The CPU does I1-I3.
        let margin = (revenue - cost) / revenue;
        let after_tax = margin * (1.0 - tax);
        after_tax
    }

    /// Run the full pipeline in Rust. No Python callbacks. No boundary crossing.
    /// NaN-as-Origin propagates through hardware. One isFinite check at output.
    #[pyfunction]
    fn run_pipeline(records: Vec<(Option<f64>, Option<f64>, Option<f64>)>) -> PipelineResult {
        let mut sum = 0.0_f64;
        let mut count = 0_usize;

        for (rev, cost, tax) in &records {
            let r = rev.unwrap_or(f64::NAN);
            let c = cost.unwrap_or(f64::NAN);
            let t = tax.unwrap_or(f64::NAN);

            let result = process_record(r, c, t);

            if result.is_finite() {
                sum += result;
                count += 1;
            }
        }

        let average = if count == 0 { f64::NAN } else { sum / count as f64 };

        PipelineResult {
            valid_count: count,
            sum,
            average,
        }
    }

    /// Run the pipeline N times and return the result. For benchmarking.
    #[pyfunction]
    fn run_pipeline_n(records: Vec<(Option<f64>, Option<f64>, Option<f64>)>, iterations: usize) -> PipelineResult {
        let mut result = PipelineResult {
            valid_count: 0,
            sum: 0.0,
            average: 0.0,
        };

        for _ in 0..iterations {
            result = run_pipeline(records.clone());
        }

        result
    }

    /// Traditional pipeline with explicit null/NaN checks at every step.
    /// For comparison benchmarking.
    #[pyfunction]
    fn run_traditional_n(records: Vec<(Option<f64>, Option<f64>, Option<f64>)>, iterations: usize) -> PipelineResult {
        let mut result = PipelineResult {
            valid_count: 0,
            sum: 0.0,
            average: 0.0,
        };

        for _ in 0..iterations {
            let mut sum = 0.0_f64;
            let mut count = 0_usize;

            for (rev, cost, tax) in &records {
                // Traditional: check every value at every step
                let r = match rev {
                    Some(v) if !v.is_nan() => *v,
                    _ => continue,
                };
                let c = match cost {
                    Some(v) if !v.is_nan() => *v,
                    _ => continue,
                };
                let t = match tax {
                    Some(v) if !v.is_nan() => *v,
                    _ => continue,
                };

                if r == 0.0 { continue; } // division by zero guard

                let margin = (r - c) / r;
                if margin.is_nan() { continue; }

                let after_tax = margin * (1.0 - t);
                if after_tax.is_nan() || !after_tax.is_finite() { continue; }

                sum += after_tax;
                count += 1;
            }

            let average = if count == 0 { f64::NAN } else { sum / count as f64 };
            result = PipelineResult {
                valid_count: count,
                sum,
                average,
            };
        }

        result
    }

    // =====================================================================
    // Cross-boundary pipeline — simulates multiple service calls
    // This is where two-sorted (NaN propagation) should beat traditional
    // =====================================================================

    /// Simulate a service boundary — a function that validates, transforms,
    /// and returns. Each function is a separate "scope" that traditionally
    /// would need its own null checks.

    #[inline(never)]  // force function call overhead — simulate service boundary
    fn service_parse(rev: f64, cost: f64, tax: f64) -> (f64, f64, f64) {
        // NaN propagates — no checks needed
        (rev, cost, tax)
    }

    #[inline(never)]
    fn service_validate(rev: f64, cost: f64, tax: f64) -> (f64, f64, f64) {
        // NaN propagates — no checks needed
        (rev, cost, tax)
    }

    #[inline(never)]
    fn service_margin(rev: f64, cost: f64) -> f64 {
        // NaN propagates through division automatically
        (rev - cost) / rev
    }

    #[inline(never)]
    fn service_tax(margin: f64, tax: f64) -> f64 {
        // NaN propagates through multiplication automatically
        margin * (1.0 - tax)
    }

    #[inline(never)]
    fn service_scale(value: f64, factor: f64) -> f64 {
        value * factor
    }

    #[inline(never)]
    fn service_adjust(value: f64, offset: f64) -> f64 {
        value + offset
    }

    /// Cross-boundary pipeline: NaN propagation across 6 function boundaries.
    /// Zero checks in the middle. One isFinite at the output.
    #[pyfunction]
    fn run_cross_boundary_nan_n(records: Vec<(Option<f64>, Option<f64>, Option<f64>)>, iterations: usize) -> PipelineResult {
        let mut result = PipelineResult {
            valid_count: 0,
            sum: 0.0,
            average: 0.0,
        };

        for _ in 0..iterations {
            let mut sum = 0.0_f64;
            let mut count = 0_usize;

            for (rev, cost, tax) in &records {
                let r = rev.unwrap_or(f64::NAN);
                let c = cost.unwrap_or(f64::NAN);
                let t = tax.unwrap_or(f64::NAN);

                // 6 function boundaries — NaN propagates through all of them
                let (r2, c2, t2) = service_parse(r, c, t);
                let (r3, c3, t3) = service_validate(r2, c2, t2);
                let margin = service_margin(r3, c3);
                let after_tax = service_tax(margin, t3);
                let scaled = service_scale(after_tax, 100.0);
                let adjusted = service_adjust(scaled, -10.0);

                // One check at the output boundary
                if adjusted.is_finite() {
                    sum += adjusted;
                    count += 1;
                }
            }

            let average = if count == 0 { f64::NAN } else { sum / count as f64 };
            result = PipelineResult {
                valid_count: count,
                sum,
                average,
            };
        }

        result
    }

    // Traditional cross-boundary: each function checks for invalid input

    #[inline(never)]
    fn service_parse_trad(rev: f64, cost: f64, tax: f64) -> Option<(f64, f64, f64)> {
        if rev.is_nan() || cost.is_nan() || tax.is_nan() { return None; }
        Some((rev, cost, tax))
    }

    #[inline(never)]
    fn service_validate_trad(rev: f64, cost: f64, tax: f64) -> Option<(f64, f64, f64)> {
        if rev.is_nan() || cost.is_nan() || tax.is_nan() { return None; }
        if rev == 0.0 { return None; }
        Some((rev, cost, tax))
    }

    #[inline(never)]
    fn service_margin_trad(rev: f64, cost: f64) -> Option<f64> {
        if rev.is_nan() || cost.is_nan() || rev == 0.0 { return None; }
        let m = (rev - cost) / rev;
        if m.is_nan() { return None; }
        Some(m)
    }

    #[inline(never)]
    fn service_tax_trad(margin: f64, tax: f64) -> Option<f64> {
        if margin.is_nan() || tax.is_nan() { return None; }
        let r = margin * (1.0 - tax);
        if r.is_nan() { return None; }
        Some(r)
    }

    #[inline(never)]
    fn service_scale_trad(value: f64, factor: f64) -> Option<f64> {
        if value.is_nan() || !value.is_finite() { return None; }
        Some(value * factor)
    }

    #[inline(never)]
    fn service_adjust_trad(value: f64, offset: f64) -> Option<f64> {
        if value.is_nan() || !value.is_finite() { return None; }
        Some(value + offset)
    }

    /// Cross-boundary pipeline: traditional checks at every function boundary.
    /// Each function independently validates its inputs.
    #[pyfunction]
    fn run_cross_boundary_trad_n(records: Vec<(Option<f64>, Option<f64>, Option<f64>)>, iterations: usize) -> PipelineResult {
        let mut result = PipelineResult {
            valid_count: 0,
            sum: 0.0,
            average: 0.0,
        };

        for _ in 0..iterations {
            let mut sum = 0.0_f64;
            let mut count = 0_usize;

            for (rev, cost, tax) in &records {
                let r = match rev { Some(v) => *v, None => continue };
                let c = match cost { Some(v) => *v, None => continue };
                let t = match tax { Some(v) => *v, None => continue };

                let (r2, c2, t2) = match service_parse_trad(r, c, t) {
                    Some(v) => v, None => continue
                };
                let (r3, c3, t3) = match service_validate_trad(r2, c2, t2) {
                    Some(v) => v, None => continue
                };
                let margin = match service_margin_trad(r3, c3) {
                    Some(v) => v, None => continue
                };
                let after_tax = match service_tax_trad(margin, t3) {
                    Some(v) => v, None => continue
                };
                let scaled = match service_scale_trad(after_tax, 100.0) {
                    Some(v) => v, None => continue
                };
                let adjusted = match service_adjust_trad(scaled, -10.0) {
                    Some(v) => v, None => continue
                };

                sum += adjusted;
                count += 1;
            }

            let average = if count == 0 { f64::NAN } else { sum / count as f64 };
            result = PipelineResult {
                valid_count: count,
                sum,
                average,
            };
        }

        result
    }
}
