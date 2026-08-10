use std::collections::HashSet;

use log::debug;

use program_structure::cfg::Cfg;
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::variable_meta::VariableMeta;
use program_structure::ir::*;
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;

use crate::taint_analysis::{run_taint_analysis, TaintAnalysis};

pub struct SignalDependentAssertWarning {
    reason: String,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl SignalDependentAssertWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::error(
            "Assert statements that depend on signals are not enforced by the circuit."
                .to_string(),
            ReportCode::SignalDependentAssert,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                format!("Signal-dependent assert ({})", self.reason),
            );
        }
        report.add_note(
            "Circom `assert` is checked only during witness generation. Use constraints (`===` / `<==`) to enforce properties of signals."
                .to_string(),
        );
        report
    }
}

/// Flag `assert(...)` statements whose condition depends on prover-controlled
/// values (signals or component outputs), either directly or through locals.
///
/// Template-parameter and compile-time constant asserts are allowed.
pub fn find_signal_dependent_asserts(cfg: &Cfg) -> ReportCollection {
    debug!("running signal-dependent assert analysis pass");
    let taint = run_taint_analysis(cfg);
    let signal_sources = collect_signal_sources(cfg);

    let mut reports = ReportCollection::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            if let Statement::Assert { meta, .. } = stmt {
                if let Some(reason) = signal_dependency_reason(stmt, &signal_sources, &taint) {
                    reports.push(build_report(meta, reason));
                }
            }
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

/// Collect prover-controlled values that can act as taint sources: plain
/// signals and component signal accesses. A read of a sub-component output
/// such as `c.out` is classified as a component read (keyed by `c`), not a
/// signal read, so component reads/writes must be included as sources.
fn collect_signal_sources(cfg: &Cfg) -> HashSet<VariableName> {
    let mut sources = HashSet::new();
    for basic_block in cfg.iter() {
        for statement in basic_block.iter() {
            for signal in statement.signals_read() {
                sources.insert(signal.name().clone());
            }
            for signal in statement.signals_written() {
                sources.insert(signal.name().clone());
            }
            for component in statement.components_read() {
                sources.insert(component.name().clone());
            }
            for component in statement.components_written() {
                sources.insert(component.name().clone());
            }
        }
    }
    sources
}

fn signal_dependency_reason(
    statement: &Statement,
    signal_sources: &HashSet<VariableName>,
    taint: &TaintAnalysis,
) -> Option<String> {
    let direct_signals = statement
        .signals_read()
        .iter()
        .map(|signal| signal.to_string())
        .collect::<Vec<_>>();
    if !direct_signals.is_empty() {
        return Some(format!("direct signal read: {}", direct_signals.join(", ")));
    }

    let direct_components = statement
        .components_read()
        .iter()
        .map(|component| component.to_string())
        .collect::<Vec<_>>();
    if !direct_components.is_empty() {
        return Some(format!(
            "direct component signal read: {}",
            direct_components.join(", ")
        ));
    }

    let local_reads = statement.locals_read().iter().collect::<Vec<_>>();
    for source in signal_sources {
        let tainted = taint.multi_step_taint(source);
        for local in &local_reads {
            if tainted.contains(local.name()) {
                return Some(format!(
                    "var `{}` depends on signal `{}` via dataflow",
                    local, source
                ));
            }
        }
    }

    None
}

fn build_report(meta: &Meta, reason: String) -> Report {
    SignalDependentAssertWarning {
        reason,
        file_id: meta.file_id(),
        file_location: meta.file_location(),
    }
    .into_report()
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::{cfg::IntoCfg, constants::Curve};

    use super::*;

    #[test]
    fn test_signal_dependent_asserts() {
        // Direct signal read in assert.
        let src = r#"
            template DirectSignalAssert(n) {
              signal input in;
              assert(in < n);
            }
        "#;
        validate_reports(src, 1);

        // Var assigned from a signal.
        let src = r#"
            template VarSignalAssert() {
              signal input in[2];
              var maskBit = in[0];
              assert(maskBit < 1);
            }
        "#;
        validate_reports(src, 1);

        // Transitive var dependence on a signal.
        let src = r#"
            template TransitiveVarSignalAssert() {
              signal input in;
              var first = in;
              var second = first + 1;
              assert(second != 0);
            }
        "#;
        validate_reports(src, 1);

        // Branch condition taints a local used in assert.
        let src = r#"
            template BranchTaintedVarAssert(n) {
              signal input in;
              var out = 0;
              if (in < n) {
                out = 1;
              }
              assert(out == 0 || out == 1);
            }
        "#;
        validate_reports(src, 1);

        // Parameter / compile-time asserts are fine.
        let src = r#"
            template ParamAsserts(nPlayers, n) {
              assert(n >= 5 && n <= 7);
              assert(nPlayers == 8 || nPlayers == 10 || nPlayers == 12);

              var maxCards = n * 2 + 5;
              assert(maxCards < 32);

              signal input in;
              var unrelated = maxCards + 1;
              assert(unrelated < 64);
            }
        "#;
        validate_reports(src, 0);

        // Var derived from a component output signal.
        let src = r#"
            template ComponentOutputVarAssert() {
              component c = WitnessGen();
              c.seed <== 7;
              var x = c.out;
              assert(x < 100);
            }
        "#;
        // WitnessGen is an unresolved call here; still, `c` is a component
        // read/write source and taints `x`.
        validate_reports(src, 1);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        let mut reports = ReportCollection::new();
        let cfg = parse_definition(src)
            .unwrap()
            .into_cfg(&Curve::default(), &mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        let reports = find_signal_dependent_asserts(&cfg);
        assert_eq!(
            reports.len(),
            expected_len,
            "src produced {} reports, expected {}: {}",
            reports.len(),
            expected_len,
            src
        );
    }
}
