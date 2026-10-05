use std::collections::{HashMap, HashSet};

use log::debug;

use program_structure::ast::*;
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;

/// Names of templates declared `template T() parallel`. Instances of these
/// templates run on a witness thread even when the call omits the `parallel`
/// keyword.
pub fn parallel_template_names(
    templates: &HashMap<String, program_structure::template_data::TemplateData>,
) -> HashSet<String> {
    templates
        .iter()
        .filter(|(_, template)| template.is_parallel())
        .map(|(name, _)| name.clone())
        .collect()
}

/// Warn when a `parallel` component is started and one of its signals is read
/// inside the same loop.
///
/// Circom joins a parallel component as soon as the parent reads an output.
/// Doing that in the loop that instantiates the component runs the calls one
/// at a time. The fast form starts every component (and assigns its inputs) in
/// one loop, then reads the outputs in a later loop.
pub fn find_parallel_output_joins(
    body: &Statement,
    parallel_templates: &HashSet<String>,
) -> ReportCollection {
    debug!("running parallel output in loop analysis pass");
    let mut reports = ReportCollection::new();
    visit_statement(body, parallel_templates, &mut reports);
    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(
    stmt: &Statement,
    parallel_templates: &HashSet<String>,
    reports: &mut ReportCollection,
) {
    match stmt {
        Statement::While { cond, stmt, .. } => {
            reports.append(&mut analyze_loop(cond, stmt, parallel_templates));
            visit_statement(stmt, parallel_templates, reports);
        }
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                visit_statement(stmt, parallel_templates, reports);
            }
        }
        Statement::IfThenElse { if_case, else_case, .. } => {
            visit_statement(if_case, parallel_templates, reports);
            if let Some(else_case) = else_case {
                visit_statement(else_case, parallel_templates, reports);
            }
        }
        _ => {}
    }
}

fn analyze_loop(
    cond: &Expression,
    body: &Statement,
    parallel_templates: &HashSet<String>,
) -> ReportCollection {
    let mut started: HashMap<String, Meta> = HashMap::new();
    let mut reads: Vec<(String, Meta)> = Vec::new();
    let mut immediate: Vec<Meta> = Vec::new();
    let mut walker = Walker {
        parallel_templates,
        started: &mut started,
        reads: &mut reads,
        immediate: &mut immediate,
        nested: false,
    };
    walker.scan_expr(cond);
    walker.scan_stmt(body);

    let mut reports = ReportCollection::new();
    let mut reported = HashSet::new();
    for (name, read_at) in &reads {
        if reported.contains(name) {
            continue;
        }
        let Some(started_at) = started.get(name) else {
            continue;
        };
        reported.insert(name.clone());
        reports.push(named_report(name, read_at, started_at));
    }
    let mut seen_immediate = HashSet::new();
    for meta in &immediate {
        if seen_immediate.insert((meta.location.start, meta.location.end)) {
            reports.push(immediate_report(meta));
        }
    }
    reports
}

struct Walker<'a> {
    parallel_templates: &'a HashSet<String>,
    started: &'a mut HashMap<String, Meta>,
    reads: &'a mut Vec<(String, Meta)>,
    immediate: &'a mut Vec<Meta>,
    /// Nested loops belong to their own analysis. This walk only collects
    /// reads from them, so a component started in the outer loop is still
    /// joined when its output is read in an inner loop.
    nested: bool,
}

impl Walker<'_> {
    fn scan_stmt(&mut self, stmt: &Statement) {
        match stmt {
            Statement::While { cond, stmt, .. } => {
                let outer = self.nested;
                self.nested = true;
                self.scan_expr(cond);
                self.scan_stmt(stmt);
                self.nested = outer;
            }
            Statement::Block { stmts, .. }
            | Statement::InitializationBlock { initializations: stmts, .. } => {
                for stmt in stmts {
                    self.scan_stmt(stmt);
                }
            }
            Statement::IfThenElse { cond, if_case, else_case, .. } => {
                self.scan_expr(cond);
                self.scan_stmt(if_case);
                if let Some(else_case) = else_case {
                    self.scan_stmt(else_case);
                }
            }
            Statement::Substitution { var, access, rhe, .. } => {
                self.scan_accesses(access);
                if !self.nested && !has_component_access(access) {
                    if let Some(meta) = self.named_parallel_call(rhe) {
                        self.started.entry(var.clone()).or_insert(meta);
                        self.scan_call_args(rhe);
                        return;
                    }
                }
                self.scan_expr(rhe);
            }
            Statement::MultiSubstitution { lhe, rhe, .. } => {
                self.scan_expr(lhe);
                self.scan_expr(rhe);
            }
            Statement::ConstraintEquality { lhe, rhe, .. } => {
                self.scan_expr(lhe);
                self.scan_expr(rhe);
            }
            Statement::Return { value, .. } | Statement::Assert { arg: value, .. } => {
                self.scan_expr(value);
            }
            Statement::LogCall { args, .. } => {
                for arg in args {
                    if let LogArgument::LogExp(expr) = arg {
                        self.scan_expr(expr);
                    }
                }
            }
            Statement::Declaration { dimensions, .. } => {
                for dimension in dimensions {
                    self.scan_expr(dimension);
                }
            }
        }
    }

    fn scan_accesses(&mut self, access: &[Access]) {
        for acc in access {
            if let Access::ArrayAccess(index) = acc {
                self.scan_expr(index);
            }
        }
    }

    fn scan_call_args(&mut self, expr: &Expression) {
        match expr {
            Expression::ParallelOp { rhe, .. } => self.scan_call_args(rhe),
            Expression::Call { args, .. } => {
                for arg in args {
                    self.scan_expr(arg);
                }
            }
            _ => self.scan_expr(expr),
        }
    }

    fn scan_expr(&mut self, expr: &Expression) {
        match expr {
            Expression::Variable { meta, name, access } => {
                if has_component_access(access) {
                    self.reads.push((name.clone(), meta.clone()));
                }
                self.scan_accesses(access);
            }
            Expression::ParallelOp { meta, rhe } => {
                // `parallel Foo()(...)` wraps the anonymous component. The
                // inner node is not itself marked parallel.
                if !self.nested && contains_anonymous(rhe) {
                    self.immediate.push(meta.clone());
                }
                self.scan_expr(rhe);
            }
            Expression::AnonymousComponent { meta, id, is_parallel, params, signals, .. } => {
                if !self.nested && (*is_parallel || self.parallel_templates.contains(id)) {
                    self.immediate.push(meta.clone());
                }
                for arg in params.iter().chain(signals.iter()) {
                    self.scan_expr(arg);
                }
            }
            Expression::InfixOp { lhe, rhe, .. } => {
                self.scan_expr(lhe);
                self.scan_expr(rhe);
            }
            Expression::PrefixOp { rhe, .. } => self.scan_expr(rhe),
            Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
                self.scan_expr(cond);
                self.scan_expr(if_true);
                self.scan_expr(if_false);
            }
            Expression::Call { args, .. } => {
                for arg in args {
                    self.scan_expr(arg);
                }
            }
            Expression::ArrayInLine { values, .. } | Expression::Tuple { values, .. } => {
                for value in values {
                    self.scan_expr(value);
                }
            }
            Expression::Number(_, _) => {}
        }
    }

    /// `foo[i] = parallel Bar(...)` or `foo[i] = Bar(...)` when `Bar` itself is
    /// a parallel template. Anonymous components are not named.
    fn named_parallel_call(&self, expr: &Expression) -> Option<Meta> {
        match expr {
            Expression::ParallelOp { meta, rhe } if is_named_call(rhe) => Some(meta.clone()),
            Expression::Call { meta, id, .. } if self.parallel_templates.contains(id) => {
                Some(meta.clone())
            }
            _ => None,
        }
    }
}

fn is_named_call(expr: &Expression) -> bool {
    match expr {
        Expression::Call { .. } => true,
        Expression::ParallelOp { rhe, .. } => is_named_call(rhe),
        _ => false,
    }
}

fn contains_anonymous(expr: &Expression) -> bool {
    match expr {
        Expression::AnonymousComponent { .. } => true,
        Expression::ParallelOp { rhe, .. } => contains_anonymous(rhe),
        _ => false,
    }
}

fn has_component_access(access: &[Access]) -> bool {
    access.iter().any(|acc| matches!(acc, Access::ComponentAccess(_)))
}

fn named_report(name: &str, read_at: &Meta, started_at: &Meta) -> Report {
    let mut report = Report::warning(
        format!(
            "Parallel component `{name}` is read in the same loop that starts it. Witness generation joins that call before the next iteration."
        ),
        ReportCode::ParallelOutputInLoop,
    );
    add_meta(
        &mut report,
        read_at,
        "This read runs the component to completion before the loop repeats.".to_string(),
        true,
    );
    add_meta(&mut report, started_at, format!("`{name}` is started in this loop."), false);
    report.add_note(
        "Start every parallel component and assign its inputs in one loop, then read the outputs in a later loop."
            .to_string(),
    );
    report
}

fn immediate_report(meta: &Meta) -> Report {
    let mut report = Report::warning(
        "Parallel component output is used in the same loop that starts it. Witness generation joins that call before the next iteration.".to_string(),
        ReportCode::ParallelOutputInLoop,
    );
    add_meta(
        &mut report,
        meta,
        "This parallel component is joined before the loop repeats.".to_string(),
        true,
    );
    report.add_note(
        "Start every parallel component and assign its inputs in one loop, then read the outputs in a later loop."
            .to_string(),
    );
    report
}

fn add_meta(report: &mut Report, meta: &Meta, message: String, primary: bool) {
    let Some(file_id) = meta.file_id else {
        return;
    };
    let location: FileLocation = meta.location.clone();
    if primary {
        report.add_primary(location, file_id as FileID, message);
    } else {
        report.add_secondary(location, file_id as FileID, Some(message));
    }
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::ast::Definition;

    use super::*;

    fn reports_for(src: &str) -> ReportCollection {
        reports_for_templates(src, &HashSet::new())
    }

    fn reports_for_templates(src: &str, parallel_templates: &HashSet<String>) -> ReportCollection {
        let definition = parse_definition(src).expect("template should parse");
        let Definition::Template { body, .. } = definition else {
            panic!("expected a template");
        };
        find_parallel_output_joins(&body, parallel_templates)
    }

    #[test]
    fn same_loop_output_read_is_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component foo[n];
                for (var i = 0; i < n; i++) {
                    foo[i] = parallel Bar();
                    foo[i].in <== in[i];
                    out[i] <== foo[i].out;
                }
            }
        "#;
        assert_eq!(reports_for(src).len(), 1);
    }

    #[test]
    fn input_assignment_in_the_start_loop_is_ok() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component foo[n];
                for (var i = 0; i < n; i++) {
                    foo[i] = parallel Bar();
                    foo[i].in <== in[i];
                }
                for (var i = 0; i < n; i++) {
                    out[i] <== foo[i].out;
                }
            }
        "#;
        assert!(reports_for(src).is_empty());
    }

    #[test]
    fn later_loop_may_read_an_earlier_parallel_component() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component foo[n];
                component bar[n];
                for (var i = 0; i < n; i++) {
                    foo[i] = parallel Foo();
                    foo[i].in <== in[i];
                }
                for (var i = 0; i < n; i++) {
                    bar[i] = parallel Bar();
                    bar[i].in <== foo[i].out;
                    out[i] <== bar[i].out;
                }
            }
        "#;
        // `bar` is started and read in the second loop. `foo` was started earlier.
        assert_eq!(reports_for(src).len(), 1);
    }

    #[test]
    fn non_parallel_component_is_not_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component foo[n];
                for (var i = 0; i < n; i++) {
                    foo[i] = Bar();
                    foo[i].in <== in[i];
                    out[i] <== foo[i].out;
                }
            }
        "#;
        assert!(reports_for(src).is_empty());
    }

    #[test]
    fn template_level_parallel_is_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component foo[n];
                for (var i = 0; i < n; i++) {
                    foo[i] = Bar();
                    foo[i].in <== in[i];
                    out[i] <== foo[i].out;
                }
            }
        "#;
        let mut parallel = HashSet::new();
        parallel.insert("Bar".to_string());
        assert_eq!(reports_for_templates(src, &parallel).len(), 1);
    }

    #[test]
    fn anonymous_parallel_in_a_loop_is_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                for (var i = 0; i < n; i++) {
                    out[i] <== parallel Bar()(in[i]);
                }
            }
        "#;
        assert_eq!(reports_for(src).len(), 1);
    }

    #[test]
    fn read_inside_a_nested_loop_is_reported_once() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component foo[n];
                for (var i = 0; i < n; i++) {
                    foo[i] = parallel Bar();
                    foo[i].in <== in[i];
                    for (var j = 0; j < 1; j++) {
                        out[i] <== foo[i].out;
                    }
                }
            }
        "#;
        assert_eq!(reports_for(src).len(), 1);
    }

    #[test]
    fn inner_loop_join_is_not_reported_twice() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component foo[n];
                for (var i = 0; i < n; i++) {
                    for (var j = 0; j < 1; j++) {
                        foo[i] = parallel Bar();
                        foo[i].in <== in[i];
                        out[i] <== foo[i].out;
                    }
                }
            }
        "#;
        assert_eq!(reports_for(src).len(), 1);
    }
}
