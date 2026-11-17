use std::collections::{HashMap, HashSet};

use log::debug;

use program_structure::ast::*;
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;
use program_structure::template_data::TemplateData;

/// Warn when a loop repeats work that does not depend on the loop index.
///
/// The whole component can move out of the loop when every input is invariant.
/// When only some inputs are invariant, a subcomponent that reads just those
/// inputs is the same case: compute it once and pass the result in. Repeated
/// `Num2Bits` of one secret key is the usual instance.
pub fn find_loop_invariant_operations(
    body: &Statement,
    templates: &HashMap<String, TemplateData>,
) -> ReportCollection {
    debug!("running loop-invariant operation analysis pass");
    let mut reports = ReportCollection::new();
    let mut cache: HashMap<String, Vec<PureOp>> = HashMap::new();
    visit(body, templates, &mut cache, &mut reports);
    debug!("{} new reports generated", reports.len());
    reports
}

#[derive(Clone)]
struct PureOp {
    template: String,
    meta: Meta,
    /// Template input signals this operation depends on.
    deps: HashSet<String>,
}

struct Inst {
    var: String,
    template: String,
    meta: Meta,
    /// Template parameters. A parameter that reads the loop index cannot be hoisted.
    args: Vec<Expression>,
    /// Each signal input, in assignment order.
    input_exprs: HashMap<String, Vec<Expression>>,
}

fn visit(
    stmt: &Statement,
    templates: &HashMap<String, TemplateData>,
    cache: &mut HashMap<String, Vec<PureOp>>,
    reports: &mut ReportCollection,
) {
    match stmt {
        Statement::While { cond, stmt, .. } => {
            analyze_loop(cond, stmt, templates, cache, reports);
            visit(stmt, templates, cache, reports);
        }
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                visit(stmt, templates, cache, reports);
            }
        }
        Statement::IfThenElse { if_case, else_case, .. } => {
            visit(if_case, templates, cache, reports);
            if let Some(else_case) = else_case {
                visit(else_case, templates, cache, reports);
            }
        }
        _ => {}
    }
}

fn analyze_loop(
    cond: &Expression,
    body: &Statement,
    templates: &HashMap<String, TemplateData>,
    cache: &mut HashMap<String, Vec<PureOp>>,
    reports: &mut ReportCollection,
) {
    let mut assigned = HashSet::new();
    collect_assigned_vars(body, &mut assigned);
    let mut variant_vars: HashSet<String> = HashSet::new();
    for name in expr_names(cond).0 {
        if assigned.contains(&name) {
            variant_vars.insert(name);
        }
    }

    let mut insts: HashMap<String, Inst> = HashMap::new();
    let mut anon = 0usize;
    // Scalar `var = expr` updates and signal updates, in source order.
    let mut var_updates: Vec<(String, Expression)> = Vec::new();
    let mut signal_updates: Vec<(String, Expression)> = Vec::new();
    collect_loop_body(
        body,
        &mut insts,
        &mut anon,
        &mut var_updates,
        &mut signal_updates,
    );

    // Which component outputs depend on the loop index. Start from the index
    // itself and close over assignments in the body.
    let mut variant_comps: HashSet<String> = HashSet::new();
    loop {
        let vars_before = variant_vars.len();
        let comps_before = variant_comps.len();
        for (name, expr) in &var_updates {
            if expr_varies(expr, &variant_vars, &variant_comps) {
                variant_vars.insert(name.clone());
            }
        }
        for (name, expr) in &signal_updates {
            if expr_varies(expr, &variant_vars, &variant_comps) {
                variant_vars.insert(name.clone());
            }
        }
        for inst in insts.values() {
            let varies = inst.args.iter().any(|arg| expr_varies(arg, &variant_vars, &variant_comps))
                || inst.input_exprs.values().flatten().any(|expr| {
                    expr_varies(expr, &variant_vars, &variant_comps)
                });
            if varies {
                variant_comps.insert(inst.var.clone());
            }
        }
        if variant_vars.len() == vars_before && variant_comps.len() == comps_before {
            break;
        }
    }

    for inst in insts.values() {
        if inst.template.is_empty() {
            continue;
        }
        let param_varies = inst
            .args
            .iter()
            .any(|arg| expr_varies(arg, &variant_vars, &variant_comps));
        let mut inputs: HashMap<String, bool> = HashMap::new();
        for (signal, exprs) in &inst.input_exprs {
            let invariant = exprs.iter().all(|expr| !expr_varies(expr, &variant_vars, &variant_comps));
            inputs.insert(signal.clone(), invariant);
        }
        let wholly_invariant =
            !param_varies && !inputs.is_empty() && inputs.values().all(|invariant| *invariant);
        if wholly_invariant {
            reports.push(whole_report(&inst.var, &inst.template, &inst.meta));
            continue;
        }
        let invariant_inputs: HashSet<String> = inputs
            .iter()
            .filter(|(_, invariant)| **invariant)
            .map(|(name, _)| name.clone())
            .collect();
        if invariant_inputs.is_empty() {
            continue;
        }
        let pure = pure_ops(&inst.template, templates, cache);
        let mut repeated: Vec<&PureOp> = pure
            .iter()
            .filter(|op| !op.deps.is_empty() && op.deps.is_subset(&invariant_inputs))
            .collect();
        if repeated.is_empty() {
            continue;
        }
        repeated.sort_by(|a, b| a.template.cmp(&b.template).then(a.meta.start.cmp(&b.meta.start)));
        repeated.dedup_by(|a, b| a.template == b.template && a.deps == b.deps);
        reports.push(partial_report(&inst.var, &inst.template, &inst.meta, &repeated));
    }
}

fn collect_loop_body(
    stmt: &Statement,
    insts: &mut HashMap<String, Inst>,
    anon: &mut usize,
    var_updates: &mut Vec<(String, Expression)>,
    signal_updates: &mut Vec<(String, Expression)>,
) {
    match stmt {
        Statement::While { .. } => {}
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                collect_loop_body(stmt, insts, anon, var_updates, signal_updates);
            }
        }
        Statement::IfThenElse { if_case, else_case, .. } => {
            collect_loop_body(if_case, insts, anon, var_updates, signal_updates);
            if let Some(else_case) = else_case {
                collect_loop_body(else_case, insts, anon, var_updates, signal_updates);
            }
        }
        Statement::Substitution { meta, var, access, op, rhe } => {
            if let Some(template) = call_template(rhe) {
                let args = call_args(rhe);
                let inst = insts.entry(var.clone()).or_insert_with(|| Inst {
                    var: var.clone(),
                    template: String::new(),
                    meta: meta.clone(),
                    args: Vec::new(),
                    input_exprs: HashMap::new(),
                });
                if inst.template.is_empty() {
                    inst.template = template;
                    inst.meta = meta.clone();
                    inst.args = args;
                }
                return;
            }
            if let Some(signal) = component_signal(access) {
                insts
                    .entry(var.clone())
                    .or_insert_with(|| Inst {
                        var: var.clone(),
                        template: String::new(),
                        meta: meta.clone(),
                        args: Vec::new(),
                        input_exprs: HashMap::new(),
                    })
                    .input_exprs
                    .entry(signal)
                    .or_default()
                    .push(rhe.clone());
                return;
            }
            if *op == AssignOp::AssignVar && access.is_empty() {
                var_updates.push((var.clone(), rhe.clone()));
            } else if *op != AssignOp::AssignVar {
                signal_updates.push((var.clone(), rhe.clone()));
            }
            collect_anonymous(rhe, insts, anon);
        }
        Statement::ConstraintEquality { lhe, rhe, .. } => {
            collect_anonymous(lhe, insts, anon);
            collect_anonymous(rhe, insts, anon);
        }
        Statement::MultiSubstitution { lhe, rhe, .. } => {
            collect_anonymous(lhe, insts, anon);
            collect_anonymous(rhe, insts, anon);
        }
        Statement::Return { value, .. } | Statement::Assert { arg: value, .. } => {
            collect_anonymous(value, insts, anon);
        }
        _ => {}
    }
}

fn call_args(expr: &Expression) -> Vec<Expression> {
    match expr {
        Expression::ParallelOp { rhe, .. } => call_args(rhe),
        Expression::Call { args, .. } => args.clone(),
        _ => Vec::new(),
    }
}

fn collect_anonymous(expr: &Expression, insts: &mut HashMap<String, Inst>, anon: &mut usize) {
    match expr {
        Expression::AnonymousComponent { meta, id, params, signals, .. } => {
            *anon += 1;
            let key = format!("<anon {}>", *anon);
            let mut input_exprs = HashMap::new();
            for (index, signal) in signals.iter().enumerate() {
                input_exprs
                    .entry(format!("arg{index}"))
                    .or_insert_with(Vec::new)
                    .push(signal.clone());
            }
            insts.insert(
                key.clone(),
                Inst {
                    var: key,
                    template: id.clone(),
                    meta: meta.clone(),
                    args: params.clone(),
                    input_exprs,
                },
            );
        }
        Expression::ParallelOp { rhe, .. } => collect_anonymous(rhe, insts, anon),
        Expression::InfixOp { lhe, rhe, .. } => {
            collect_anonymous(lhe, insts, anon);
            collect_anonymous(rhe, insts, anon);
        }
        Expression::PrefixOp { rhe, .. } => collect_anonymous(rhe, insts, anon),
        Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
            collect_anonymous(cond, insts, anon);
            collect_anonymous(if_true, insts, anon);
            collect_anonymous(if_false, insts, anon);
        }
        Expression::Call { args, .. } => {
            for arg in args {
                collect_anonymous(arg, insts, anon);
            }
        }
        Expression::ArrayInLine { values, .. } | Expression::Tuple { values, .. } => {
            for value in values {
                collect_anonymous(value, insts, anon);
            }
        }
        Expression::Variable { access, .. } => {
            for acc in access {
                if let Access::ArrayAccess(index) = acc {
                    collect_anonymous(index, insts, anon);
                }
            }
        }
        Expression::Number(_, _) => {}
    }
}

fn collect_assigned_vars(stmt: &Statement, assigned: &mut HashSet<String>) {
    match stmt {
        Statement::While { .. } => {}
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                collect_assigned_vars(stmt, assigned);
            }
        }
        Statement::IfThenElse { if_case, else_case, .. } => {
            collect_assigned_vars(if_case, assigned);
            if let Some(else_case) = else_case {
                collect_assigned_vars(else_case, assigned);
            }
        }
        Statement::Substitution { var, access, op, rhe, .. } => {
            if *op == AssignOp::AssignVar && access.is_empty() && call_template(rhe).is_none() {
                assigned.insert(var.clone());
            }
        }
        _ => {}
    }
}

fn expr_varies(expr: &Expression, vars: &HashSet<String>, comps: &HashSet<String>) -> bool {
    let (names, read_comps) = expr_names(expr);
    names.iter().any(|name| vars.contains(name)) || read_comps.iter().any(|name| comps.contains(name))
}

/// Signal names and component names read by an expression.
fn expr_names(expr: &Expression) -> (HashSet<String>, HashSet<String>) {
    let mut names = HashSet::new();
    let mut comps = HashSet::new();
    walk_names(expr, &mut names, &mut comps);
    (names, comps)
}

fn walk_names(expr: &Expression, names: &mut HashSet<String>, comps: &mut HashSet<String>) {
    match expr {
        Expression::Variable { name, access, .. } => {
            if access.iter().any(|acc| matches!(acc, Access::ComponentAccess(_))) {
                comps.insert(name.clone());
            } else {
                names.insert(name.clone());
            }
            for acc in access {
                if let Access::ArrayAccess(index) = acc {
                    walk_names(index, names, comps);
                }
            }
        }
        Expression::InfixOp { lhe, rhe, .. } => {
            walk_names(lhe, names, comps);
            walk_names(rhe, names, comps);
        }
        Expression::PrefixOp { rhe, .. } | Expression::ParallelOp { rhe, .. } => {
            walk_names(rhe, names, comps);
        }
        Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
            walk_names(cond, names, comps);
            walk_names(if_true, names, comps);
            walk_names(if_false, names, comps);
        }
        Expression::Call { args, .. } => {
            for arg in args {
                walk_names(arg, names, comps);
            }
        }
        Expression::AnonymousComponent { params, signals, .. } => {
            for arg in params.iter().chain(signals.iter()) {
                walk_names(arg, names, comps);
            }
        }
        Expression::ArrayInLine { values, .. } | Expression::Tuple { values, .. } => {
            for value in values {
                walk_names(value, names, comps);
            }
        }
        Expression::Number(_, _) => {}
    }
}

fn call_template(expr: &Expression) -> Option<String> {
    match expr {
        Expression::ParallelOp { rhe, .. } => call_template(rhe),
        Expression::Call { id, .. } => Some(id.clone()),
        _ => None,
    }
}

fn component_signal(access: &[Access]) -> Option<String> {
    access.iter().find_map(|acc| match acc {
        Access::ComponentAccess(name) => Some(name.clone()),
        Access::ArrayAccess(_) => None,
    })
}

fn pure_ops<'a>(
    name: &str,
    templates: &HashMap<String, TemplateData>,
    cache: &'a mut HashMap<String, Vec<PureOp>>,
) -> &'a [PureOp] {
    if !cache.contains_key(name) {
        let ops = templates
            .get(name)
            .map(|template| pure_ops_in(template))
            .unwrap_or_default();
        cache.insert(name.to_string(), ops);
    }
    cache.get(name).map(Vec::as_slice).unwrap_or(&[])
}

struct RawComp {
    var: String,
    template: String,
    meta: Meta,
    signals: HashSet<String>,
    comps: HashSet<String>,
}

fn pure_ops_in(template: &TemplateData) -> Vec<PureOp> {
    let inputs: HashSet<String> = template.get_inputs().keys().cloned().collect();
    let mut comps = Vec::new();
    let mut signals: Vec<(String, HashSet<String>, HashSet<String>)> = Vec::new();
    collect_template_ops(template.get_body(), &mut comps, &mut signals);

    let mut comp_deps: HashMap<String, HashSet<String>> = HashMap::new();
    let mut comp_reads: HashMap<String, HashSet<String>> = HashMap::new();
    let mut comp_meta: HashMap<String, (String, Meta)> = HashMap::new();
    for comp in &comps {
        comp_deps.insert(comp.var.clone(), comp.signals.clone());
        comp_reads.insert(comp.var.clone(), comp.comps.clone());
        comp_meta.insert(comp.var.clone(), (comp.template.clone(), comp.meta.clone()));
    }
    let mut sig_deps: HashMap<String, HashSet<String>> = HashMap::new();
    let mut sig_comps: HashMap<String, HashSet<String>> = HashMap::new();
    for (name, read_signals, read_comps) in &signals {
        sig_deps.insert(name.clone(), read_signals.clone());
        sig_comps.insert(name.clone(), read_comps.clone());
    }

    for _ in 0..comps.len() + signals.len() + 1 {
        let mut changed = false;
        let sig_snapshot = sig_deps.clone();
        let comp_snapshot = comp_deps.clone();
        for (name, deps) in sig_deps.iter_mut() {
            let reads = sig_comps.get(name).cloned().unwrap_or_default();
            changed |= expand_deps(deps, &reads, &inputs, &sig_snapshot, &comp_snapshot);
        }
        for (name, deps) in comp_deps.iter_mut() {
            let reads = comp_reads.get(name).cloned().unwrap_or_default();
            changed |= expand_deps(deps, &reads, &inputs, &sig_snapshot, &comp_snapshot);
        }
        if !changed {
            break;
        }
    }

    let mut ops = Vec::new();
    for (var, deps) in comp_deps {
        if deps.is_empty() || !deps.is_subset(&inputs) {
            continue;
        }
        let Some((template, meta)) = comp_meta.get(&var) else {
            continue;
        };
        ops.push(PureOp {
            template: template.clone(),
            meta: meta.clone(),
            deps,
        });
    }
    ops
}

fn expand_deps(
    deps: &mut HashSet<String>,
    comp_reads: &HashSet<String>,
    inputs: &HashSet<String>,
    sig_deps: &HashMap<String, HashSet<String>>,
    comp_deps: &HashMap<String, HashSet<String>>,
) -> bool {
    let mut extra = HashSet::new();
    let mut remove = Vec::new();
    for name in deps.iter() {
        if inputs.contains(name) {
            continue;
        }
        if let Some(inner) = sig_deps.get(name) {
            extra.extend(inner.iter().cloned());
            remove.push(name.clone());
        }
    }
    for name in comp_reads {
        if let Some(inner) = comp_deps.get(name) {
            extra.extend(inner.iter().cloned());
        }
    }
    let old = deps.clone();
    for name in remove {
        deps.remove(&name);
    }
    deps.extend(extra);
    *deps != old
}

fn collect_template_ops(
    stmt: &Statement,
    comps: &mut Vec<RawComp>,
    signals: &mut Vec<(String, HashSet<String>, HashSet<String>)>,
) {
    match stmt {
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                collect_template_ops(stmt, comps, signals);
            }
        }
        Statement::IfThenElse { if_case, else_case, .. } => {
            collect_template_ops(if_case, comps, signals);
            if let Some(else_case) = else_case {
                collect_template_ops(else_case, comps, signals);
            }
        }
        Statement::While { stmt, .. } => collect_template_ops(stmt, comps, signals),
        Statement::Substitution { meta, var, access, rhe, .. } => {
            if let Some(template) = call_template(rhe) {
                let (read_signals, read_comps) = expr_names(rhe);
                comps.push(RawComp {
                    var: var.clone(),
                    template,
                    meta: meta.clone(),
                    signals: read_signals,
                    comps: read_comps,
                });
                return;
            }
            if component_signal(access).is_some() {
                if let Some(comp) = comps.iter_mut().rev().find(|comp| comp.var == *var) {
                    let (read_signals, read_comps) = expr_names(rhe);
                    comp.signals.extend(read_signals);
                    comp.comps.extend(read_comps);
                }
                return;
            }
            if access.is_empty() {
                let (read_signals, read_comps) = expr_names(rhe);
                signals.push((var.clone(), read_signals, read_comps));
            }
        }
        _ => {}
    }
}

fn whole_report(var: &str, template: &str, meta: &Meta) -> Report {
    let mut report = Report::warning(
        format!(
            "`{var}` (`{template}`) does not depend on the loop index, so every iteration repeats it"
        ),
        ReportCode::LoopInvariantOperation,
    );
    add_meta(
        &mut report,
        meta,
        "Compute this once before the loop and pass the result in.".to_string(),
    );
    report
}

fn partial_report(var: &str, template: &str, meta: &Meta, ops: &[&PureOp]) -> Report {
    let names = ops
        .iter()
        .map(|op| format!("`{}`", op.template))
        .collect::<Vec<_>>()
        .join(", ");
    let inputs = {
        let mut deps: Vec<&String> = ops.iter().flat_map(|op| op.deps.iter()).collect();
        deps.sort();
        deps.dedup();
        deps.iter().map(|name| format!("`{name}`")).collect::<Vec<_>>().join(", ")
    };
    let mut report = Report::warning(
        format!(
            "`{var}` (`{template}`) repeats {names} from {inputs} on every iteration"
        ),
        ReportCode::LoopInvariantOperation,
    );
    add_meta(
        &mut report,
        meta,
        "Compute that operation once before the loop and pass the result in.".to_string(),
    );
    for op in ops.iter().take(3) {
        let Some(file_id) = op.meta.file_id else {
            continue;
        };
        report.add_secondary(
            op.meta.location.clone(),
            file_id as FileID,
            Some(format!("`{}` depends only on the loop-invariant input", op.template)),
        );
    }
    report
}

fn add_meta(report: &mut Report, meta: &Meta, message: String) {
    let Some(file_id) = meta.file_id else {
        return;
    };
    let location: FileLocation = meta.location.clone();
    report.add_primary(location, file_id as FileID, message);
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::ast::Definition;

    use super::*;

    fn load(sources: &[&str]) -> HashMap<String, TemplateData> {
        let mut elem_id = 0usize;
        let mut map = HashMap::new();
        for (file_id, src) in sources.iter().enumerate() {
            let definition = parse_definition(src).expect("template should parse");
            let Definition::Template { name, body, args, arg_location, parallel, is_custom_gate, .. } =
                definition
            else {
                panic!("expected a template");
            };
            let data = TemplateData::new(
                name.clone(),
                file_id,
                body,
                args.len(),
                args,
                arg_location,
                &mut elem_id,
                parallel,
                is_custom_gate,
            );
            map.insert(name, data);
        }
        map
    }

    fn messages(body: &Statement, templates: &HashMap<String, TemplateData>) -> Vec<String> {
        find_loop_invariant_operations(body, templates)
            .into_iter()
            .map(|report| report.message().to_string())
            .collect()
    }

    #[test]
    fn repeated_bit_decomposition_of_one_key_is_reported() {
        let map = load(&[
            r#"
            template Decrypt() {
                signal input ciphertext;
                signal input privateKey;
                signal output out;
                component bits = Num2Bits(253);
                bits.in <== privateKey;
                out <== ciphertext;
            }
            "#,
            r#"
            template Caller(n) {
                signal input privateKey;
                signal input ciphertext[n];
                signal output out[n];
                component decrypt[n];
                for (var i = 0; i < n; i++) {
                    decrypt[i] = Decrypt();
                    decrypt[i].ciphertext <== ciphertext[i];
                    decrypt[i].privateKey <== privateKey;
                    out[i] <== decrypt[i].out;
                }
            }
            "#,
        ]);
        let found = messages(map["Caller"].get_body(), &map);
        assert!(
            found.iter().any(|message| message.contains("Num2Bits") && message.contains("privateKey")),
            "{found:?}"
        );
        assert!(found.iter().all(|message| !message.contains("does not depend on the loop index")));
    }

    #[test]
    fn bits_passed_in_are_not_reported() {
        let map = load(&[
            r#"
            template Decrypt() {
                signal input ciphertext;
                signal input privateKeyBits;
                signal output out;
                out <== ciphertext + privateKeyBits;
            }
            "#,
            r#"
            template Caller(n) {
                signal input privateKey;
                signal input ciphertext[n];
                signal output out[n];
                component skBits = Num2Bits(253);
                skBits.in <== privateKey;
                component decrypt[n];
                for (var i = 0; i < n; i++) {
                    decrypt[i] = Decrypt();
                    decrypt[i].ciphertext <== ciphertext[i];
                    decrypt[i].privateKeyBits <== skBits.out;
                    out[i] <== decrypt[i].out;
                }
            }
            "#,
        ]);
        let found = messages(map["Caller"].get_body(), &map);
        assert!(found.is_empty(), "{found:?}");
    }

    #[test]
    fn invariant_component_in_the_loop_is_reported() {
        let map = load(&[
            r#"
            template Caller(n) {
                signal input key;
                signal output out[n];
                component bits[n];
                for (var i = 0; i < n; i++) {
                    bits[i] = Num2Bits(8);
                    bits[i].in <== key;
                    out[i] <== bits[i].out[0];
                }
            }
            "#,
        ]);
        let found = messages(map["Caller"].get_body(), &map);
        assert_eq!(found.len(), 1, "{found:?}");
        assert!(found[0].contains("does not depend on the loop index"), "{found:?}");
    }

    #[test]
    fn per_iteration_input_is_not_a_whole_component_hit() {
        let map = load(&[
            r#"
            template Caller(n) {
                signal input key[n];
                signal output out[n];
                component bits[n];
                for (var i = 0; i < n; i++) {
                    bits[i] = Num2Bits(8);
                    bits[i].in <== key[i];
                    out[i] <== bits[i].out[0];
                }
            }
            "#,
        ]);
        let found = messages(map["Caller"].get_body(), &map);
        assert!(found.is_empty(), "{found:?}");
    }
}
