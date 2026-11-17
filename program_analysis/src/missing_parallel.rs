use std::collections::{HashMap, HashSet};

use log::debug;

use program_structure::ast::*;
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;
use program_structure::template_data::TemplateData;

/// Warn when a component's witness can overlap other work and neither the
/// instantiation nor the template is marked `parallel`.
///
/// A loop-carried chain is excluded: the next iteration cannot start until it
/// reads this component's output, so the keyword would not overlap the calls.
/// Comparators, bit converters, and other templates that only wrap them are
/// excluded too: spawning a witness thread costs more than running them inline.
pub fn find_missing_parallel(
    body: &Statement,
    parallel_templates: &HashSet<String>,
    templates: &HashMap<String, TemplateData>,
) -> ReportCollection {
    debug!("running missing parallel analysis pass");
    let mut reports = ReportCollection::new();
    let mut seen = HashSet::new();
    let mut ctx = Ctx {
        parallel_templates,
        templates,
        reports: &mut reports,
        seen: &mut seen,
        cost: HashMap::new(),
        visiting: HashSet::new(),
    };
    analyze_region(body, false, &mut ctx);
    debug!("{} new reports generated", reports.len());
    reports
}

struct Ctx<'a> {
    parallel_templates: &'a HashSet<String>,
    templates: &'a HashMap<String, TemplateData>,
    reports: &'a mut ReportCollection,
    seen: &'a mut HashSet<(usize, usize)>,
    cost: HashMap<String, bool>,
    visiting: HashSet<String>,
}

struct Started {
    name: String,
    meta: Meta,
    is_parallel: bool,
    template: String,
    deps: HashSet<String>,
    /// First input assignment. The witness cannot start before this.
    ready_at: Option<usize>,
    joined: Option<usize>,
}

enum Event {
    Start {
        name: String,
        meta: Meta,
        is_parallel: bool,
        template: String,
        arg_comps: HashSet<String>,
        arg_signals: HashSet<String>,
    },
    /// Inputs of `name`. Components named here are joined.
    Input {
        name: String,
        signals: HashSet<String>,
        comps: HashSet<String>,
    },
    SignalAssign {
        dest: String,
        signals: HashSet<String>,
        comps: HashSet<String>,
    },
    Join {
        comps: HashSet<String>,
    },
    /// A loop. `reads` joins outer components. `starts` means the loop
    /// instantiates some component. `inputs` are input assignments to
    /// components started outside the loop.
    Barrier {
        reads: HashSet<String>,
        starts: bool,
        inputs: Vec<(String, HashSet<String>, HashSet<String>)>,
    },
}

fn analyze_region(stmt: &Statement, in_loop: bool, ctx: &mut Ctx<'_>) {
    let mut events = Vec::new();
    collect(stmt, in_loop, &mut events, ctx);
    report_siblings(&events, ctx);
}

fn collect(stmt: &Statement, in_loop: bool, events: &mut Vec<Event>, ctx: &mut Ctx<'_>) {
    match stmt {
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                collect(stmt, in_loop, events, ctx);
            }
        }
        Statement::While { cond, stmt, .. } => {
            warn_loop_instances(stmt, ctx);
            analyze_region(stmt, true, ctx);
            let mut summary = summarize(stmt);
            summary.reads.extend(component_reads(cond));
            events.push(Event::Barrier {
                reads: summary.reads,
                starts: summary.starts,
                inputs: summary.inputs,
            });
        }
        Statement::IfThenElse { cond, if_case, else_case, .. } => {
            let comps = component_reads(cond);
            if !comps.is_empty() {
                events.push(Event::Join { comps });
            }
            analyze_region(if_case, in_loop, ctx);
            if let Some(else_case) = else_case {
                analyze_region(else_case, in_loop, ctx);
            }
            let mut summary = summarize(if_case);
            if let Some(else_case) = else_case {
                let other = summarize(else_case);
                summary.reads.extend(other.reads);
                summary.inputs.extend(other.inputs);
            }
            summary.reads.extend(component_reads(cond));
            // Joining when either branch reads avoids warning about overlap
            // that exists on only one path. Branches are analyzed on their own.
            events.push(Event::Barrier {
                reads: summary.reads,
                starts: false,
                inputs: summary.inputs,
            });
        }
        Statement::Substitution { var, access, rhe, .. } => {
            note_anonymous(rhe, in_loop, ctx);
            let index_comps = access_component_reads(access);
            if !index_comps.is_empty() {
                events.push(Event::Join { comps: index_comps });
            }
            if !has_component_access(access) {
                if let Some(start) = named_start(var, rhe, ctx.parallel_templates) {
                    events.push(start);
                    return;
                }
            }
            let signals = signal_names(rhe);
            let comps = component_reads(rhe);
            if has_component_access(access) {
                events.push(Event::Input { name: var.clone(), signals, comps });
            } else if !comps.is_empty() || !signals.is_empty() {
                events.push(Event::SignalAssign { dest: var.clone(), signals, comps });
            }
        }
        Statement::MultiSubstitution { lhe, rhe, .. } => {
            note_anonymous(lhe, in_loop, ctx);
            note_anonymous(rhe, in_loop, ctx);
            let comps = {
                let mut comps = component_reads(lhe);
                comps.extend(component_reads(rhe));
                comps
            };
            if !comps.is_empty() {
                events.push(Event::Join { comps });
            }
        }
        Statement::ConstraintEquality { lhe, rhe, .. } => {
            note_anonymous(lhe, in_loop, ctx);
            note_anonymous(rhe, in_loop, ctx);
            let mut comps = component_reads(lhe);
            comps.extend(component_reads(rhe));
            if !comps.is_empty() {
                events.push(Event::Join { comps });
            }
        }
        Statement::Return { value, .. } | Statement::Assert { arg: value, .. } => {
            note_anonymous(value, in_loop, ctx);
            let comps = component_reads(value);
            if !comps.is_empty() {
                events.push(Event::Join { comps });
            }
        }
        Statement::LogCall { args, .. } => {
            for arg in args {
                if let LogArgument::LogExp(expr) = arg {
                    note_anonymous(expr, in_loop, ctx);
                    let comps = component_reads(expr);
                    if !comps.is_empty() {
                        events.push(Event::Join { comps });
                    }
                }
            }
        }
        Statement::Declaration { .. } => {}
    }
}

fn warn_loop_instances(body: &Statement, ctx: &mut Ctx<'_>) {
    let instances = instances_in(body, ctx.parallel_templates);
    let (produced, deps) = signal_flow(body);
    for inst in instances {
        if inst.is_parallel {
            continue;
        }
        let carried = inst
            .inputs
            .iter()
            .any(|signal| reaches(signal, &inst.name, &produced, &deps, &mut HashSet::new()));
        if !carried {
            warn(&inst.name, &inst.template, &inst.meta, ctx);
        }
    }
}

struct Instance {
    name: String,
    meta: Meta,
    template: String,
    is_parallel: bool,
    inputs: HashSet<String>,
}

/// Instantiations in this loop, not in a nested loop.
fn instances_in(stmt: &Statement, parallel_templates: &HashSet<String>) -> Vec<Instance> {
    let mut found = Vec::new();
    collect_instances(stmt, false, parallel_templates, &mut found);
    for inst in &mut found {
        let mut inputs = HashSet::new();
        collect_input_signals(stmt, &inst.name, &mut inputs);
        inst.inputs = inputs;
    }
    found
}

fn collect_instances(
    stmt: &Statement,
    nested: bool,
    parallel_templates: &HashSet<String>,
    found: &mut Vec<Instance>,
) {
    match stmt {
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                collect_instances(stmt, nested, parallel_templates, found);
            }
        }
        Statement::While { stmt, .. } => {
            if !nested {
                // Descend once so a loop body is visited, and skip loops inside it.
                collect_instances(stmt, true, parallel_templates, found);
            }
        }
        Statement::IfThenElse { if_case, else_case, .. } => {
            collect_instances(if_case, nested, parallel_templates, found);
            if let Some(else_case) = else_case {
                collect_instances(else_case, nested, parallel_templates, found);
            }
        }
        Statement::Substitution { var, access, rhe, .. }
            if !nested && !has_component_access(access) =>
        {
            if let Some((mut is_parallel, meta, template)) = call_info(rhe) {
                if parallel_templates.contains(&template) {
                    is_parallel = true;
                }
                found.push(Instance {
                    name: var.clone(),
                    meta,
                    template,
                    is_parallel,
                    inputs: HashSet::new(),
                });
            }
        }
        _ => {}
    }
}

fn collect_input_signals(stmt: &Statement, name: &str, inputs: &mut HashSet<String>) {
    match stmt {
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                collect_input_signals(stmt, name, inputs);
            }
        }
        Statement::While { stmt, .. } => collect_input_signals(stmt, name, inputs),
        Statement::IfThenElse { if_case, else_case, .. } => {
            collect_input_signals(if_case, name, inputs);
            if let Some(else_case) = else_case {
                collect_input_signals(else_case, name, inputs);
            }
        }
        Statement::Substitution { var, access, rhe, .. }
            if var == name && has_component_access(access) =>
        {
            inputs.extend(signal_names(rhe));
            inputs.extend(access_signal_names(access));
        }
        _ => {}
    }
}

/// `produced[signal]` is the set of components whose outputs were written into
/// that signal. `deps[signal]` is the set of signals it was assigned from.
fn signal_flow(
    stmt: &Statement,
) -> (HashMap<String, HashSet<String>>, HashMap<String, HashSet<String>>) {
    let mut produced = HashMap::new();
    let mut deps = HashMap::new();
    flow_stmt(stmt, &mut produced, &mut deps);
    (produced, deps)
}

fn flow_stmt(
    stmt: &Statement,
    produced: &mut HashMap<String, HashSet<String>>,
    deps: &mut HashMap<String, HashSet<String>>,
) {
    match stmt {
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                flow_stmt(stmt, produced, deps);
            }
        }
        Statement::While { stmt, .. } => flow_stmt(stmt, produced, deps),
        Statement::IfThenElse { if_case, else_case, .. } => {
            flow_stmt(if_case, produced, deps);
            if let Some(else_case) = else_case {
                flow_stmt(else_case, produced, deps);
            }
        }
        Statement::Substitution { var, access, rhe, .. }
            if !has_component_access(access) && call_info(rhe).is_none() =>
        {
            produced.entry(var.clone()).or_default().extend(component_reads(rhe));
            deps.entry(var.clone()).or_default().extend(signal_names(rhe));
        }
        _ => {}
    }
}

fn reaches(
    signal: &str,
    component: &str,
    produced: &HashMap<String, HashSet<String>>,
    deps: &HashMap<String, HashSet<String>>,
    seen: &mut HashSet<String>,
) -> bool {
    if !seen.insert(signal.to_string()) {
        return false;
    }
    if produced.get(signal).is_some_and(|comps| comps.contains(component)) {
        return true;
    }
    deps.get(signal).into_iter().flatten().any(|src| reaches(src, component, produced, deps, seen))
}

fn report_siblings(events: &[Event], ctx: &mut Ctx<'_>) {
    let mut comps: Vec<Started> = Vec::new();
    let mut produced: HashMap<String, HashSet<String>> = HashMap::new();
    let mut barriers: Vec<(usize, HashSet<String>, bool)> = Vec::new();

    for (index, event) in events.iter().enumerate() {
        match event {
            Event::Start { name, meta, is_parallel, template, arg_comps, arg_signals } => {
                let mut deps = arg_comps.clone();
                for signal in arg_signals {
                    if let Some(from) = produced.get(signal) {
                        deps.extend(from.iter().cloned());
                    }
                }
                join_named(&mut comps, arg_comps, index);
                comps.push(Started {
                    name: name.clone(),
                    meta: meta.clone(),
                    is_parallel: *is_parallel,
                    template: template.clone(),
                    deps,
                    ready_at: None,
                    joined: None,
                });
            }
            Event::Input { name, signals, comps: read } => {
                let mut extra = HashSet::new();
                for signal in signals {
                    if let Some(from) = produced.get(signal) {
                        extra.extend(from.iter().cloned());
                    }
                }
                if let Some(comp) =
                    comps.iter_mut().rev().find(|comp| comp.name == *name && comp.joined.is_none())
                {
                    comp.deps.extend(read.iter().cloned());
                    comp.deps.extend(extra);
                    if comp.ready_at.is_none() {
                        comp.ready_at = Some(index);
                    }
                }
                join_named(&mut comps, read, index);
            }
            Event::SignalAssign { dest, signals, comps: read } => {
                let mut from = read.clone();
                for signal in signals {
                    if let Some(producers) = produced.get(signal) {
                        from.extend(producers.iter().cloned());
                    }
                }
                produced.entry(dest.clone()).or_default().extend(from);
                join_named(&mut comps, read, index);
            }
            Event::Join { comps: read } => join_named(&mut comps, read, index),
            Event::Barrier { reads, starts, inputs } => {
                // Components already input-ready can overlap work this loop starts.
                barriers.push((index, reads.clone(), *starts));
                for (name, signals, read) in inputs {
                    let mut extra = HashSet::new();
                    for signal in signals {
                        if let Some(from) = produced.get(signal) {
                            extra.extend(from.iter().cloned());
                        }
                    }
                    if let Some(comp) = comps
                        .iter_mut()
                        .rev()
                        .find(|comp| comp.name == *name && comp.joined.is_none())
                    {
                        comp.deps.extend(read.iter().cloned());
                        comp.deps.extend(extra);
                        if comp.ready_at.is_none() {
                            comp.ready_at = Some(index);
                        }
                    }
                    join_named(&mut comps, read, index);
                }
                join_named(&mut comps, reads, index);
            }
        }
    }

    let end = events.len();
    for i in 0..comps.len() {
        for j in (i + 1)..comps.len() {
            let (left, right) = (&comps[i], &comps[j]);
            let (Some(left_ready), Some(right_ready)) = (left.ready_at, right.ready_at) else {
                continue;
            };
            let left_join = left.joined.unwrap_or(end);
            let right_join = right.joined.unwrap_or(end);
            // Both witnesses can be running: each is input-ready before the
            // other is joined.
            let overlap = left_ready < right_join && right_ready < left_join;
            let independent = !left.deps.contains(&right.name) && !right.deps.contains(&left.name);
            if overlap && independent {
                if !left.is_parallel {
                    warn(&left.name, &left.template, &left.meta, ctx);
                }
                if !right.is_parallel {
                    warn(&right.name, &right.template, &right.meta, ctx);
                }
            }
        }
    }
    for comp in &comps {
        if comp.is_parallel {
            continue;
        }
        let join = comp.joined.unwrap_or(end);
        let Some(ready) = comp.ready_at else {
            continue;
        };
        for (pos, reads, starts) in &barriers {
            if *starts && ready < *pos && *pos < join && !reads.contains(&comp.name) {
                warn(&comp.name, &comp.template, &comp.meta, ctx);
            }
        }
    }
}

fn join_named(comps: &mut [Started], names: &HashSet<String>, at: usize) {
    for comp in comps.iter_mut() {
        if comp.joined.is_none() && names.contains(&comp.name) {
            comp.joined = Some(at);
        }
    }
}

fn named_start(var: &str, rhe: &Expression, parallel_templates: &HashSet<String>) -> Option<Event> {
    let (is_parallel, meta, template) = call_info(rhe)?;
    let is_parallel = is_parallel || parallel_templates.contains(&template);
    let mut arg_comps = HashSet::new();
    let mut arg_signals = HashSet::new();
    if let Some(args) = call_args(rhe) {
        for arg in args {
            arg_comps.extend(component_reads(arg));
            arg_signals.extend(signal_names(arg));
        }
    }
    Some(Event::Start {
        name: var.to_string(),
        meta,
        is_parallel,
        template,
        arg_comps,
        arg_signals,
    })
}

/// `(is_parallel, meta, template name)` for `Foo()` and `parallel Foo()`.
fn call_info(expr: &Expression) -> Option<(bool, Meta, String)> {
    match expr {
        Expression::ParallelOp { rhe, .. } => call_info(rhe).map(|(_, meta, id)| (true, meta, id)),
        Expression::Call { meta, id, .. } => Some((false, meta.clone(), id.clone())),
        _ => None,
    }
}

fn call_args(expr: &Expression) -> Option<&[Expression]> {
    match expr {
        Expression::ParallelOp { rhe, .. } => call_args(rhe),
        Expression::Call { args, .. } => Some(args),
        _ => None,
    }
}

struct Summary {
    reads: HashSet<String>,
    starts: bool,
    inputs: Vec<(String, HashSet<String>, HashSet<String>)>,
}

fn summarize(stmt: &Statement) -> Summary {
    let mut summary = Summary { reads: HashSet::new(), starts: false, inputs: Vec::new() };
    summarize_into(stmt, &mut summary);
    summary
}

fn summarize_into(stmt: &Statement, summary: &mut Summary) {
    match stmt {
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                summarize_into(stmt, summary);
            }
        }
        Statement::While { cond, stmt, .. } => {
            summary.reads.extend(component_reads(cond));
            summarize_into(stmt, summary);
        }
        Statement::IfThenElse { cond, if_case, else_case, .. } => {
            summary.reads.extend(component_reads(cond));
            summarize_into(if_case, summary);
            if let Some(else_case) = else_case {
                summarize_into(else_case, summary);
            }
        }
        Statement::Substitution { var, access, rhe, .. } => {
            summary.reads.extend(access_component_reads(access));
            if has_component_access(access) {
                summary.inputs.push((var.clone(), signal_names(rhe), component_reads(rhe)));
                summary.reads.extend(component_reads(rhe));
            } else {
                summary.reads.extend(component_reads(rhe));
                summary.starts |= call_info(rhe).is_some() || contains_anonymous(rhe);
            }
        }
        Statement::MultiSubstitution { lhe, rhe, .. } => {
            summary.reads.extend(component_reads(lhe));
            summary.reads.extend(component_reads(rhe));
            summary.starts |=
                contains_anonymous(lhe) || contains_anonymous(rhe) || call_info(rhe).is_some();
        }
        Statement::ConstraintEquality { lhe, rhe, .. } => {
            summary.reads.extend(component_reads(lhe));
            summary.reads.extend(component_reads(rhe));
            summary.starts |= contains_anonymous(lhe) || contains_anonymous(rhe);
        }
        Statement::Return { value, .. } | Statement::Assert { arg: value, .. } => {
            summary.reads.extend(component_reads(value));
            summary.starts |= contains_anonymous(value);
        }
        Statement::LogCall { args, .. } => {
            for arg in args {
                if let LogArgument::LogExp(expr) = arg {
                    summary.reads.extend(component_reads(expr));
                    summary.starts |= contains_anonymous(expr);
                }
            }
        }
        Statement::Declaration { .. } => {}
    }
}

fn note_anonymous(expr: &Expression, in_loop: bool, ctx: &mut Ctx<'_>) {
    if !in_loop {
        return;
    }
    visit_anonymous(expr, ctx);
}

fn visit_anonymous(expr: &Expression, ctx: &mut Ctx<'_>) {
    match expr {
        Expression::AnonymousComponent { meta, id, is_parallel, params, signals, .. } => {
            let covered = *is_parallel || ctx.parallel_templates.contains(id);
            if !covered {
                warn("(anonymous)", id, meta, ctx);
            }
            for arg in params.iter().chain(signals.iter()) {
                visit_anonymous(arg, ctx);
            }
        }
        Expression::ParallelOp { rhe, .. } => visit_anonymous(rhe, ctx),
        Expression::InfixOp { lhe, rhe, .. } => {
            visit_anonymous(lhe, ctx);
            visit_anonymous(rhe, ctx);
        }
        Expression::PrefixOp { rhe, .. } => visit_anonymous(rhe, ctx),
        Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
            visit_anonymous(cond, ctx);
            visit_anonymous(if_true, ctx);
            visit_anonymous(if_false, ctx);
        }
        Expression::Call { args, .. } => {
            for arg in args {
                visit_anonymous(arg, ctx);
            }
        }
        Expression::ArrayInLine { values, .. } | Expression::Tuple { values, .. } => {
            for value in values {
                visit_anonymous(value, ctx);
            }
        }
        Expression::Variable { access, .. } => {
            for acc in access {
                if let Access::ArrayAccess(index) = acc {
                    visit_anonymous(index, ctx);
                }
            }
        }
        Expression::Number(_, _) => {}
    }
}

fn contains_anonymous(expr: &Expression) -> bool {
    match expr {
        Expression::AnonymousComponent { .. } => true,
        Expression::ParallelOp { rhe, .. } => contains_anonymous(rhe),
        Expression::InfixOp { lhe, rhe, .. } => contains_anonymous(lhe) || contains_anonymous(rhe),
        Expression::PrefixOp { rhe, .. } => contains_anonymous(rhe),
        Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
            contains_anonymous(cond) || contains_anonymous(if_true) || contains_anonymous(if_false)
        }
        Expression::Call { args, .. } => args.iter().any(contains_anonymous),
        Expression::ArrayInLine { values, .. } | Expression::Tuple { values, .. } => {
            values.iter().any(contains_anonymous)
        }
        Expression::Variable { access, .. } => access
            .iter()
            .any(|acc| matches!(acc, Access::ArrayAccess(index) if contains_anonymous(index))),
        Expression::Number(_, _) => false,
    }
}

fn component_reads(expr: &Expression) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_components(expr, &mut names);
    names
}

fn collect_components(expr: &Expression, names: &mut HashSet<String>) {
    match expr {
        Expression::Variable { name, access, .. } => {
            if has_component_access(access) {
                names.insert(name.clone());
            }
            for acc in access {
                if let Access::ArrayAccess(index) = acc {
                    collect_components(index, names);
                }
            }
        }
        Expression::InfixOp { lhe, rhe, .. } => {
            collect_components(lhe, names);
            collect_components(rhe, names);
        }
        Expression::PrefixOp { rhe, .. } => collect_components(rhe, names),
        Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
            collect_components(cond, names);
            collect_components(if_true, names);
            collect_components(if_false, names);
        }
        Expression::ParallelOp { rhe, .. } => collect_components(rhe, names),
        Expression::Call { args, .. } => {
            for arg in args {
                collect_components(arg, names);
            }
        }
        Expression::AnonymousComponent { params, signals, .. } => {
            for arg in params.iter().chain(signals.iter()) {
                collect_components(arg, names);
            }
        }
        Expression::ArrayInLine { values, .. } | Expression::Tuple { values, .. } => {
            for value in values {
                collect_components(value, names);
            }
        }
        Expression::Number(_, _) => {}
    }
}

fn signal_names(expr: &Expression) -> HashSet<String> {
    let mut names = HashSet::new();
    collect_signals(expr, &mut names);
    names
}

fn collect_signals(expr: &Expression, names: &mut HashSet<String>) {
    match expr {
        Expression::Variable { name, access, .. } => {
            if !has_component_access(access) {
                names.insert(name.clone());
            }
            for acc in access {
                if let Access::ArrayAccess(index) = acc {
                    collect_signals(index, names);
                }
            }
        }
        Expression::InfixOp { lhe, rhe, .. } => {
            collect_signals(lhe, names);
            collect_signals(rhe, names);
        }
        Expression::PrefixOp { rhe, .. } => collect_signals(rhe, names),
        Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
            collect_signals(cond, names);
            collect_signals(if_true, names);
            collect_signals(if_false, names);
        }
        Expression::ParallelOp { rhe, .. } => collect_signals(rhe, names),
        Expression::Call { args, .. } => {
            for arg in args {
                collect_signals(arg, names);
            }
        }
        Expression::AnonymousComponent { params, signals, .. } => {
            for arg in params.iter().chain(signals.iter()) {
                collect_signals(arg, names);
            }
        }
        Expression::ArrayInLine { values, .. } | Expression::Tuple { values, .. } => {
            for value in values {
                collect_signals(value, names);
            }
        }
        Expression::Number(_, _) => {}
    }
}

fn access_component_reads(access: &[Access]) -> HashSet<String> {
    let mut names = HashSet::new();
    for acc in access {
        if let Access::ArrayAccess(index) = acc {
            names.extend(component_reads(index));
        }
    }
    names
}

fn access_signal_names(access: &[Access]) -> HashSet<String> {
    let mut names = HashSet::new();
    for acc in access {
        if let Access::ArrayAccess(index) = acc {
            names.extend(signal_names(index));
        }
    }
    names
}

fn has_component_access(access: &[Access]) -> bool {
    access.iter().any(|acc| matches!(acc, Access::ComponentAccess(_)))
}

/// True when running `template` on its own witness thread is cheaper than
/// joining that thread. Leaf comparators and templates built only from them
/// are not.
fn worth_a_thread(template: &str, ctx: &mut Ctx<'_>) -> bool {
    if let Some(known) = ctx.cost.get(template) {
        return *known;
    }
    if !ctx.visiting.insert(template.to_string()) {
        // A cycle of templates is a real subcircuit, not a comparator.
        return true;
    }
    let callees = ctx.templates.get(template).map(|definition| callee_names(definition.get_body()));
    let worth = if is_leaf_cheap(template) {
        false
    } else if is_leaf_expensive(template) {
        true
    } else if let Some(callees) = callees {
        callees.iter().any(|callee| worth_a_thread(callee, ctx))
    } else {
        // No body: keep the warning. Known-cheap leaves are handled above.
        true
    };
    ctx.visiting.remove(template);
    ctx.cost.insert(template.to_string(), worth);
    worth
}

fn is_leaf_cheap(template: &str) -> bool {
    matches!(
        template,
        "IsZero"
            | "IsEqual"
            | "LessThan"
            | "GreaterThan"
            | "LessEqThan"
            | "GreaterEqThan"
            | "Num2Bits"
            | "Num2Bits_strict"
            | "Bits2Num"
            | "Bits2Num_strict"
            | "AND"
            | "OR"
            | "XOR"
            | "NAND"
            | "NOR"
            | "NOT"
            | "Mux1"
            | "Mux2"
            | "Mux3"
            | "MultiMux1"
            | "MultiMux2"
            | "MultiMux3"
            | "BabyAdd"
            | "BabyDbl"
            | "Sign"
            | "CompConstant"
            | "AliasCheck"
            | "QuinSelector"
    )
}

fn is_leaf_expensive(template: &str) -> bool {
    matches!(
        template,
        "Poseidon" | "PoseidonEx" | "EscalarMulFix" | "EscalarMulAny" | "EscalarMul" | "BabyPbk"
    )
}

fn callee_names(stmt: &Statement) -> Vec<String> {
    let mut names = Vec::new();
    let mut components = HashSet::new();
    collect_callees(stmt, &mut components, &mut names);
    names
}

fn collect_callees(stmt: &Statement, components: &mut HashSet<String>, names: &mut Vec<String>) {
    match stmt {
        Statement::Block { stmts, .. }
        | Statement::InitializationBlock { initializations: stmts, .. } => {
            for stmt in stmts {
                collect_callees(stmt, components, names);
            }
        }
        Statement::While { stmt, .. } => collect_callees(stmt, components, names),
        Statement::IfThenElse { if_case, else_case, .. } => {
            collect_callees(if_case, components, names);
            if let Some(else_case) = else_case {
                collect_callees(else_case, components, names);
            }
        }
        Statement::Declaration { xtype, name, dimensions, .. } => {
            if matches!(xtype, VariableType::Component) {
                components.insert(name.clone());
            }
            for dim in dimensions {
                collect_anonymous(dim, names);
            }
        }
        Statement::Substitution { var, access, rhe, .. } => {
            // `c = Foo()` instantiates a component. `out <== helper()` is a
            // function call and does not make the template expensive.
            if components.contains(var) && !has_component_access(access) {
                if let Some((_, _, id)) = call_info(rhe) {
                    names.push(id);
                }
            }
            collect_anonymous(rhe, names);
        }
        Statement::MultiSubstitution { lhe, rhe, .. } => {
            collect_anonymous(lhe, names);
            collect_anonymous(rhe, names);
        }
        Statement::ConstraintEquality { lhe, rhe, .. } => {
            collect_anonymous(lhe, names);
            collect_anonymous(rhe, names);
        }
        Statement::Return { value, .. } | Statement::Assert { arg: value, .. } => {
            collect_anonymous(value, names);
        }
        Statement::LogCall { args, .. } => {
            for arg in args {
                if let LogArgument::LogExp(expr) = arg {
                    collect_anonymous(expr, names);
                }
            }
        }
    }
}

fn collect_anonymous(expr: &Expression, names: &mut Vec<String>) {
    match expr {
        Expression::AnonymousComponent { id, params, signals, .. } => {
            names.push(id.clone());
            for arg in params.iter().chain(signals.iter()) {
                collect_anonymous(arg, names);
            }
        }
        Expression::ParallelOp { rhe, .. } => collect_anonymous(rhe, names),
        Expression::InfixOp { lhe, rhe, .. } => {
            collect_anonymous(lhe, names);
            collect_anonymous(rhe, names);
        }
        Expression::PrefixOp { rhe, .. } => collect_anonymous(rhe, names),
        Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
            collect_anonymous(cond, names);
            collect_anonymous(if_true, names);
            collect_anonymous(if_false, names);
        }
        Expression::Call { args, .. } => {
            for arg in args {
                collect_anonymous(arg, names);
            }
        }
        Expression::ArrayInLine { values, .. } | Expression::Tuple { values, .. } => {
            for value in values {
                collect_anonymous(value, names);
            }
        }
        Expression::Variable { access, .. } => {
            for acc in access {
                if let Access::ArrayAccess(index) = acc {
                    collect_anonymous(index, names);
                }
            }
        }
        Expression::Number(_, _) => {}
    }
}

fn warn(name: &str, template: &str, meta: &Meta, ctx: &mut Ctx<'_>) {
    if !worth_a_thread(template, ctx) {
        return;
    }
    if !ctx.seen.insert((meta.start, meta.end)) {
        return;
    }
    let mut report = Report::warning(
        format!(
            "Component `{name}` (`{template}`) is not marked `parallel`, but its witness can overlap other work."
        ),
        ReportCode::MissingParallel,
    );
    add_meta(&mut report, meta, "Add `parallel` on this instantiation.".to_string());
    report.add_note(
        "Declare `parallel` here or on the template. The keyword does not change the constraints. If this output is read in the same loop, read it in a later loop so the calls overlap.".to_string(),
    );
    ctx.reports.push(report);
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

    fn reports_for(src: &str) -> ReportCollection {
        reports_for_templates(src, &HashSet::new())
    }

    fn reports_for_templates(src: &str, parallel_templates: &HashSet<String>) -> ReportCollection {
        let definition = parse_definition(src).expect("template should parse");
        let Definition::Template { body, .. } = definition else {
            panic!("expected a template");
        };
        find_missing_parallel(&body, parallel_templates, &HashMap::new())
    }

    #[test]
    fn independent_loop_without_parallel_is_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component chunk[n];
                for (var i = 0; i < n; i++) {
                    chunk[i] = Poseidon(1);
                    chunk[i].inputs[0] <== in[i];
                    out[i] <== chunk[i].out;
                }
            }
        "#;
        let reports = reports_for(src);
        assert_eq!(reports.len(), 1);
        assert!(reports[0].message().contains("chunk"));
        assert!(reports[0].message().contains("Poseidon"));
        assert_eq!(reports[0].id(), "CS0021");
    }

    #[test]
    fn comparator_loop_is_not_reported() {
        let src = r#"
            template T(n) {
                signal input a[n];
                signal input b[n];
                signal output out[n];
                component eq[n];
                for (var i = 0; i < n; i++) {
                    eq[i] = IsEqual();
                    eq[i].in[0] <== a[i];
                    eq[i].in[1] <== b[i];
                    out[i] <== eq[i].out;
                }
            }
        "#;
        assert!(reports_for(src).is_empty());
    }

    #[test]
    fn wrapper_around_a_comparator_is_not_reported() {
        let check = r#"
            template Check() {
                signal input a;
                signal input b;
                signal output out;
                component eq;
                eq = IsEqual();
                eq.in[0] <== a;
                eq.in[1] <== b;
                out <== eq.out;
            }
        "#;
        let caller = r#"
            template T(n) {
                signal input a[n];
                signal input b[n];
                signal output out[n];
                component check[n];
                for (var i = 0; i < n; i++) {
                    check[i] = Check();
                    check[i].a <== a[i];
                    check[i].b <== b[i];
                    out[i] <== check[i].out;
                }
            }
        "#;
        let definition = parse_definition(check).expect("wrapper should parse");
        let Definition::Template {
            name, args, arg_location, body, parallel, is_custom_gate, ..
        } = definition
        else {
            panic!("expected a template");
        };
        let mut elem_id = 0;
        let check = TemplateData::new(
            name,
            0,
            body,
            args.len(),
            args,
            arg_location,
            &mut elem_id,
            parallel,
            is_custom_gate,
        );
        let mut templates = HashMap::new();
        templates.insert(check.get_name().to_string(), check);
        let caller = parse_definition(caller).expect("caller should parse");
        let Definition::Template { body, .. } = caller else {
            panic!("expected a template");
        };
        assert!(find_missing_parallel(&body, &HashSet::new(), &templates).is_empty());
    }

    #[test]
    fn function_call_does_not_make_a_comparator_expensive() {
        let check = r#"
            template Check() {
                signal input a;
                signal output out;
                component eq;
                eq = IsEqual();
                eq.in[0] <== a;
                eq.in[1] <== helper();
                out <== eq.out;
            }
        "#;
        let caller = r#"
            template T(n) {
                signal input a[n];
                signal output out[n];
                component check[n];
                for (var i = 0; i < n; i++) {
                    check[i] = Check();
                    check[i].a <== a[i];
                    out[i] <== check[i].out;
                }
            }
        "#;
        let definition = parse_definition(check).expect("wrapper should parse");
        let Definition::Template {
            name, args, arg_location, body, parallel, is_custom_gate, ..
        } = definition
        else {
            panic!("expected a template");
        };
        let mut elem_id = 0;
        let check = TemplateData::new(
            name,
            0,
            body,
            args.len(),
            args,
            arg_location,
            &mut elem_id,
            parallel,
            is_custom_gate,
        );
        let mut templates = HashMap::new();
        templates.insert(check.get_name().to_string(), check);
        let caller = parse_definition(caller).expect("caller should parse");
        let Definition::Template { body, .. } = caller else {
            panic!("expected a template");
        };
        assert!(find_missing_parallel(&body, &HashSet::new(), &templates).is_empty());
    }

    #[test]
    fn wrapper_around_poseidon_is_reported() {
        let hash = r#"
            template HashOne() {
                signal input in;
                signal output out;
                component h;
                h = Poseidon(1);
                h.inputs[0] <== in;
                out <== h.out;
            }
        "#;
        let caller = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component hash[n];
                for (var i = 0; i < n; i++) {
                    hash[i] = HashOne();
                    hash[i].in <== in[i];
                    out[i] <== hash[i].out;
                }
            }
        "#;
        let definition = parse_definition(hash).expect("hash wrapper should parse");
        let Definition::Template {
            name, args, arg_location, body, parallel, is_custom_gate, ..
        } = definition
        else {
            panic!("expected a template");
        };
        let mut elem_id = 0;
        let hash = TemplateData::new(
            name,
            0,
            body,
            args.len(),
            args,
            arg_location,
            &mut elem_id,
            parallel,
            is_custom_gate,
        );
        let mut templates = HashMap::new();
        templates.insert(hash.get_name().to_string(), hash);
        let caller = parse_definition(caller).expect("caller should parse");
        let Definition::Template { body, .. } = caller else {
            panic!("expected a template");
        };
        let reports = find_missing_parallel(&body, &HashSet::new(), &templates);
        assert_eq!(reports.len(), 1);
        assert!(reports[0].message().contains("HashOne"));
    }

    #[test]
    fn parallel_loop_is_not_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component chunk[n];
                for (var i = 0; i < n; i++) {
                    chunk[i] = parallel Poseidon(1);
                    chunk[i].inputs[0] <== in[i];
                }
                for (var i = 0; i < n; i++) {
                    out[i] <== chunk[i].out;
                }
            }
        "#;
        assert!(reports_for(src).is_empty());
    }

    #[test]
    fn template_level_parallel_is_not_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                component chunk[n];
                for (var i = 0; i < n; i++) {
                    chunk[i] = Poseidon(1);
                    chunk[i].inputs[0] <== in[i];
                    out[i] <== chunk[i].out;
                }
            }
        "#;
        let mut parallel = HashSet::new();
        parallel.insert("Poseidon".to_string());
        assert!(reports_for_templates(src, &parallel).is_empty());
    }

    #[test]
    fn loop_carried_chain_is_not_reported() {
        let src = r#"
            template T(n) {
                signal input in[n][2];
                signal output out[2];
                component adder[n];
                signal acc[n + 1][2];
                acc[0][0] <== in[0][0];
                acc[0][1] <== in[0][1];
                for (var i = 0; i < n; i++) {
                    adder[i] = BabyAdd();
                    adder[i].x1 <== acc[i][0];
                    adder[i].y1 <== acc[i][1];
                    adder[i].x2 <== in[i][0];
                    adder[i].y2 <== in[i][1];
                    acc[i + 1][0] <== adder[i].xout;
                    acc[i + 1][1] <== adder[i].yout;
                }
                out[0] <== acc[n][0];
                out[1] <== acc[n][1];
            }
        "#;
        assert!(reports_for(src).is_empty());
    }

    #[test]
    fn chain_through_an_intermediate_signal_is_not_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out;
                component step[n];
                signal acc[n + 1];
                signal tmp[n];
                acc[0] <== 0;
                for (var i = 0; i < n; i++) {
                    step[i] = Worker();
                    step[i].in <== acc[i];
                    tmp[i] <== step[i].out;
                    acc[i + 1] <== tmp[i] + in[i];
                }
                out <== acc[n];
            }
        "#;
        assert!(reports_for(src).is_empty());
    }

    #[test]
    fn overlapping_siblings_are_reported() {
        let src = r#"
            template T() {
                signal input x;
                signal input y;
                signal output out;
                component left;
                component right;
                component join;
                left = EscalarMulFix();
                right = EscalarMulAny();
                left.e <== x;
                right.e <== y;
                join = BabyAdd();
                join.x1 <== left.out;
                join.x2 <== right.out;
                out <== join.xout;
            }
        "#;
        let reports = reports_for(src);
        assert_eq!(
            reports.len(),
            2,
            "{:?}",
            reports.iter().map(|r| r.message()).collect::<Vec<_>>()
        );
        let names: Vec<_> = reports.iter().map(|r| r.message().clone()).collect();
        assert!(names.iter().any(|m| m.contains("left") && m.contains("EscalarMulFix")));
        assert!(names.iter().any(|m| m.contains("right") && m.contains("EscalarMulAny")));
    }

    #[test]
    fn immediate_input_is_not_reported() {
        let src = r#"
            template T() {
                signal input x;
                signal output out;
                component bits;
                component mul;
                bits = Num2Bits(253);
                bits.in <== x;
                mul = EscalarMulAny();
                mul.e <== bits.out;
                out <== mul.out;
            }
        "#;
        assert!(reports_for(src).is_empty());
    }

    #[test]
    fn one_parallel_sibling_reports_only_the_other() {
        let src = r#"
            template T() {
                signal input x;
                signal input y;
                signal output out;
                component left;
                component right;
                left = parallel Worker();
                right = Worker();
                left.in <== x;
                right.in <== y;
                out <== left.out + right.out;
            }
        "#;
        let reports = reports_for(src);
        assert_eq!(reports.len(), 1);
        assert!(reports[0].message().contains("right"));
    }

    #[test]
    fn component_live_across_a_loop_is_reported() {
        let src = r#"
            template T(n) {
                signal input keys[2];
                signal input cards[n][4];
                signal output out;
                component pubs;
                component rows[n];
                component fold;
                pubs = HashPublicKeys();
                pubs.publicKeys <== keys;
                for (var i = 0; i < n; i++) {
                    rows[i] = parallel HashCiphertexts();
                    rows[i].ciphertext <== cards[i];
                }
                fold = Poseidon(1);
                fold.inputs[0] <== pubs.out;
                out <== fold.out;
            }
        "#;
        let reports = reports_for(src);
        assert_eq!(
            reports.len(),
            1,
            "{:?}",
            reports.iter().map(|r| r.message()).collect::<Vec<_>>()
        );
        assert!(reports[0].message().contains("pubs"));
    }

    #[test]
    fn anonymous_component_in_a_loop_is_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out[n];
                for (var i = 0; i < n; i++) {
                    out[i] <== Worker()(in[i]);
                }
            }
        "#;
        let reports = reports_for(src);
        assert_eq!(reports.len(), 1);
        assert!(reports[0].message().contains("Worker"));
    }

    #[test]
    fn component_waiting_on_a_loop_is_not_reported() {
        let src = r#"
            template T(n) {
                signal input in[n];
                signal output out;
                component fold;
                component rows[n];
                fold = Poseidon(1);
                for (var i = 0; i < n; i++) {
                    rows[i] = parallel Worker();
                    rows[i].in <== in[i];
                }
                fold.inputs[0] <== rows[0].out;
                out <== fold.out;
            }
        "#;
        assert!(reports_for(src).is_empty());
    }

    #[test]
    fn anonymous_component_outside_a_loop_is_not_reported() {
        let src = r#"
            template T() {
                signal input in;
                signal output out;
                out <== Worker()(in);
            }
        "#;
        assert!(reports_for(src).is_empty());
    }
}
