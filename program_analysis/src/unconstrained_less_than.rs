use std::collections::{HashMap, HashSet};
use std::fmt;

use log::{debug, trace};

use num_bigint::BigInt;
use program_structure::cfg::Cfg;
use program_structure::ir::degree_meta::DegreeMeta;
use program_structure::ir::value_meta::{ValueMeta, ValueReduction};
use program_structure::ir::variable_meta::VariableMeta;
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::ir::*;

use crate::taint_analysis::{run_taint_analysis, TaintAnalysis};

/// Templates whose outputs are checked outside the circuit (public hash /
/// commitment binding). Signals that flow into these are treated as
/// externally constrained for LessThan bit-range purposes.
const HASH_TEMPLATES: &[&str] = &[
    "Poseidon",
    "PoseidonEx",
    "Pedersen",
    "MiMC7",
    "MultiMiMC7",
    "MiMCSponge",
    "MiMCFeistel",
    "SMTHash1",
    "SMTHash2",
    "BabyPbk",
];

pub struct UnconstrainedLessThanWarning {
    value: Expression,
    bit_sizes: Vec<(Meta, Expression)>,
}
impl UnconstrainedLessThanWarning {
    fn primary_meta(&self) -> &Meta {
        self.value.meta()
    }

    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Inputs to `LessThan` need to be constrained to ensure that they are non-negative"
                .to_string(),
            ReportCode::UnconstrainedLessThan,
        );
        if let Some(file_id) = self.primary_meta().file_id {
            report.add_primary(
                self.primary_meta().file_location(),
                file_id,
                format!("`{}` needs to be constrained to ensure that it is <= p/2.", self.value),
            );
            for (meta, size) in self.bit_sizes {
                report.add_secondary(
                    meta.file_location(),
                    file_id,
                    Some(format!("`{}` is constrained to `{}` bits here.", self.value, size)),
                );
            }
        }
        report
    }
}

#[derive(Eq, PartialEq, Hash)]
struct VariableAccess {
    pub var: VariableName,
    pub access: Vec<AccessType>,
}

impl VariableAccess {
    fn new(var: &VariableName, access: &[AccessType]) -> Self {
        // We disregard the version to make sure accesses are not order dependent.
        VariableAccess { var: var.without_version(), access: access.to_vec() }
    }
}

/// Tracks component instantiations `var = T(...)` where then template `T` is
/// either `LessThan` or `Num2Bits`.
enum Component {
    LessThan,
    Num2Bits { bit_size: Box<Expression> },
}

impl Component {
    fn less_than() -> Self {
        Self::LessThan
    }

    fn num_2_bits(bit_size: &Expression) -> Self {
        Self::Num2Bits { bit_size: Box::new(bit_size.clone()) }
    }
}

/// Tracks component input signal initializations on the form `T.in <== input`
/// where `T` is either `LessThan` or `Num2Bits`.
enum ComponentInput {
    LessThan { value: Box<Expression> },
    Num2Bits { value: Box<Expression>, bit_size: Box<Expression> },
}

impl ComponentInput {
    fn less_than(value: &Expression) -> Self {
        Self::LessThan { value: Box::new(value.clone()) }
    }

    fn num_2_bits(value: &Expression, bit_size: &Expression) -> Self {
        Self::Num2Bits { value: Box::new(value.clone()), bit_size: Box::new(bit_size.clone()) }
    }
}

/// Tracks constraints for a single input to `LessThan`.
#[derive(Default)]
struct ConstraintData {
    /// Input to `LessThan`.
    pub less_than: Vec<Meta>,
    /// Input to `Num2Bits`.
    pub num_2_bits: Vec<Meta>,
    /// Size constraints enforced by `Num2Bits`.
    pub bit_sizes: Vec<Expression>,
}

/// The `LessThan` template from Circomlib does not constrain the individual
/// inputs to the input size `n` bits, or to be positive. If the inputs are
/// allowed to be greater than p/2 it is possible to find field elements `a` and
/// `b` such that
///
///   1. `a > b` either as unsigned integers, or as signed elements in GF(p),
///   2. lt = LessThan(n),
///   3. lt.in[0] = a,
///   4. lt.in[1] = b, and
///   5. lt.out = 1
///
/// This analysis pass looks for instantiations of `LessThan` where the inputs
/// are not constrained to be <= p/2 using `Num2Bits`.
pub fn find_unconstrained_less_than(cfg: &Cfg) -> ReportCollection {
    debug!("running unconstrained less-than analysis pass");
    let taint_analysis = run_taint_analysis(cfg);
    let hash_components = collect_hash_components(cfg);
    let safe_signals = collect_safe_signals(cfg, &taint_analysis, &hash_components);
    let mut components = HashMap::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            update_components(stmt, &mut components);
        }
    }
    let mut inputs = Vec::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            update_inputs(stmt, &components, &mut inputs);
        }
    }
    let mut constraints = HashMap::<Expression, ConstraintData>::new();
    for input in inputs {
        match input {
            ComponentInput::LessThan { value } => {
                let entry = constraints.entry(*value.clone()).or_default();
                entry.less_than.push(value.meta().clone());
            }
            ComponentInput::Num2Bits { value, bit_size, .. } => {
                let entry = constraints.entry(*value.clone()).or_default();
                entry.num_2_bits.push(value.meta().clone());
                entry.bit_sizes.push(*bit_size.clone());
            }
        }
    }

    // Generate a report for each input to `LessThan` where the input size is
    // not constrained to be positive using `Num2Bits`.
    let mut reports = ReportCollection::new();
    let max_value = BigInt::from(cfg.constants().prime_size() - 1);
    for (value, data) in constraints {
        // Check if the the value is used as input for `LessThan`.
        if data.less_than.is_empty() {
            continue;
        }
        // Skip values that are fixed, loop locals, template inputs (and
        // intermediates derived from them), component outputs, or bound via
        // hashing/commitments managed externally.
        if is_safe_less_than_input(&value, cfg, &taint_analysis, &safe_signals) {
            continue;
        }
        // Check if the value is constrained to be positive.
        let mut is_positive = false;
        for bit_size in &data.bit_sizes {
            if let Some(ValueReduction::FieldElement { value }) = bit_size.value() {
                if value < &max_value {
                    is_positive = true;
                    break;
                }
            }
        }
        if is_positive {
            continue;
        }
        // We failed to prove that the input is positive. Generate a report.
        reports.push(build_report(&value, &data));
    }
    debug!("{} new reports generated", reports.len());
    reports
}

/// Collect signals that are safe LessThan sources: template inputs, component
/// outputs, hash-bound signals, constants/template-params, and any signal
/// assigned only from other safe sources (e.g. `twoN <== nActual * 2`).
fn collect_safe_signals(
    cfg: &Cfg,
    taint: &TaintAnalysis,
    hash_components: &HashSet<VariableName>,
) -> HashSet<VariableName> {
    use AssignOp::*;
    use Expression::*;
    use SignalType::*;
    use Statement::*;
    use VariableType::*;

    let mut safe = HashSet::new();

    // Seed with inputs, components, and hash-bound signals.
    for (name, decl) in cfg.declarations().iter() {
        match decl.variable_type() {
            Signal(Input, _) | Component | AnonymousComponent => {
                safe.insert(name.clone());
            }
            Signal(_, _) if flows_into_hash(name, taint, hash_components) => {
                safe.insert(name.clone());
            }
            _ => {}
        }
    }

    // Propagate through signal assignments from safe-only expressions.
    let mut changed = true;
    while changed {
        changed = false;
        for basic_block in cfg.iter() {
            for stmt in basic_block.iter() {
                let Substitution { meta, var, op, rhe } = stmt else {
                    continue;
                };
                if !matches!(op, AssignConstraintSignal | AssignSignal) {
                    continue;
                }
                // Only track ordinary signal assignments, not component updates.
                if !meta.type_knowledge().is_signal() {
                    continue;
                }
                let value = if let Update { rhe, .. } = rhe { rhe.as_ref() } else { rhe };
                if expression_from_safe_sources(value, cfg, taint, &safe) && safe.insert(var.clone())
                {
                    trace!("signal `{var:?}` derived from externally constrained sources");
                    changed = true;
                }
            }
        }
    }
    safe
}

/// Returns true if every variable in `value` is a safe LessThan source.
fn expression_from_safe_sources(
    value: &Expression,
    cfg: &Cfg,
    taint: &TaintAnalysis,
    safe_signals: &HashSet<VariableName>,
) -> bool {
    if value.is_constant() {
        return true;
    }
    if value.degree().map(|range| range.is_constant()).unwrap_or(false) {
        return true;
    }
    let vars = value.variables_read().map(|var| var.name().clone()).collect::<HashSet<_>>();
    !vars.is_empty()
        && vars.iter().all(|name| variable_is_safe_source(name, cfg, taint, safe_signals))
}

/// Collect component variables that instantiate a hash/commitment template.
fn collect_hash_components(cfg: &Cfg) -> HashSet<VariableName> {
    use AssignOp::*;
    use Expression::*;
    use Statement::*;

    let mut hash_components = HashSet::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            let Substitution { meta, var, op: AssignLocalOrComponent, rhe } = stmt else {
                continue;
            };
            if meta.type_knowledge().is_local() || meta.type_knowledge().is_signal() {
                continue;
            }
            let rhe = if let Update { rhe, .. } = rhe { rhe.as_ref() } else { rhe };
            if let Call { name, .. } = rhe {
                if HASH_TEMPLATES.contains(&name.as_str()) {
                    trace!("hash/commitment component `{var:?}` (`{name}`) found");
                    hash_components.insert(var.clone());
                    hash_components.insert(var.without_version());
                }
            }
        }
    }
    hash_components
}

fn update_components(stmt: &Statement, components: &mut HashMap<VariableAccess, Component>) {
    use AssignOp::*;
    use Statement::*;
    use Expression::*;
    if let Substitution { meta, var, op: AssignLocalOrComponent, rhe, .. } = stmt {
        // If the variable `var` is declared as a local variable or signal, we exit early.
        if meta.type_knowledge().is_local() || meta.type_knowledge().is_signal() {
            return;
        }
        // If this is an assignment on the form `var[i] = T(...)` we need to store the access and obtain the RHS.
        let (rhe, access) = if let Update { access, rhe, .. } = rhe {
            (rhe.as_ref(), access.clone())
        } else {
            (rhe, Vec::new())
        };
        if let Call { name: component_name, args, .. } = rhe {
            if component_name == "LessThan" && args.len() == 1 {
                // We assume this is the `LessThan` circuit from Circomlib.
                trace!(
                    "`LessThan` template instantiation `{var}{}` found",
                    vec_to_display(&access, "")
                );
                let component = VariableAccess::new(var, &access);
                components.insert(component, Component::less_than());
            } else if component_name == "Num2Bits" && args.len() == 1 {
                // We assume this is the `Num2Bits` circuit from Circomlib.
                trace!(
                    "`LessThan` template instantiation `{var}{}` found",
                    vec_to_display(&access, "")
                );
                let component = VariableAccess::new(var, &access);
                components.insert(component, Component::num_2_bits(&args[0]));
            }
        }
    }
}

fn update_inputs(
    stmt: &Statement,
    components: &HashMap<VariableAccess, Component>,
    inputs: &mut Vec<ComponentInput>,
) {
    use AssignOp::*;
    use Statement::*;
    use Expression::*;
    use AccessType::*;
    if let Substitution {
        var, op: AssignConstraintSignal, rhe: Update { access, rhe, .. }, ..
    } = stmt
    {
        // If this is a `Num2Bits` input signal assignment, the input signal
        // access would be the last element of the `access` vector.
        let mut component_access = access.clone();
        let signal_access = component_access.pop();
        let component = VariableAccess::new(var, &component_access);
        if let Some(Component::Num2Bits { bit_size, .. }) = components.get(&component) {
            let Some(ComponentAccess(signal_name)) = signal_access else {
                return;
            };
            if signal_name != "in" {
                return;
            }
            trace!("`Num2Bits` input signal assignment `{rhe}` found");
            inputs.push(ComponentInput::num_2_bits(rhe, bit_size));
        }

        // If this is a `LessThan` input signal assignment, the input index
        // access would be the last element, and the input signal access
        // would be the next to last element of the `access` vector.
        let mut component_access = access.clone();
        let index_access = component_access.pop();
        let signal_access = component_access.pop();
        let component = VariableAccess::new(var, &component_access);
        if let Some(Component::LessThan { .. }) = components.get(&component) {
            let (Some(ComponentAccess(signal_name)), Some(ArrayAccess(_))) =
                (signal_access, index_access)
            else {
                return;
            };
            if signal_name != "in" {
                return;
            }
            trace!("`LessThan` input signal assignment `{rhe}` found");
            inputs.push(ComponentInput::less_than(rhe));
        }
    }
}

/// Returns true if a LessThan input does not need an explicit Num2Bits
/// non-negativity constraint in this template.
#[must_use]
fn is_safe_less_than_input(
    value: &Expression,
    cfg: &Cfg,
    taint: &TaintAnalysis,
    safe_signals: &HashSet<VariableName>,
) -> bool {
    expression_from_safe_sources(value, cfg, taint, safe_signals)
}

fn variable_is_safe_source(
    name: &VariableName,
    cfg: &Cfg,
    taint: &TaintAnalysis,
    safe_signals: &HashSet<VariableName>,
) -> bool {
    use SignalType::*;
    use VariableType::*;

    if safe_signals.contains(name) || safe_signals.contains(&name.without_version()) {
        return true;
    }
    if cfg.parameters().contains(name) || cfg.parameters().contains(&name.without_version()) {
        return true;
    }

    match lookup_var_type(cfg, name) {
        // Loop indices and other locals that do not depend on signals. (SSA
        // phi nodes often drop constant degree knowledge for induction vars.)
        Some(Local) => !is_tainted_by_signal(name, cfg, taint),
        // Template inputs are constrained by the caller / protocol.
        Some(Signal(Input, _)) => true,
        // Subcomponent outputs are constrained inside the callee.
        Some(Component | AnonymousComponent) => true,
        Some(Signal(Output | Intermediate, _)) => false,
        None => false,
    }
}

/// Look up a variable's type, including SSA-versioned locals.
///
/// `Cfg::get_type` strips versions before lookup, but local declarations are
/// stored under versioned keys after SSA conversion.
fn lookup_var_type<'a>(cfg: &'a Cfg, name: &VariableName) -> Option<&'a VariableType> {
    if let Some(var_type) = cfg.get_type(name) {
        return Some(var_type);
    }
    cfg.declarations().iter().find_map(|(key, decl)| {
        (key.name() == name.name() && key.suffix() == name.suffix())
            .then_some(decl.variable_type())
    })
}

fn is_tainted_by_signal(name: &VariableName, cfg: &Cfg, taint: &TaintAnalysis) -> bool {
    use VariableType::*;
    let sinks = HashSet::from([name.clone(), name.without_version()]);
    cfg.declarations().iter().any(|(source, decl)| {
        matches!(decl.variable_type(), Signal(_, _) | Component | AnonymousComponent)
            && taint.taints_any(source, &sinks)
    })
}

fn flows_into_hash(
    name: &VariableName,
    taint: &TaintAnalysis,
    hash_components: &HashSet<VariableName>,
) -> bool {
    if hash_components.is_empty() {
        return false;
    }
    taint.taints_any(name, hash_components)
        || taint.taints_any(&name.without_version(), hash_components)
}

#[must_use]
fn build_report(value: &Expression, data: &ConstraintData) -> Report {
    UnconstrainedLessThanWarning {
        value: value.clone(),
        bit_sizes: data.num_2_bits.iter().cloned().zip(data.bit_sizes.iter().cloned()).collect(),
    }
    .into_report()
}

#[must_use]
fn vec_to_display<T: fmt::Display>(elems: &[T], sep: &str) -> String {
    elems.iter().map(|elem| format!("{elem}")).collect::<Vec<String>>().join(sep)
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::{cfg::IntoCfg, constants::Curve};

    use super::*;

    #[test]
    fn test_unconstrained_less_than() {
        // Template inputs and intermediates derived from them are external.
        let src = r#"
            template Test(n) {
              signal input a;
              signal input b;
              signal small;
              signal large;
              signal output ok;

              small <== a;
              large <== b;

              component lt = LessThan(n);
              lt.in[0] <== small;
              lt.in[1] <== large;

              ok <== lt.out;
            }
        "#;
        validate_reports(src, 0);

        // Arithmetic over inputs (twoN <== n*2, sum <== a+b, gated <== e*in).
        let src = r#"
            template Test(n) {
              signal input nActual;
              signal twoN;
              signal output ok;

              twoN <== nActual * 2;
              component lt = LessThan(5);
              lt.in[0] <== 0;
              lt.in[1] <== twoN;
              ok <== lt.out;
            }
        "#;
        validate_reports(src, 0);

        let src = r#"
            template Test() {
              signal input a;
              signal input b;
              signal sum;
              signal output ok;

              sum <== a + b;
              component lt = LessThan(5);
              lt.in[0] <== sum;
              lt.in[1] <== 10;
              ok <== lt.out;
            }
        "#;
        validate_reports(src, 0);

        let src = r#"
            template Test() {
              signal input enabled;
              signal input in;
              signal gated;
              signal output ok;

              gated <== enabled * in;
              component lt = LessThan(8);
              lt.in[0] <== gated;
              lt.in[1] <== 10;
              ok <== lt.out;
            }
        "#;
        validate_reports(src, 0);

        // Fixed constants / template parameters do not need Num2Bits.
        let src = r#"
            template Test(n) {
              signal output ok;

              component lt = LessThan(8);
              lt.in[0] <== 3;
              lt.in[1] <== n + 1;

              ok <== lt.out;
            }
        "#;
        validate_reports(src, 0);

        // Loop induction variables are compile-time non-negative.
        let src = r#"
            template Test(n) {
              signal input vals[n];
              signal output out;
              component active[n];
              for (var i = 0; i < n; i++) {
                active[i] = LessThan(8);
                active[i].in[0] <== i;
                active[i].in[1] <== vals[i];
              }
              out <== active[0].out;
            }
        "#;
        validate_reports(src, 0);

        // Signals that flow into a hash/commitment are managed externally.
        let src = r#"
            template Test(n) {
              signal input a;
              signal mid;
              signal output ok;
              signal output h;

              mid <== a;
              component hash = Poseidon(1);
              hash.inputs[0] <== mid;

              component lt = LessThan(8);
              lt.in[0] <== mid;
              lt.in[1] <== 10;

              ok <== lt.out;
              h <== hash.out;
            }
        "#;
        validate_reports(src, 0);

        // A signal with no externally constrained derivation should still warn.
        let src = r#"
            template Test() {
              signal ghost;
              signal output ok;

              ghost <-- ghost + 1;
              component lt = LessThan(8);
              lt.in[0] <== ghost;
              lt.in[1] <== 10;
              ok <== lt.out;
            }
        "#;
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

        let reports = find_unconstrained_less_than(&cfg);
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
