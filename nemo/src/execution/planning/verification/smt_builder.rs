//! This module define the lowering for rules to smtlib,
//! as well as evaluating these lowerings

use core::ops::Range;
use std::collections::{HashMap, HashSet};
use std::i64;
use std::ops::{Add, Mul, Sub};

use smtlib::{
    Bool, Error, Int, SatResult, Solver, Storage, backend::z3_binary::Z3Binary, funs::Fun,
    prelude::*, terms::Dynamic,
};

use crate::nemo_physical::datavalues::DataValue;

use crate::execution::planning::normalization::{
    atom::{body::BodyAtom, head::HeadAtom},
    operation::Operation,
    rule::NormalizedRule,
    rule_annotation::NormalizedRuleAnnotation,
};

use crate::rule_model::components::{
    tag::Tag,
    term::{
        operation::operation_kind::OperationKind,
        primitive::{Primitive, variable::Variable},
    },
};

/// Lowers Datalog rules to smt represenation
#[derive(Debug)]
pub struct Lowering<'a> {
    st: &'a Storage,

    predicates_to_fun: HashMap<Tag, Fun<'a>>,
}

impl<'a> Lowering<'a> {
    /// Creates new instance of the lowering struct
    pub fn new(st: &'a Storage) -> Self {
        let predicates_to_fun = HashMap::<Tag, Fun<'a>>::new();
        Self {
            st,
            predicates_to_fun,
        }
    }

    /// Returns the smt function for the given predicate
    pub fn get_predicate_fun(&mut self, predicate: &Tag) -> &Fun<'a> {
        self.predicates_to_fun
            .get(predicate)
            .expect("predicate should be registered")
    }

    /// Constructs and declares the functions for the predicates
    pub fn build_predicate(
        &mut self,
        predicate: Tag,
        arity: usize,
        solver: &mut Solver<'a, Z3Binary>,
    ) -> Result<(), Error> {
        let arg_sort = (0..arity).map(|_| Int::sort()).collect();
        let fun = Fun::new(self.st, predicate.name(), arg_sort, Bool::sort());

        solver.declare_fun(&fun)?;
        self.predicates_to_fun.insert(predicate, fun);
        Ok(())
    }

    /// Constructs the body atom
    pub fn lower_body_atom(
        &mut self,
        body_atom: &BodyAtom,
        var_map: &'a HashMap<Variable, Int>,
    ) -> Result<Bool<'a>, Error> {
        let pred_fun = self.get_predicate_fun(&body_atom.predicate());

        let args: Vec<Dynamic> = body_atom
            .terms()
            .map(|term| var_map.get(term).expect("anon var not supported yet"))
            .map(|f| f.into_dynamic())
            .collect();

        pred_fun.call(&args)?.as_bool()
    }

    /// Constructs the head atom into smt representation
    pub fn lower_head_atom(
        &mut self,
        head_atom: &HeadAtom,
        var_map: &'a HashMap<Variable, Int>,
    ) -> Result<Bool<'a>, Error> {
        let args: Vec<Dynamic> = head_atom
            .terms()
            .map(|term| self.lower_primitive(term, var_map))
            .map(|f| f.into_dynamic())
            .collect();

        let pred_fun: &Fun<'_> = self.get_predicate_fun(&head_atom.predicate());
        pred_fun.call(&args)?.as_bool()
    }

    /// Converts primitive into smt representation, expects only variables and ground terms for now
    pub fn lower_primitive(
        &self,
        primitive: &Primitive,
        var_map: &HashMap<Variable, Int<'a>>,
    ) -> Int<'a> {
        match primitive {
            Primitive::Variable(variable) => *var_map.get(variable).expect("var not found in map"),
            Primitive::Ground(ground_term) => {
                Int::new(self.st, ground_term.value().to_i64_unchecked())
            }
        }
    }

    ///Converts rule annotation to smt representation
    pub fn lower_rule_annotation(
        &mut self,
        annotation: &NormalizedRuleAnnotation,
        var_map: &HashMap<Variable, Int<'a>>,
    ) -> Vec<Bool<'a>> {
        annotation
            .body()
            .iter()
            .map(|operation| {
                self.lower_operation(operation, var_map)
                    .expect("should work")
                    .as_bool()
                    .expect("please please please")
            })
            .collect()
    }

    /// Converts operation into smt representation
    pub fn lower_operation(
        &mut self,
        operation: &Operation,
        var_map: &HashMap<Variable, Int<'a>>,
    ) -> Result<Dynamic<'a>, Error> {
        match operation {
            Operation::Primitive(primitive) => Ok(self.lower_primitive(primitive, var_map).into()),
            Operation::Opreation { kind, subterms } => {
                self.lower_operation_kind(kind, subterms, var_map)
            }
        }
    }

    /// Converts operation kind into smt representation
    pub fn lower_operation_kind(
        &mut self,
        kind: &OperationKind,
        subterms: &Vec<Operation>,
        var_map: &HashMap<Variable, Int<'a>>,
    ) -> Result<Dynamic<'a>, Error> {
        // expect to only have two subterms
        let left = self.lower_operation(
            subterms.first().expect("invalid program component"),
            var_map,
        )?;
        let right =
            self.lower_operation(subterms.get(1).expect("invalid program component"), var_map)?;

        match kind {
            OperationKind::Equal => Ok(left._eq(right).into_dynamic()),
            OperationKind::Unequals => Ok(left._neq(right).into_dynamic()),
            OperationKind::NumericSum => Ok(left.as_int()?.add(right.as_int()?).into_dynamic()),
            OperationKind::NumericSubtraction => {
                Ok(left.as_int()?.sub(right.as_int()?).into_dynamic())
            }
            OperationKind::NumericProduct => Ok(left.as_int()?.mul(right.as_int()?).into_dynamic()),
            OperationKind::NumericDivision => Ok((left.as_int()? / right.as_int()?).into_dynamic()),
            OperationKind::NumericGreaterthaneq => {
                Ok(left.as_int()?.ge(right.as_int()?).into_dynamic())
            }
            OperationKind::NumericGreaterthan => {
                Ok(left.as_int()?.gt(right.as_int()?).into_dynamic())
            }
            OperationKind::NumericLessthaneq => {
                Ok(left.as_int()?.le(right.as_int()?).into_dynamic())
            }
            OperationKind::NumericLessthan => Ok(left.as_int()?.lt(right.as_int()?).into_dynamic()),
            _ => panic!("other operations not supported for now"),
        }
    }

    /// Lowers the restrictions on the frontier variables to the solver
    pub fn lower_restrictions(
        &self,
        restrictions: &HashMap<Variable, Range<i64>>,
        var_map: &HashMap<Variable, Int<'a>>,
        solver: &mut Solver<'a, Z3Binary>,
    ) {
        for (var, range) in restrictions {
            if let Some(int_var) = var_map.get(var) {
                let lower_bound = Int::new(self.st, range.start);
                let upper_bound = Int::new(self.st, range.end);

                // Assert the variable is within the bounds
                solver
                    .assert(int_var.ge(lower_bound))
                    .expect("failed asserting lower bound");
                solver
                    .assert(int_var.lt(upper_bound))
                    .expect("failed asserting upper bound");
            }
        }
    }

    /// Generates Smtlib code for rule
    pub fn lower_rule(
        &mut self,
        rule: &NormalizedRule,
        var_map: &'a HashMap<Variable, Int<'a>>,
        solver: &mut Solver<'a, Z3Binary>,
    ) -> Result<(), Error> {
        let body_atoms = rule.positive().iter().map(|atom| {
            self.lower_body_atom(atom, var_map)
                .expect("failed in lower rule")
        });

        for atom in body_atoms {
            solver.assert(atom).expect("failed in asserting atom");
        }

        let body_operations = rule.operations().iter().map(|op| {
            self.lower_operation(op, var_map)
                .expect("should work")
                .as_bool()
                .expect("please please please")
        });

        for op in body_operations {
            solver.assert(op).expect("failed in asserting op");
        }

        // might not be necessary
        /*let head_atoms: Vec<Bool<'_>> = rule.head().iter()
        .map(|atom| self.lower_head_atom(atom, var_map).expect("failed in lower rule"))
        .collect();*/

        // The negation of the conjunction of all of these has to be asserted, as we want to check whether the
        // assertion are satisfied
        for annotation in rule.annotations() {
            let lowered_ann = self.lower_rule_annotation(annotation, var_map);
            for ann in lowered_ann {
                solver.assert(ann).expect("failed asserting an annotation");
            }
        }
        Ok(())
    }
}

impl<'a> Lowering<'a> {
    /// Checks whether the given rule is satisfiable with the given annotations TODO: add current range restriction
    pub fn check_rule(
        rule: &NormalizedRule,
        restrictions: &HashMap<Variable, Range<i64>>,
    ) -> Result<bool, Error> {
        let st = Storage::new();
        let mut solver: Solver<'_, Z3Binary> =
            Solver::new(&st, Z3Binary::new("/usr/bin/z3").expect("bla")).expect("f");

        /*solver.set_logger((
            |cmd: Command<'_>| println!("> {cmd}"),
            |_cmd: Command<'_>, _: &str| (),
        ));*/

        let mut lowering = Lowering::new(&st);

        let var_map = lowering.build_var_map(&rule.variables().collect());

        // Generate the smt representation for all predicates in the rule
        let predicate_set: HashSet<(Tag, usize)> = rule.predicates().collect();
        for (predicate, arity) in predicate_set {
            lowering
                .build_predicate(predicate, arity, &mut solver)
                .expect("failed to build predicate");
        }

        lowering.lower_rule(rule, &var_map, &mut solver)?;

        lowering.lower_restrictions(restrictions, &var_map, &mut solver);

        // TODO: should probably check whether there exists a model not satisfying the annotations
        // What I mean by this -> There should be a seperate check to see whether the annotations are actually
        // "satisfied", e.g. for recursion "invariants" that they hold
        let result = solver.check_sat()?;
        match result {
            SatResult::Unsat => Ok(false),
            SatResult::Sat => {
                let model = solver.get_model().unwrap();
                //println!("{model}");
                Ok(true)
            }
            SatResult::Unknown => Ok(false),
        }
    }

    /// Builds a map of nemo variables to their smt represenation (TODO: make this take an iterator over vars)
    pub fn build_var_map(&self, vars: &Vec<&Variable>) -> HashMap<Variable, Int<'a>> {
        let mut var_map = HashMap::<Variable, Int<'a>>::new();
        for var in vars {
            if let Some(name) = var.name() {
                var_map.insert((*var).clone(), *Int::new_const(self.st, name));
            }
        }
        var_map
    }

    /// Checks whether the rule annotatioins are actually satisfied (assert at least)(TODO)
    /*pub fn check_rule_annotation(rule: &NormalizedRule, restrictions: &HashMap<Variable, Range<i64>>) -> Result<bool,Error>{
        let st = Storage::new();
        let mut solver: Solver<'_, Z3Binary> = Solver::new(&st, Z3Binary::new("/usr/bin/z3").expect("bla")).expect("f");
        let mut lowering = Lowering::new(&st);

        let var_map = lowering.build_var_map(&rule.variables().collect());

        // Generate the smt representation for all predicates in the rule
        let predicate_set: HashSet<(Tag, usize)> = rule.predicates().collect();
        for (predicate, arity) in predicate_set{
            lowering.build_predicate(predicate, arity, &mut solver).expect("failed to build predicate");
        }

        Ok(true)
    }*/

    /// Get the minimum & maximum of the frontier variables
    pub fn get_head_var_range(
        restrictions: &HashMap<Variable, Range<i64>>,
        annotation_ops: &Vec<Operation>,
        body_ops: &Vec<Operation>,
        arith_head_vars: &HashSet<Variable>,
        rule_vars: Vec<&Variable>,
    ) -> Result<HashMap<Variable, Range<i64>>, Error> {
        let st = Storage::new();
        let mut solver: Solver<'_, Z3Binary> =
            Solver::new(&st, Z3Binary::new("/usr/bin/z3").expect("bla")).expect("f");
        // TODO: set logic to some sort of LIA or so
        //solver.set_logic(Logi)
        let mut lowering = Lowering::new(&st);

        let mut var_map = HashMap::<Variable, Int<'a>>::new();

        // Build the vars, could be converted to iterator and so on TODO: use the new function
        for var in rule_vars {
            if let Some(name) = var.name() {
                var_map.insert(var.clone(), *Int::new_const(&st, name));
            }
        }

        // Lower the restrictions
        lowering.lower_restrictions(restrictions, &var_map, &mut solver);

        // Lower the annotation ops
        for operation in annotation_ops {
            solver
                .assert(lowering.lower_operation(operation, &var_map)?.as_bool()?)
                .expect("failed to assert op");
        }

        // Lower body operations
        for operation in body_ops {
            solver
                .assert(lowering.lower_operation(operation, &var_map)?.as_bool()?)
                .expect("failed to assert op");
        }

        let mut min_values = HashMap::<Variable, i64>::new();
        for var in arith_head_vars {
            let min = solver.scope(|solver| {
                let var_const = var_map.get(var).expect("var should be registered");
                solver.minimize(*var_const)?;
                solver.check_sat()?;

                let min_value: i64 = solver.eval(*var_const)?.try_into().unwrap_or(i64::MIN);
                Ok(min_value)
            })?;
            min_values.insert(var.clone(), min);
        }

        let mut max_values = HashMap::<Variable, i64>::new();
        for var in arith_head_vars {
            let max = solver.scope(|solver| {
                let var_const = var_map.get(var).expect("var should be registered");
                solver.maximize(*var_const)?;
                solver.check_sat()?;

                let max_value: i64 = solver.eval(*var_const)?.try_into().unwrap_or(i64::MAX);
                Ok(max_value)
            })?;
            max_values.insert(var.clone(), max);
        }

        // Generate range from min, max
        let mut var_range = HashMap::<Variable, Range<i64>>::new();
        for var in arith_head_vars {
            let min = *min_values.get(var).expect("min value should be there");
            let max = *max_values.get(var).expect("max value should be there");
            var_range.insert(var.clone(), min..max + 1);
        }

        Ok(var_range)
    }
}
