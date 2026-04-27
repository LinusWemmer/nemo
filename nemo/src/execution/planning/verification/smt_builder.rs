

use std::collections::HashMap;
use std::ops::{Add, Mul, Sub};

use smtlib::{
    Error,
    funs::Fun,
    terms::Dynamic,
    backend::z3_binary::Z3Binary,
    Int, 
    Bool, 
    SatResultWithModel, 
    Solver, 
    Storage, 
    prelude::*
};

use crate::nemo_physical::datavalues::DataValue;

use crate::execution::planning::normalization::{
    atom::{
        body::BodyAtom,
        head::HeadAtom
    },
    operation::Operation,
    rule_annotation::NormalizedRuleAnnotation,
    rule::NormalizedRule
};

use crate::rule_model::components::{
    tag::Tag,   
    term::{
        operation::operation_kind::OperationKind,
        primitive::{Primitive, variable::Variable}
    }
};

/// Lowers Datalog rules to smt represenation
#[derive(Debug)]
pub struct Lowering<'a>{
    st: &'a Storage,

    predicates_to_fun: HashMap<Tag, Fun<'a>>,
}

impl<'a> Lowering<'a>{

    /// Creates new instance of the lowering struct
    pub fn new(st: &'a Storage) -> Self{
        let predicates_to_fun = HashMap::<Tag, Fun<'a>>::new();
        Self { 
            st,
            predicates_to_fun,
        }
    }

    /// Returns the smt function for the given predicate
    pub fn get_predicate_fun(&mut self, predicate: &Tag) -> &Fun<'a>{

        self.predicates_to_fun
            .get(predicate).expect("predicate should be registered")
    }

    /// Constructs and declares the functions for the predicates
    pub fn build_predicate(&mut self, predicate: Tag, arity: usize, solver: &mut Solver<'a , Z3Binary>) -> Result<(), Error>{
        let arg_sort = (0..arity).map(|_| Int::sort()).collect();
        let fun = Fun::new(self.st, predicate.name(), arg_sort , Bool::sort());

        solver.declare_fun(&fun)?;
        self.predicates_to_fun.insert(predicate, fun);
        Ok(())
    }

    /// Constructs the body atom 
    pub fn lower_body_atom(&mut self, body_atom: &BodyAtom, var_map: &'a HashMap<Variable, Int>) -> Result<Bool<'a>, Error>{
        let pred_fun = self.get_predicate_fun(&body_atom.predicate());     
       
        let args: Vec<Dynamic>= body_atom.terms()
            .map(|term| var_map.get(term).expect("anon var not supported yet"))
            .map(|f|f.into_dynamic())
            .collect();
        pred_fun.call(&args)?.as_bool()
    }

    /// Constructs the head atom into smt representation
    pub fn lower_head_atom(&mut self, head_atom: &HeadAtom, var_map: &'a HashMap<Variable, Int>) -> Result<Bool<'a>, Error>{
        let args: Vec<Dynamic>= head_atom.terms()
            .map(|term| self.lower_primitive(term, var_map))
            .map(|f|f.into_dynamic())
            .collect();

        let pred_fun: &Fun<'_> = self.get_predicate_fun(&head_atom.predicate());
        pred_fun.call(&args)?.as_bool()
    }

    /// Converts primitive into smt representation, expects only variables and ground terms for now
    pub fn lower_primitive(
        &self,
        primitive: &Primitive,
        var_map: &'a HashMap<Variable, Int<'a>>
    )-> Int<'a>{

        match primitive{
            Primitive::Variable(variable) => *var_map.get(variable).expect("var not found in map"),
            Primitive::Ground(ground_term) =>
                Int::new(self.st, ground_term.value().to_i64_unchecked()),
        }
    }

    ///Converts rule annotation to smt representation
    pub fn lower_rule_annotation(&mut self, annotation: &NormalizedRuleAnnotation, var_map: &'a HashMap<Variable, Int<'a>>) -> Vec<Bool<'a>>{
        annotation.body().iter()
            .map(|operation| self.lower_operation(operation, var_map).expect("should work").as_bool().expect("please please please"))
            .collect()
    }

    /// Converts operation into smt representation
    pub fn lower_operation(&mut self, operation: &Operation, var_map: &'a HashMap<Variable, Int<'a>>) -> Result<Dynamic<'a>,Error>{
        match operation{
            Operation::Primitive(primitive) => Ok(self.lower_primitive(primitive, var_map).into()),
            Operation::Opreation { kind, subterms } => 
                self.lower_operation_kind(kind, subterms, var_map),
        }
    }

    /// Converts operation kind into smt representation
    pub fn lower_operation_kind(&mut self, kind: &OperationKind, subterms: &Vec<Operation>, var_map: &'a HashMap<Variable, Int<'a>>) -> Result<Dynamic<'a>,Error>{

        // expect to only have two subterms
        let left = self.lower_operation(subterms.first().expect("invalid program component"), var_map)?;
        let right = self.lower_operation(subterms.get(1).expect("invalid program component"), var_map)?;

        match kind{
            OperationKind::Equal => Ok(left._eq(right).into_dynamic()),
            OperationKind::Unequals => Ok(left._neq(right).into_dynamic()),
            OperationKind::NumericSum => Ok(left.as_int()?.add(right.as_int()?).into()),
            OperationKind::NumericSubtraction => Ok(left.as_int()?.sub(right.as_int()?).into()),
            OperationKind::NumericProduct => Ok(left.as_int()?.mul(right.as_int()?).into()),
            OperationKind::NumericDivision => Ok((left.as_int()? / right.as_int()?).into()),
            OperationKind::NumericGreaterthaneq => Ok(left.as_int()?.ge(right.as_int()?).into()),
            OperationKind::NumericGreaterthan => Ok(left.as_int()?.gt(right.as_int()?).into()),
            OperationKind::NumericLessthaneq => Ok(left.as_int()?.le(right.as_int()?).into()),
            OperationKind::NumericLessthan => Ok(left.as_int()?.lt(right.as_int()?).into()),
            _ => panic!("other operations not supported for now")
        }
    }

    /// Generates Smtlib code for rule
    pub fn lower_rule(
        &'a mut self, 
        rule: &NormalizedRule, 
        var_map: &'a mut HashMap<Variable, Int<'a>>, 
        solver: &mut Solver<'a , Z3Binary> ,
    ) -> Result<(),Error>{

        // Build the vars, could be converted to iterator and so on TODO: use the new function
        for var in rule.variables(){
            if let Some(name) = var.name(){
                var_map
                    .entry(var.clone())
                    .or_insert(*Int::new_const(self.st, name));
            }
        }

        let body_atoms = rule.positive().iter()
            .map(|atom| self.lower_body_atom(atom, var_map).expect("failed in lower rule"));

        for atom in body_atoms{
            println!("{atom}");
            solver.assert(atom).expect("failed in asserting atom");
        }

        let body_operations = rule.operations().iter()
            .map(|op| self.lower_operation(op, var_map).expect("should work").as_bool().expect("please please please"));

        for op in body_operations{
            println!("op");
            solver.assert(op).expect("failed in asserting op")
        }

        // might not be necessary
        /*let head_atoms: Vec<Bool<'_>> = rule.head().iter()
            .map(|atom| self.lower_head_atom(atom, var_map).expect("failed in lower rule"))
            .collect();*/

        for annotation in rule.annotations(){
            let low_ann = self.lower_rule_annotation(annotation, var_map);
            for ann in low_ann{
                println!("{ann}");
                solver.assert(ann).expect("failed asserting an annotation");
            }
        }
        Ok(())
    }

    /// Checks whether the given rule is satisfiable with the given annotations TODO: add current range restriction
    pub fn check_rule(rule: &NormalizedRule) -> Result<bool, Error>{
        let st = Storage::new();
        let mut solver: Solver<'_, Z3Binary> = Solver::new(&st, Z3Binary::new("/usr/bin/z3").expect("bla")).expect("f");
        let mut vars = HashMap::<Variable, Int<'a>>::new();

        let mut lowering = Lowering::new(&st);

        for (predicate, arity) in rule.predicates(){
            lowering.build_predicate(predicate, arity, &mut solver).expect("failed to build predicate");
        }

        lowering.lower_rule(rule, &mut vars, &mut solver)?;
        
        
        // TODO: should probably check whether there exists a model not satisfying the annotations
        let result = solver.check_sat_with_model()?;
        match result{
            SatResultWithModel::Unsat => println!("Unsat"),
            SatResultWithModel::Sat(model) => println!("Result: {model}"),
            SatResultWithModel::Unknown => println!("Unknown"),
        }
        Ok(true)
    }
                
}
