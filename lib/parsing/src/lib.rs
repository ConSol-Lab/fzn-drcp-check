use std::{collections::LinkedList, fs::File, path::PathBuf};

use drcp_format::{
    reader::{ProofReader, ReadStep},
    steps::StepId,
    AtomicConstraint, IntAtomicConstraint, LiteralDefinitions,
};
use ocaml::ToValue;

#[ocaml::sig("Leq | Geq | Eq | Ne")]
#[derive(ToValue)]
pub enum Comparator {
    Leq,
    Geq,
    Eq,
    Ne,
}

impl From<drcp_format::Comparison> for Comparator {
    fn from(value: drcp_format::Comparison) -> Self {
        match value {
            drcp_format::Comparison::GreaterThanEqual => Comparator::Geq,
            drcp_format::Comparison::LessThanEqual => Comparator::Leq,
            drcp_format::Comparison::Equal => Comparator::Eq,
            drcp_format::Comparison::NotEqual => Comparator::Ne,
        }
    }
}

#[ocaml::sig("{ variable: string; comparator: comparator; value: int }")]
#[derive(ToValue)]
pub struct Atomic {
    variable: String,
    comparator: Comparator,
    value: i32,
}

impl From<AtomicConstraint<String>> for Atomic {
    fn from(value: AtomicConstraint<String>) -> Self {
        match value {
            AtomicConstraint::Bool(_) => todo!(),
            AtomicConstraint::Int(IntAtomicConstraint {
                name,
                comparison,
                value,
            }) => Atomic {
                variable: name,
                comparator: comparison.into(),
                value: value.try_into().expect("failed to convert integer types"),
            },
        }
    }
}

#[ocaml::sig("Unsat | Optimal of atomic")]
#[derive(ToValue)]
pub enum Conclusion {
    Unsat,
    Optimal(Atomic),
}

type SourceConclusion = drcp_format::steps::Conclusion<AtomicConstraint<String>>;

impl<'a> From<SourceConclusion> for Conclusion {
    fn from(value: SourceConclusion) -> Self {
        match value {
            drcp_format::steps::Conclusion::Unsatisfiable => Conclusion::Unsat,
            drcp_format::steps::Conclusion::Optimal(bound) => Conclusion::Optimal(bound.into()),
        }
    }
}

#[ocaml::sig("{ premises: atomic list; conclusion: atomic }")]
#[derive(ToValue)]
pub struct Inference {
    premises: LinkedList<Atomic>,
    conclusion: Atomic,
}

type SourceInference<'a> =
    drcp_format::steps::Inference<'a, Vec<AtomicConstraint<String>>, AtomicConstraint<String>>;

impl<'a> From<SourceInference<'a>> for Inference {
    fn from(value: SourceInference<'a>) -> Self {
        Inference {
            premises: value.premises.into_iter().map(Into::into).collect(),
            conclusion: value.propagated.unwrap().into(),
        }
    }
}

#[ocaml::sig("{ clause: atomic list }")]
#[derive(ToValue)]
pub struct Nogood {
    clause: LinkedList<Atomic>,
}

type SourceNogood = drcp_format::steps::Nogood<Vec<AtomicConstraint<String>>, Vec<StepId>>;

impl<'a> From<SourceNogood> for Nogood {
    fn from(value: SourceNogood) -> Self {
        Nogood {
            clause: value.literals.into_iter().map(Into::into).collect(),
        }
    }
}

#[ocaml::sig("Inference of inference | Nogood of nogood")]
#[derive(ToValue)]
pub enum Step {
    Inference(Inference),
    Nogood(Nogood),
}

#[ocaml::sig("{ steps: step list; conclusion: conclusion }")]
#[derive(ToValue)]
pub struct Proof {
    steps: LinkedList<Step>,
    conclusion: Conclusion,
}

#[ocaml::func]
#[ocaml::sig("string -> proof")]
pub fn parse_proof(file_path: &str) -> Result<Proof, ocaml::Error> {
    let proof_path = PathBuf::from(file_path);
    let lits_path = proof_path.with_extension("lits");

    let lits_file = File::open(lits_path).map_err(|e| ocaml::Error::Error(Box::new(e)))?;
    let definitions: LiteralDefinitions<String> = drcp_format::LiteralDefinitions::parse(lits_file)
        .map_err(|e| ocaml::Error::Error(Box::new(e)))?;

    let proof_file = File::open(proof_path).map_err(|e| ocaml::Error::Error(Box::new(e)))?;
    let mut proof_reader = ProofReader::new(proof_file, definitions);

    let mut steps = LinkedList::new();

    let conclusion = loop {
        let next_step = proof_reader
            .next_step()
            .map_err(|e| ocaml::Error::Error(Box::new(e)))?;

        let Some(next_step) = next_step else {
            return Err(ocaml::Error::Message("Missing conclusion in proof"));
        };

        match convert_step(next_step) {
            Converted::Step(step) => steps.push_back(step),
            Converted::Conclusion(conclusion) => break conclusion,
        }
    };

    Ok(Proof { steps, conclusion })
}

enum Converted {
    Step(Step),
    Conclusion(Conclusion),
}

fn convert_step(reader_step: ReadStep<'_, AtomicConstraint<String>>) -> Converted {
    match reader_step {
        drcp_format::steps::Step::Inference(inference) => {
            Converted::Step(Step::Inference(inference.into()))
        }
        drcp_format::steps::Step::Nogood(nogood) => Converted::Step(Step::Nogood(nogood.into())),
        drcp_format::steps::Step::Delete(_) => todo!("implement deletion steps"),
        drcp_format::steps::Step::Conclusion(conclusion) => {
            Converted::Conclusion(conclusion.into())
        }
    }
}
