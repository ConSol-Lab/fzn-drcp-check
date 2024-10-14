use ocaml::ToValue;

// Inductive Step :=
//   | inference (premises : list Atomic) (conclusion : Atomic).
//
// Inductive Conclusion :=
//   | unsat
//   | optimal (bound : Atomic).
//
// Record Proof :=
//   {
//     steps : list Step;
//     conclusion : Conclusion;
//   }.

#[ocaml::sig("Leq | Geq | Eq | Ne")]
#[derive(ToValue)]
pub enum Comparator {
    Leq,
    Geq,
    Eq,
    Ne,
}

#[ocaml::sig("{ variable: string; comparator: comparator; value: int }")]
#[derive(ToValue)]
pub struct Atomic {
    variable: String,
    comparator: Comparator,
    value: i32,
}

#[ocaml::sig("Unsat | Optimal of atomic")]
#[derive(ToValue)]
pub enum Conclusion {
    Unsat,
    Optimal(Atomic),
}

#[ocaml::sig("{ premises: atomic list; conclusion: atomic }")]
#[derive(ToValue)]
pub struct Inference {
    premises: Vec<Atomic>,
    conclusion: Atomic,
}

#[ocaml::sig("Inference of inference | Nogood of atomic list")]
#[derive(ToValue)]
pub enum Step {
    Inference(Inference),
    Nogood(Vec<Atomic>),
}

#[ocaml::sig("{ steps: step list; conclusion: conclusion }")]
#[derive(ToValue)]
pub struct Proof {
    steps: Vec<Step>,
    conclusion: Conclusion,
}

ocaml::custom!(Comparator);
ocaml::custom!(Atomic);
ocaml::custom!(Conclusion);
ocaml::custom!(Step);
ocaml::custom!(Proof);

#[ocaml::func]
#[ocaml::sig("string -> proof")]
pub fn parse_proof(_file_path: &str) -> Proof {
    Proof {
        steps: vec![],
        conclusion: Conclusion::Unsat,
    }
}
