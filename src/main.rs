use std::{collections::HashMap, fmt::{self, Display}, sync::atomic::AtomicUsize};

/// A type variable for inference; can also end up appearing in the final
/// signature in polymorphic functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVar(usize);

impl TypeVar {
    /// Construct a new type variable.
    pub fn new() -> TypeVar {
        static VAR_COUNTER: AtomicUsize = AtomicUsize::new(0);
        TypeVar(VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed))
    }
}

impl Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "'{}", self.0)
    }
}

/// A type variable for inference; can also end up appearing in the final
/// signature in polymorphic functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Skolem(usize);

impl Skolem {
    /// Construct a new type variable.
    pub fn new() -> Skolem {
        static VAR_COUNTER: AtomicUsize = AtomicUsize::new(0);
        Skolem(VAR_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed))
    }
}

static GREEK_LETTERS: [&str; 24] = [
    "α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "λ", "μ", "ν", "ξ", "ο", "π", "ρ", "σ", "τ",
    "υ", "φ", "χ", "ψ", "ω",
];

impl Display for Skolem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if(self.0 < 24) {
            write!(f, "{}", GREEK_LETTERS[self.0])
        } else {
            write!(f, "sk{}", self.0)
        }
    }
}

enum Monotype {
    Var(TypeVar),
    Skolem(Skolem),
    Int,
    Bool,
    Arrow(Box<Monotype>, Box<Monotype>),
}

struct EqConstraint(Monotype, Monotype);

struct ClassConstraint(String, Monotype);

enum Constraint {
    Eq(EqConstraint),
    Class(ClassConstraint),
}

struct Polytype {
    vars: Vec<Skolem>,
    class_constraints: Vec<ClassConstraint>,
    ty: Monotype,
}

struct Environment(HashMap<String, Polytype>);

impl Environment {
    fn new() -> Environment {
        Environment(HashMap::new())
    }

    fn insert(&mut self, name: String, polytype: Polytype) {
        if self.0.contains_key(&name) {
            panic!("Duplicate definition of {}", name);
        }

        self.0.insert(name, polytype);
    }

    fn lookup(&self, name: &str) -> &Polytype {
        self.0.get(name).expect(&format!("Unbound variable {}", name))
    }
}


enum Expr {
    Var(String),
    Lam(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Int(i64),
    Bool(bool),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}

fn main() {
    let mut environment = Environment::new();

    let gt_sk = Skolem::new();

    let gt = Polytype {
        vars: vec![gt_sk],
        class_constraints: vec![ClassConstraint("Ord".to_string(), Monotype::Skolem(gt_sk))],
        ty: Monotype::Arrow(
            Box::new(Monotype::Skolem(gt_sk)),
            Box::new(Monotype::Arrow(
                Box::new(Monotype::Skolem(gt_sk)),
                Box::new(Monotype::Bool),
            )),
        ),
    };

    environment.insert(">".to_string(), gt);

    let max = Expr::Let(
        "max".to_string(),
        Box::new(Expr::Lam(
            "x".to_string(),
            Box::new(Expr::Lam(
                "y".to_string(),
                Box::new(Expr::If(
                    Box::new(Expr::App(
                        Box::new(Expr::App(Box::new(Expr::Var(">".to_string())), Box::new(Expr::Var("x".to_string())))),
                        Box::new(Expr::Var("y".to_string())),
                    )),
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Var("y".to_string())),
                )),
            )),
        )),
        Box::new(Expr::App(
            Box::new(Expr::App(Box::new(Expr::Var("max".to_string())), Box::new(Expr::Int(3)))),
            Box::new(Expr::Int(4)),
        )),
    );

    println!("Hello, world!");
}
