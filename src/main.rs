use std::{collections::{HashMap, HashSet}, env, fmt::{self, Display}, sync::atomic::AtomicUsize};

/// A type variable for inference; can also end up appearing in the final
/// signature in polymorphic functions.
/// 
/// In general, we write type variables as '0, or ?0.
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

/// A skolem variable. These are used to represent type variables that should
/// not be solved for - they are part of some "higher-up" polymorphic type.
/// 
/// Here, we write skolems as greek letters; this is ~somewhat confusing with
/// our other uses of greek characters, but they don't need to show up that
/// much.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Skolem(usize);

impl Skolem {
    /// Construct a new skolem variable.
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
        if self.0 < 24 {
            write!(f, "{}", GREEK_LETTERS[self.0])
        } else {
            write!(f, "sk{}", self.0)
        }
    }
}

/// A monotype is a type which cannot contain foralls.
/// We notate monotypes as τ.
#[derive(Clone, Debug)]
enum Monotype {
    Var(TypeVar),
    Skolem(Skolem),
    Int,
    Bool,
    Arrow(Box<Monotype>, Box<Monotype>),
}

impl Display for Monotype {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Monotype::Var(v) => write!(f, "{}", v),
            Monotype::Skolem(s) => write!(f, "{}", s),
            Monotype::Int => write!(f, "Int"),
            Monotype::Bool => write!(f, "Bool"),
            Monotype::Arrow(m_1, m_2) => write!(f, "({} -> {})", m_1, m_2),
        }
    }
}

impl Monotype {
    /// Collect the free type variables in a monotype.
    fn ftv(&self) -> HashSet<TypeVar> {
        match self {
            Monotype::Var(v) => {
                let mut s = HashSet::new();
                s.insert(*v);
                s
            }
            Monotype::Arrow(m_1, m_2) => m_1.ftv().union(&m_2.ftv()).copied().collect(),
            _ => HashSet::new()
        }
    }

    /// Substitute skolem variables in a type with type variables.
    fn subst_skolem_in_type(&self, mapping: &HashMap<Skolem, TypeVar>) -> Monotype {
        match self {
            Monotype::Skolem(sk) => match mapping.get(sk) {
                Some(v) => Monotype::Var(*v),
                None => Monotype::Skolem(*sk),
            }
            Monotype::Arrow(m_1, m_2) => {
                let m_1_prime = m_1.subst_skolem_in_type(mapping);
                let m_2_prime = m_2.subst_skolem_in_type(mapping);
                Monotype::Arrow(Box::new(m_1_prime), Box::new(m_2_prime))
            }
            m => m.clone()
        }
    }

    /// Apply a substitution to a monotype.
    fn apply_substitution(&self, substitution: &Substitution) -> Monotype {
        match self {
            Monotype::Var(v) => {
                substitution.get(*v).cloned().unwrap_or(Monotype::Var(*v))
            }
            Monotype::Arrow(m_1, m_2) =>
                Monotype::Arrow(Box::new(m_1.apply_substitution(substitution)), Box::new(m_2.apply_substitution(substitution))),
            m => m.clone()
        }
    }
}

/// An equality constraint is a statement that two types are equal.
#[derive(Debug, Clone)]
struct EqConstraint(Monotype, Monotype);

impl Display for EqConstraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} = {}", self.0, self.1)
    }
}

/// A class constraint is a statement that a type belongs to a class.
/// An example might be `Eq a`, which states that `a` is an instance of the
/// `Eq` class - i.e. it can be compared for equality.
#[derive(Debug, Clone)]
struct ClassConstraint(String, Monotype);

impl Display for ClassConstraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

#[derive(Debug, Clone)]
enum Constraint {
    Eq(EqConstraint),
    Class(ClassConstraint),
}

impl Constraint {
    fn eq(m_1: Monotype, m_2: Monotype) -> Constraint {
        Constraint::Eq(EqConstraint(m_1, m_2))
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constraint::Eq(c) => write!(f, "{}", c),
            Constraint::Class(c) => write!(f, "{}", c),
        }
    }
}

/// A polytype is a type with some number of foralls at the beginning.
/// We notate polytypes as σ.
#[derive(Clone, Debug)]
struct Polytype {
    vars: Vec<Skolem>,
    class_constraints: Vec<ClassConstraint>,
    ty: Monotype,
}

impl Display for Polytype {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.vars.is_empty() {
            write!(f, "{}", self.ty)
        } else {
            write!(f, "∀{}. {}. {}", self.vars.iter().map(|v| format!("{}", v)).collect::<Vec<String>>().join(", "), self.class_constraints.iter().map(|c| format!("{}", c)).collect::<Vec<String>>().join(", "), self.ty)
        }
    }
}

impl Polytype {
    /// Turn a polytype into a monotype, replacing all type variables with
    /// skolem variables (they should not be solved for).
    fn inst(&self) -> (Monotype, Vec<ClassConstraint>) {
        let mapping = 
            self
                .vars
                .iter()
                .map(|&s| (s, TypeVar::new()))
                .collect();
        
        let class_constraints = 
            self.class_constraints.iter().map(
                |ClassConstraint(name, m)|
                    ClassConstraint(name.clone(), m.subst_skolem_in_type(&mapping))
            ).collect();

        (self.ty.subst_skolem_in_type(&mapping), class_constraints)
    }
}

/// The environment is a mapping between variable names and their types.
/// Notably, the environment contains polytypes, not monotypes.
/// 
/// The environment is notated as Γ.
#[derive(Clone, Debug)]
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

    /// Collect the free type variables in the environment.
    fn ftv(&self) -> HashSet<TypeVar> {
        self.0.values().flat_map(|p| p.ty.ftv()).collect()
    }
}

/// An expression in our language.
enum Expr {
    Var(String),
    Lam(String, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Int(i64),
    Bool(bool),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Expr::*;
        match self {
            Var(x) => write!(f, "{}", x),
            Lam(x, e) => write!(f, "λ{}. {}", x, e),
            App(e1, e2) => write!(f, "({} {})", e1, e2),
            Let(x, e1, e2) => write!(f, "let {} = {} in {}", x, e1, e2),
            Int(n) => write!(f, "{}", n),
            Bool(b) => write!(f, "{}", b),
            If(e1, e2, e3) => write!(f, "if {} then {} else {}", e1, e2, e3),
        }
    }
}

#[derive(Debug)]
struct Substitution(HashMap<TypeVar, Monotype>);

impl Substitution {
    fn new() -> Substitution {
        Substitution(HashMap::new())
    }

    fn insert(&mut self, k: TypeVar, v: Monotype) {
        if v.ftv().contains(&k) {
            panic!("occur check failed")
        }
        self.0.insert(k, v);
    }

    fn get(&self, k: TypeVar) -> Option<&Monotype> {
        self.0.get(&k)
    }
}

/// Attempt to solve a set of constraints, returning a substitution that
/// satisfies the most constraints possible.
fn solve(mut constraints: Vec<Constraint>) -> (Vec<Constraint>, Substitution) {
    let mut class_constraints = vec![];
    let mut substitution: Substitution = Substitution::new();

    use Monotype::*;

    while let Some(constraint) = constraints.pop() {
        match constraint {
            // we can't actually solve class constraints here lol
            Constraint::Class(c) => {
                class_constraints.push(c)
            },
            Constraint::Eq(EqConstraint(ty_1,ty_2 )) => match (ty_1, ty_2) {
                // a = a; already satisfied
                (Var(v_1), Var(v_2)) if v_1 == v_2 => {},
                (Var(v), m) | (m, Var(v))  => {
                    if let Some(ty) = substitution.get(v) {
                        constraints.push(Constraint::eq(m, ty.clone()))
                    } else {
                        let m = m.apply_substitution(&substitution);
                        substitution.insert(v, m);
                    }
                },
                // (a → b) = (c → d) => a = c, b = d
                (Arrow(a, b), Arrow(c, d)) => {
                    constraints.push(Constraint::eq(*a, *c));
                    constraints.push(Constraint::eq(*b, *d));
                },
                // Skolems can only unify with themselves.
                (Skolem(s), Skolem(z)) if s == z => {},
                (Int, Int) => {},
                (Bool, Bool) => {},
                (a, b) => panic!("could not unify {a} and {b}")
            }
        }   
    }

    for ClassConstraint(name, ty) in class_constraints {
        let constraint = ClassConstraint(name, ty.apply_substitution(&substitution));
        constraints.push(Constraint::Class(constraint));
    }

    (constraints, substitution)
}

/// Collect the free type variables from a set of constraints.
fn ftv_constraints(constraints: &Vec<Constraint>) -> HashSet<TypeVar> {
    constraints.iter().map(|c| match c {
        Constraint::Class(ClassConstraint(_, ty)) => ty.ftv(),
        Constraint::Eq(EqConstraint(t1, t2)) => t1.ftv().union(&t2.ftv()).copied().collect()
    }).flat_map(|s| s).collect()
}

/// Apply a substitution to a set of constraints.
fn apply_substitution_to_constraints(constraints: Vec<Constraint>, substitution: &Substitution) -> Vec<Constraint> {
    constraints.into_iter().map(|c| match c {
        Constraint::Class(ClassConstraint(name, ty)) => Constraint::Class(ClassConstraint(name, ty.apply_substitution(substitution))),
        Constraint::Eq(EqConstraint(t1, t2)) => Constraint::Eq(EqConstraint(t1.apply_substitution(substitution), t2.apply_substitution(substitution)))
    }).collect()
}

/// Infer the type of an expression.
fn infer(env: &Environment, expr: &Expr) -> (Monotype, Vec<Constraint>) {
    use Expr::*;
    // Each of these matches a syntax-directed rule in the inference system.
    // In each rule, we have the premises above the line and the conclusion below the line.
    // Generally, a premise means we need to infer the type of some subexpression.
    // The conclusion is the type of the expression itself.
    // The conclusion may also generate some constraints that need to be solved.
    // In general, you can read an expression that looks like
    //     Γ ⊢ e : τ ↝ C
    // as "Given the environment Γ, the expression e has type τ, generating constraints C."
    // Constraints "flow down" the tree; they do not "flow up" at all.
    match expr {
        // Integer constants:
        //
        // -------------
        //  Γ ⊢ n : Int
        Int(_) => (Monotype::Int, vec![]),
        // Boolean constants:
        //
        // --------------
        //  Γ ⊢ b : Bool
        Bool(_) => (Monotype::Bool, vec![]),
        //           x : σ ∈ Γ
        // -------------------------------
        //  Γ ⊢ x : inst(σ).0 ↝ inst(σ).1
        Var(x) => {
            let (ty, cs) = env.lookup(&x).inst();
            let cs = cs.into_iter().map(Constraint::Class).collect();
            (ty, cs)
        },
        // Function application:
        //
        //     Γ ⊢ f : τ₁ ↝ C₁     Γ ⊢ x : τ₂ ↝ C₂
        // -------------------------------------------
        //  Γ ⊢ (f x) : τ₀ ↝ C₁ ∪ C₂ ∪ {τ₁ = τ₂ → τ₀}
        App(func, arg) => {
            let (func_type, func_cs) = infer(env, func);
            let ret_type = Monotype::Var(TypeVar::new());
            let (arg_type, arg_cs) = infer(env, arg);

            let mut cs = func_cs;

            cs.extend(arg_cs);
            cs.push(Constraint::Eq(EqConstraint(
                func_type,
                Monotype::Arrow(Box::new(arg_type), Box::new(ret_type.clone()))
            )));

            (ret_type, cs)
        }
        // Lambda abstraction:
        //
        //  fresh(τ₀)    Γ, x : ∀ . Ø . τ₀ ⊢ e : τ₁ ↝ C
        // ---------------------------------------------
        //             Γ ⊢ λx. e : τ₀ → τ₁ ↝ C
        //
        // The premise with x really just means "this is a polytype with no foralls".
        // We can't assume anything about x; this is why let generalization is important.
        // `fresh` here is equivalent to saying "let τ₀ be a new type variable".
        Lam(var, body ) => {
            let arg_type = Monotype::Var(TypeVar::new());

            let var_type = Polytype {
                vars: vec![],
                class_constraints: vec![],
                ty: arg_type.clone()
            };

            let mut env = env.clone();

            env.insert(var.clone(), var_type);

            let (body_type, body_cs) = infer(&env, body);

            let ty = Monotype::Arrow(Box::new(arg_type), Box::new(body_type));

            (ty, body_cs)
        }
        // If expressions:
        //
        //       Γ ⊢ c :   τ₀ ↝ C₁     Γ ⊢ t : τ₁ ↝ C₂     Γ ⊢ e : τ₂ ↝ C₃
        // ---------------------------------------------------------------------
        //  Γ ⊢ (if c then t else e) : τ₁ ↝ C₁ ∪ C₂ ∪ C₃ ∪ {τ₀ = Bool, τ₁ = τ₂}
        If(cond, then, r#else) => {
            let (cond_type, cond_cs) = infer(env, cond);
            let (then_type, then_cs) = infer(env, then);
            let (else_type, else_cs) = infer(env, r#else);

            let mut cs = cond_cs;
            cs.extend(then_cs);
            cs.extend(else_cs);
            cs.push(Constraint::Eq(EqConstraint(cond_type, Monotype::Bool)));
            cs.push(Constraint::Eq(EqConstraint(then_type.clone(), else_type)));

            (then_type, cs)
        }
        // Let expressions:
        // (For "Σ @ x", read "the substitution Σ applied to x".)
        // Abbreviations here:
        // - cco "class constraints of"
        // - Σ₁[v ⟳ α]  Assign skolems α₁, α₂, ... αₙ to v₁, v₂, ... vₙ and make a substitution Σ₁
        //
        // 1. v = ftv(C₁) ∪ ftv(Σ @ x) - ftv(Γ)
        // 
        //   Γ ⊢ value : τ₀ ↝ C₀     (C₁, Σ₀) = solve(C₀)        Γ,x:(Σ₁[v ⟳ α] @ τ₀) ⊢ body : τ₁ ↝ C₂
        // ---------------------------------------------------------------------------------------------
        //                      Γ ⊢ let x = value in body : τ₁ ↝ C₂
        // 
        // TODO i need to fix this comment up it sucks
        Let(var, value, body) => {
            let (value_type, value_cs) = infer(env, value);
            let (cs, substitution) = solve(value_cs);
            let value_type = value_type.apply_substitution(&substitution);
            let cs_ftv = ftv_constraints(&cs);
            let env_ftv = env.ftv();

            // v = ftv(value) ∪ ftv(cs) - ftv(env)
            // assign α₁, α₂, ... αₙ to v₁, v₂, ... vₙ

            let skolems: Vec<(TypeVar, Skolem)> = value_type.ftv().union(&cs_ftv).filter(|t| !env_ftv.contains(t)).copied().map(|t| (t, Skolem::new())).collect();

            let skolemizer = Substitution(skolems.iter().copied().map(|(t, s)| (t, Monotype::Skolem(s))).collect());

            let value_type = value_type.apply_substitution(&skolemizer);

            let var_type = Polytype {
                vars: skolems.iter().map(|(_, s)| s).copied().collect(),
                class_constraints: apply_substitution_to_constraints(cs, &skolemizer).into_iter().filter_map(|c| match c {
                    Constraint::Class(c) => Some(c),
                    _ => None,
                }).collect(),
                ty: value_type,
            };

            let mut env = env.clone();
            
            env.insert(var.to_string(), var_type);
            
            infer(&env, body)
        }
        _ => unimplemented!()
    }
}


/// Get the type of an expression.
/// Attempts to fully solve constraints and substitute type variables.
fn type_of(expr: &Expr, env: &Environment) -> (Monotype, Vec<Constraint>) {
    let (ty, constraints) = infer(env, expr);
    let (constraints, substitution) = solve(constraints);
    let ty = ty.apply_substitution(&substitution);
    let constraints = apply_substitution_to_constraints(constraints, &substitution);
    (ty, constraints)
}

/// Helper function to display constraints.
fn stringify_constraints(constraints: Vec<Constraint>) -> String {
    constraints.iter().map(|c| format!("{}", c)).collect::<Vec<String>>().join(", ")
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
        Box::new(Expr::Var("max".to_string()))
        // Box::new(Expr::App(
        //     Box::new(Expr::App(, Box::new(Expr::Int(3)))),
        //     Box::new(Expr::Int(4)),
        // )),
    );

    let const_fn = Expr::Lam(
        "x".to_string(),
        Box::new(Expr::Lam("y".to_string(), Box::new(Expr::Var("x".to_string()))))
    );

    let const_fn_applied = Expr::App(
        Box::new(Expr::App(Box::new(const_fn), Box::new(Expr::Int(3)))),
        Box::new(Expr::Bool(true))
    );

    let (ty, constraints) = type_of(&max, &environment);

    println!("Type: {}", ty);
    println!("Constraints: {}", stringify_constraints(constraints));
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    #[should_panic]
    fn weird_solve() {
        let _0 = TypeVar::new();
        let _1 = TypeVar::new();

        // '1 = ('0 → '0)
        // '0 = ('1 → '1)

        let constraints = vec![
            Constraint::eq(Monotype::Var(_0), Monotype::Arrow(Box::new(Monotype::Var(_1)), Box::new(Monotype::Var(_1)))),
            Constraint::eq(Monotype::Var(_1), Monotype::Arrow(Box::new(Monotype::Var(_0)), Box::new(Monotype::Var(_0)))),
        ];

        solve(constraints);
    }
}