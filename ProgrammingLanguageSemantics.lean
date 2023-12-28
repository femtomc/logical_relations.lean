import Init.Prelude
import Mathlib.Data.Nat.Basic
import Lean

/-!

Lesson 1: lambda calculus design

We'll start by considering a simple language with arithmetic, and function definitions.

* We separate the meta-types of the language into two categories: syntax, and values.

* The type of syntax will be called `Term`, and the type of the values will be called `Value`.

* We want to define an evaluation semantics: a rule system which includes a rewrite rule that allows us to manipulate the syntax.

* Our key theorem is that, if the rule system terminates, then the resulting syntax must be a value.

-/

inductive Term
| Nat : ℕ → Term
| Var : ℕ → Term
| Prim : (ℕ → ℕ → ℕ) → Term
| Abs : Term → Term
| App : Term → Term → Term

def termRepr : Term → Nat → Lean.Format
| Term.Nat n, _ => repr n
| Term.Var n, _ => "var(" ++ repr n ++ ")"
| Term.Prim _, _ => "<opaque prim>"
| Term.Abs t, depth => "(λ " ++ termRepr t (depth + 1) ++ ")"
| Term.App t1 t2, depth => "(" ++ termRepr t1 (depth + 1) ++ " " ++ termRepr t2 (depth + 1) ++ ")"

instance : Repr Term where
reprPrec t _ := termRepr t 0

def Env := List Term

def lookupEnv : Env -> ℕ -> Option Term
| [], _ => none
| (v :: _), 0 => some v
| (_ :: vs), (n + 1) => lookupEnv vs n

def shift : ℕ -> Term -> Term
| _, Term.Nat n => Term.Nat n
| d, Term.Var k => Term.Var (k + d)
| d, Term.Abs t => Term.Abs (shift (d + 1) t)
| d, Term.App t1 t2 => Term.App (shift d t1) (shift d t2)
| _, Term.Prim f => Term.Prim f

def subst : ℕ -> Term -> Term -> Term
| _, _, Term.Nat n => Term.Nat n
| k, s, t@(Term.Var k') => if k = k' then s else t
| k, s, Term.Abs t => Term.Abs (subst (k + 1) (shift 1 s) t)
| k, s, Term.App t1 t2 => Term.App (subst k s t1) (subst k s t2)
| _, _, t@(Term.Prim _) => t

def eval : ℕ -> Env → Term → Term
| 0, _, t@(_) => t
| _, _, Term.Nat n => Term.Nat n
| _, env, Term.Var n => (lookupEnv env n).getD (Term.Var n)
| fuel + 1, env, Term.Abs t => Term.Abs (eval fuel (Term.Var 0 :: env.map (shift 1)) t)
| _, _, Term.Prim f => Term.Prim f
| fuel + 1, env, (Term.App (Term.Abs t) v) =>
  let v_eval := eval fuel env v; 
  eval fuel env (subst 0 v_eval t) 
| fuel + 1, env, (Term.App t1 t2) =>
  let t1_eval := eval fuel env t1;
  let t2_eval := eval fuel env t2;
  eval fuel env (Term.App t1_eval t2_eval)

-- Nicely, we can run our evaluation interpreter and get results, but
-- we have to give it fuel!
#eval eval 10 [] (Term.App (Term.Abs (Term.Var 0)) (Term.Nat 5))

/-!

Lesson 2: Type systems 

In Lesson 2, we'll add types to the language, and prove that the type system is sound with respect to the operational semantics.

We'll do this using a technique called logical relations.

-/
