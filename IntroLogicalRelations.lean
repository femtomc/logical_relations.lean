import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

/-!
This is a tutorial file showing the usage of logical relations to prove properties about languages, including things like soundness of operational semantics, soundness of a type system, and even soundness of a denotational semantics.

First, we'll start by considering a simple language with arithmetic, and function definitions.
-/

inductive Term
| Nat : ℕ → Term
| Var : ℕ → Term
| Abs : Term → Term
| App : Term → Term → Term
| Prim : (ℕ → ℕ → ℕ) → Term

def Env := List Term

def lookupEnv : Env -> ℕ -> Option Term
| [], _ => none
| (v :: _), 0 => some v
| (_ :: vs), (n + 1) => lookupEnv vs n

def shift : ℕ -> Term -> Term
| d, Term.Nat n => Term.Nat n
| d, Term.Var k => Term.Var (k + d)
| d, Term.Abs t => Term.Abs (shift (d + 1) t)
| d, Term.App t1 t2 => Term.App (shift d t1) (shift d t2)
| d, Term.Prim f => Term.Prim f

def subst : ℕ -> Term -> Term -> Term
| k, s, Term.Nat n => Term.Nat n
| k, s, Term.Var k' => if k = k' then s else Term.Var k'
| k, s, Term.Abs t => Term.Abs (subst (k + 1) (shift 1 s) t)
| k, s, Term.App t1 t2 => Term.App (subst k s t1) (subst k s t2)
| k, s, Term.Prim f => Term.Prim f

def eval : Env → Term → Term
| env, Term.Nat n => Term.Nat n
| env, Term.Var n => (lookupEnv env n).getD (Term.Var n)
| env, Term.Abs t => Term.Abs (eval (Term.Var 0 :: env.map (shift 1)) t)
| env, Term.Prim f => Term.Prim f
| env, (Term.App (Term.Abs t) v) =>
  let v_eval := eval env v; 
  eval env (subst 0 v_eval t) 
| env, (Term.App t1 t2) =>
  let t1_eval := eval env t1;
  let t2_eval := eval env t2;
  eval env (Term.App t1_eval t2_eval)
