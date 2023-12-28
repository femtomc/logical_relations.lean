import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.LibrarySearch
import Lean

/-!

Programming language semantics
==============================

`This entire notebook is a Lean file <https://github.com/femtomc/pls.lean/blob/main/ProgrammingLanguageSemantics.lean>`_, which means that it's a program that Lean can compile and run.

----

**Lesson 1: Untyped lambda calculus & operational semantics**

  .. epigraph::

    "There may, indeed, be other applications of the system than its use as a logic."

    -- Alonzo Church, 1941

We'll start by considering a language with arithmetic, function abstraction, and function application.

* We separate the meta-types of the language into two categories: syntax, and values.

* The inductive type of syntax will be called `Term`, and the type of the values will be denoted by an indicator function operating on `Term`.

* We want to define an evaluation semantics: a rule system which includes a rewrite rule that allows us to manipulate the syntax.

The key theorem which we'll seek to prove: *if the rule system terminates, then the result must be a value*.

----

-/

-- We'll start by defining the syntax of the language.
inductive Term
| Nat : ℕ → Term                -- Literal numbers.
| Var : ℕ → Term                -- Variables.
| Prim : (ℕ → ℕ → ℕ) → Term   -- Primitive functions.
| Abs : Term → Term             -- Function abstraction.
| App : Term → Term → Term     -- Function application.

-- We tell Lean how to print our terms.
def termRepr : Term → Nat → Lean.Format
| Term.Nat n, _ => repr n
| Term.Var n, _ => "var(" ++ repr n ++ ")"
| Term.Prim _, _ => "<opaque prim>"
| Term.Abs t, depth => "(λ " ++ termRepr t (depth + 1) ++ ")"
| Term.App t1 t2, depth => "(" ++ termRepr t1 (depth + 1) ++ " " ++ termRepr t2 (depth + 1) ++ ")"

instance : Repr Term where
reprPrec t _ := termRepr t 0


/-!

----

A term in a lambda calculus language is a syntactic entity that represents a computation.

* Terms are the basic building blocks of lambda calculus and are used to define functions (a constructor) and apply functions to arguments (a destructor).

* Terms can include variables, lambda abstractions (i.e., definitions of anonymous functions), and applications (i.e., invocation of functions with arguments).

* There can be different kinds of terms depending on the specific lambda calculus being used (e.g., simply typed lambda calculus, untyped lambda calculus).

* A term can be in an unevaluated form and does not have to represent a value that has been computed.

(*Exercise 1*): Our lambda calculus representation uses **de Bruijn notation**. Understand what this means, and why we use it.

----
-/

def is_value : Term → Prop
| Term.Nat _ => true
| Term.Prim _ => true
| Term.Abs _ => true
| _ => false

/-!

----

The notion of a value denotes a subset of the inductive type `Term`: a value represents a computed result that cannot be reduced or evaluated further.

* Values are terms that are in normal form or weak head normal form (whnf), meaning there are no more computation steps that can be applied to them to reduce them further.

* Looking ahead to typed lambda calculi, values might include things like constants (numbers, booleans), data constructors (for algebraic data types), and functions (since functions are first-class and considered values).

----

-/

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

-- In Lean, we can define the operational semantics of our language as a recursive function.
-- But there's something interesting: note that we have to give it a fuel argument, so that Lean knows that the recursion will terminate.
def eval : ℕ → Env → Term → Option Term
| 0, _, _ => none
| _, _, Term.Nat n => some (Term.Nat n)
| _, env, Term.Var n => lookupEnv env n
| fuel + 1, env, Term.Abs t => do
    let t_eval <- eval fuel (Term.Var 0 :: env.map (shift 1)) t;
    return Term.Abs t_eval
| _, _, Term.Prim f => some (Term.Prim f)
| fuel + 1, env, Term.App (Term.Abs t) v => do
    let v_eval <- eval fuel env v;
    eval fuel env (subst 0 v_eval t)
| fuel + 1, env, Term.App t1 t2 => do
    let t1_eval <- eval fuel env t1;
    let t2_eval <- eval fuel env t2;
    eval fuel env (Term.App t1_eval t2_eval)

-- We can run our evaluation interpreter and get results, but
-- we have to give it fuel!
#eval eval 10 [] (Term.App (Term.Abs (Term.Var 0)) (Term.Nat 7))

/-!

----

Now, let's write out first theorem: if the evaluation semantics terminates, then the result must be a value.

----

-/

theorem if_halts_then_value (fuel : ℕ) (t : Term) :
  ∀ (t' : Term), fuel != 0 ∧ eval fuel [] t = some t' →
  is_value t' :=
  by {
    intros t' h_eval
    cases h_eval with 
    | intro h_neq h_eval => {
      induction t
      case intro.Nat => {
          rw [eval] at h_eval
          injection h_eval with h_eq
          simp [<-h_eq, is_value]
          intro fuel_eq_0
          rw [fuel_eq_0] at h_neq
          contradiction
      }
      
      case intro.Var => {
        rw [eval] at h_eval
        rw [lookupEnv] at h_eval
        contradiction
        intro fuel_eq_0
        rw [fuel_eq_0] at h_neq
        contradiction
      }

      case intro.Prim => {
        rw [eval] at h_eval
        injection h_eval with h_eq
        simp [<-h_eq, is_value]
        intro fuel_eq_0
        rw [fuel_eq_0] at h_neq
        contradiction
      }
      
      case intro.Abs => {
        let fuel' := fuel - 1
        have h_fuel_eq : fuel = fuel' + 1 := by {
          simp [fuel']
          induction fuel
          contradiction
          exact rfl
        }
        rw [h_fuel_eq] at h_eval
        rw [eval] at h_eval
        cases eval_res : eval fuel' (Term.Var 0 :: List.map (shift 1) []) _
        
        case none => {
          rw [eval_res] at h_eval
          have h_none : (do 
                            let t_eval ← none
                            pure (Term.Abs t_eval)
          ) = none := rfl
          rw [h_none] at h_eval
          contradiction
        }
        
        case some => {
          rw [eval_res] at h_eval
          have h_eval_simp : some (Term.Abs ?x) = some t' := by exact h_eval
          injection h_eval_simp with h_eq
          simp [<-h_eq]
          exact rfl
        }
      }
      
      case intro.App => {
        sorry
      }
    }
  }

/-!

----

**Lesson 2: Simple type systems**

  .. epigraph::

    "For every λ, a type shall be its bind, to every term, a well-formedness, we'll find. 
    No more shall self-applying functions toll, for simple types have cleansed my soul."

    -- The Rime of the Simply Typed Mariner, 1834

In Lesson 2, we'll add types to the language, and prove that a few key theorems relating the type system to the operational semantics. 

These theorems are called *preservation* and *progress*.

----
-/

inductive TType
| Nat : TType                     -- Type of natural numbers.
| Fun : TType → TType → TType   -- Function types from one type to another.

/-!

----

For our types, we have natural numbers, and functions from one type to another. For pedagogy, we're not going to demonstrate how type systems avoid errors related to arithmetic (like passing Boolean values to functions which expect numbers).

----

-/

-- The type of contexts for holding the types of variables.
inductive TypingContext
| empty : TypingContext
| extend : TypingContext → ℕ → TType → TypingContext

open TypingContext

def lookup : TypingContext -> ℕ -> Option TType
| empty, _ => none
| extend Γ' x τ, n => if x = n then some τ else lookup Γ' n

-- Typechecking: a typing relation.
inductive TypeJudgment : TypingContext → Term → TType → Prop
| Type_Nat {Γ : TypingContext} (n : ℕ) :
    TypeJudgment Γ (Term.Nat n) TType.Nat

| Type_Var {Γ : TypingContext} (n : ℕ) (τ : TType) :
    (lookup Γ n = some τ) →
    TypeJudgment Γ (Term.Var n) τ

| Type_Prim {Γ : TypingContext} (f : ℕ → ℕ → ℕ) :
    TypeJudgment Γ (Term.Prim f) (TType.Fun TType.Nat (TType.Fun TType.Nat TType.Nat))

| Type_Abs {Γ : TypingContext} (t : Term) (τ1 τ2 : TType) :
    TypeJudgment (extend Γ 0 τ1) t τ2 →
    TypeJudgment Γ (Term.Abs t) (TType.Fun τ1 τ2)

| Type_App {Γ : TypingContext} (t1 t2 : Term) (τ1 τ2 : TType) :
    TypeJudgment Γ t1 (TType.Fun τ1 τ2) →
    TypeJudgment Γ t2 τ1 →
    TypeJudgment Γ (Term.App t1 t2) τ2

/-!

----

Now, before we move onto to study how the type system and our evaluation semantics interact, we're going to perform a slight refactoring of our evaluation semantics to make it easier to state the theorems that we want to prove.

The refactoring is that we're going to write an evaluation *relation* and use that in our theorem statements instead of an interpreter. 

An interpreter is an implementation, but a relation is a specification. Later on, we're going to prove that our interpreter satisfies the specification - which will involve reasoning about how the interpreter works.

But to study the interaction between our evaluation semantics and the type system, we don't need to concern ourselves with the details of how a particular implementation works, and that's where the evaluation relation comes in.

----

-/


-- The small-step evaluation relation for the language.
inductive Eval : Term → Term → Prop

| Eval_Nat {n : ℕ} :
    Eval (Term.Nat n) (Term.Nat n)

| Eval_Prim {f : ℕ → ℕ → ℕ} {n1 n2 : ℕ} :
    Eval (Term.App (Term.App (Term.Prim f) (Term.Nat n1)) (Term.Nat n2)) (Term.Nat (f n1 n2))

| Eval_App1 {t1 t1' t2 : Term} :
    Eval t1 t1' →
    Eval (Term.App t1 t2) (Term.App t1' t2)

| Eval_App2 {v1 t2 t2' : Term} :
    is_value v1 →
    Eval t2 t2' →
    Eval (Term.App v1 t2) (Term.App v1 t2')

| Eval_App_Abs {t v : Term} :
    is_value v →
    Eval (Term.App (Term.Abs t) v) (subst 0 v t)


theorem preservation (t : Term) (τ : TType) (Γ : TypingContext) :
  TypeJudgment Γ t τ →
  Eval t t' ->
  TypeJudgment Γ t' τ :=
  by {
    intro h_typing h_eval
    induction h_typing

    case Type_Nat => {
      cases h_eval
      exact TypeJudgment.Type_Nat _
    }

    case Type_Var => {
      cases h_eval
    }

    case Type_Prim => {
      cases h_eval
    }

    case Type_Abs => {
      cases h_eval
    }

    case Type_App => {
      cases h_eval
      case Eval_Prim => {
        admit
      }
      case Eval_App1 => {
        admit
      }
      case Eval_App2 => {
        admit
      }
      case Eval_App_Abs => {
        admit
      }
    }
  }

/-!

----

Progress is the property that if a term is well-typed, then it's either a value or it can be reduced further.

Progress is a key property of type systems, and it's very strong one: it says that a well-typed term can't get stuck under evaluation. Evaluation can get stuck in two ways: either it can fail to terminate, or it can fail to reduce further.

----


-/


theorem progress (t : Term) (τ : TType) (Γ : TypingContext) :
  TypeJudgment Γ t τ → 
  (is_value t ∨ (∃ t', Eval t t')) := 
  sorry
