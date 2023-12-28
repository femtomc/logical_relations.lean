import Init.Prelude
import Mathlib.Data.Nat.Basic
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

* The type of syntax will be called `Term`, and the type of the values will be called `Value`.

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

inductive Value
| Nat : ℕ → Value
| Prim : Term -> Value
| Abs : Term -> Value
deriving Repr

/-!

----

A value is a special kind of term that represents a computed result and cannot be reduced or evaluated further.

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

-- We can run our evaluation interpreter and get results, but
-- we have to give it fuel!
#eval eval 10 [] (Term.App (Term.Abs (Term.Var 0)) (Term.Nat 7))

/-!

----

**Lesson 2: Simple type systems**

  .. epigraph::

    "For every λ, a type shall be its bind, to every term, a well-formedness, we'll find. 
    No more shall self-applying functions toll, for simple types have cleansed my soul."

    -- The Rime of the Simply Typed Mariner, 1834

In Lesson 2, we'll add types to the language, and prove that the type system is sound with respect to the operational semantics. 
What soundness means is that if the type system says a term has a certain type, then the operational semantics will never get stuck when evaluating that term.

We'll formulate this statement, and then prove it using a technique called logical relations.

This will be our first look at logical relations, which is a powerful technique for proving theorems about programming language semantics.

----
-/

inductive TType
| Nat : TType                     -- Type of natural numbers.
| Fun : TType → TType → TType   -- Function types from one type to another.

/-!

----

Our types are simple: we have natural numbers, and functions from one type to another. For pedagogy, we're not going to demonstrate how type systems avoid errors related to arithmetic (like passing Boolean values to functions which expect numbers).

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

theorem preservation (t : Term) (τ : TType) (Γ : TypingContext) :
  TypeJudgment Γ t τ →
  TypeJudgment Γ (eval 10 [] t) τ := 
  by 
    sorry

/-!

----

Preservation is the property that if a term has a type, then evaluating that term will not change its type.

More formally: if a term `t` is well-typed and evaluates to a term `t'` (according to evaluation semantics), then `t'` is also well-typed with the same type as `t`. Short & formal: if `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`.


-/
