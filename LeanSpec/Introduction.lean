/-!
# Introduction

In the context of mathematics, proof is critical. There is little value in stating a
theorem unless there is intent to prove that theorem, or perhaps pose a challenge to the
mathematical community. Often the statement of the theorem is simple, but its proof is
long and complex.

For software development, proof is less critical, though that is not to say it is not
important. The statement of a theorem is a program specification. A proof of the
theorem yields a program that satisfies the specification, or a program separately
constructed can be verified correct with respect to the specification. However,
_routine_ formal verification of programs is not common outside of research activities,
though there are noticeable examples in industry.

What about the specifications themselves? Theorems without proof are of limited
value in mathematics, but specification without proof in software development is
highly valuable. A specification provides a complete and unambiguous statement of
what the software must achieve. Any questions relating to functionality can be
addressed by referring to the specification. Furthermore, while routine proof is
beyond current capability, routine formal specification is a viable goal.

Consider one typical scenario for software development in industry. A collection of
use cases is created capturing the functionality and actor interactions. From this,
the requirements specification is written, consisting of a collection of
individual requirements, presented as __shall__ clauses. For those requirements, a
design is created employing the Unified Modelling Language (UML), which consists of
diagrams (class, state, sequence, etc) supported by natural language descriptive text.
However, a large part of the output of this process is natural language text, with all
the vagueness and ambiguity that entails. Experience shows that, despite significant
effort being expended on using precise language, specifications and designs are open to
interpretation. A designer may misinterpret the intent of a requirement, a software
developer the intent of a requirement or design clause, a tester the intent of a
requirement, etc. The potential for misinterpretation is increased because because the
context is not always clear in informal presentations. A balance has to be
maintained with requirements to, on the one hand, be concise and to the point, and on
the other hand, provide enough contextual information to ensure correct interpretation.

Formal specifications are precise and unambiguous due the the semantics of the
underlying formal language. Mathematical notation, which has evolved over hundreds of
years, allows concise expression of specifications. The formal notation further ensures
context is unambiguous (i.e. everything on which the specification depends is explicit).
Dependently typed languages are particularly suited to program specification because of
the tight integration between specification language, programming language, and proof
framework. In the case of Lean, they are one and the same language. Furthermore, the
concept of dependent type provides a richness of expression not available in
non-dependent approaches.

# Lean As A Specification Language

This tutorial is not intended to be a comprehensive description of the Lean language
and its logic. Here we provide an overview of the more salient parts to allow understanding
of later sections. Full details can be found in the [Lean 4 Manual](https://leanprover.github.io/lean4/doc/).
The most relevant content is:
* [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean4/title_page.html)
for the logic and proof;
* [Functional Programming in Lean](https://leanprover.github.io/lean4/doc/fplean.html)
for the programming language.

## Lean Logic

The Lean logic includes the usual propositional connectives and quantifiers:

| Connective | Meaning                    |
| ---------- | -------------------------- |
| P ∧ Q      | Conjunction                |
| P ∨ Q      | Disjunction                |
| P → Q      | Implication                |
| P ↔ Q      | Logical Equivalence        |
| ¬ P        | Negation                   |
| ∀x, P x    | Universal Quantification   |
| ∃x, P x    | Existential Quantification |
| True       | Always true proposition    |
| False      | Never true proposition     |

## Lean Types

Some of the types provided by Lean are:

| Connective  | Meaning            |
| ----------- | ------------------- |
| T × U       | Cartesian Product   |
| T ⊕ U       | Disjoint Union      |
| T → U       | Function Type       |
| Nat         | Natural Numbers     |
| String      | Character Sequences |
| List T      | Finite Sequences of T's |
| (a:A) → B a | Dependent Function  |
| (a:A) × B a | Dependent Product   |

Most of these types are common with many other languages. The last two are
characteristic of dependent type theory. The function and Cartesian product types
are the degenerate cases of the dependent function and product types (respectively)
in which there is no dependence between the type arguments.

## Types, Propositions and Specifications

The propositional connectives and quantifiers provided by Lean are commonly understood,
as are the non-dependent types. The dependent function and product types are less
familiar and give dependent type theory (and hence Lean) its unique flavour.

Consider the specification of a function that doubles a number. Its property
is captured by:
-/
def DoubleProp := ∀n : Nat, ∃m : Nat, m = 2 * n

/-
A simple specification, but not quite what we want. In Lean propositions have
no computational content, they are either provable or not provable, so we need
to define a function separately and prove it satisfies the proposition.

Types, on the other hand, have data and computational content. If we had a type
that captured the same meaning as the proposition, then an element of the type
would be a function satisfying the proposition. It is the expressive power of
dependent type theory that allows us to construct types of this nature. Given the
dependent function corresponds to universal quantification, and dependent product
corresponds to existential quantification, we might try something like:
-/
def Double₁ := (n : Nat) → (m : Nat) × sorry -- m = 2 * n

/-
Here we have a function that takes `n : Nat` as argument, and returns a pair.
The first element of the pair is a number `m : Nat`, and the second element is
something that captures the desired relationship `m = 2 * n`. The problem
we have here is the second argument of a product is a type, but the property
we want to express is a proposition (which in Lean is not the same as a type).

We need a hybrid that captures the data aspect of the dependent product, and the
propositional aspect of the existential quantifier. Lean has such an entity: the _subtype_.
A subtype is of the form `{ a : A // P a }` where `A` is a type and `P a` is a
proposition. The elements of the subtype are those elements `a` of type `A` such that
the proposition `P a` holds. The specification becomes:
-/
def Double₂ := (n : Nat) → { m : Nat // m = 2 * n }

/-
`Double₂` is a type; the type of functions that take a natural number as argument
and double the argument.

When specifying functions we can move universally quantified variables and function arguments
to the left of the `:=`:
-/
def Double₃ (n : Nat) := { m : Nat // m = 2 * n }

/-
This latter approach will in general be used throughout the tutorial.

Strictly, an element of `{ a : A // P a }` is not simply an element of `A`, it is
a pair whose first component is an element `a` of type `A`, and whose second
component is evidence of `P a`. If we were to define a function that meets this
specification it would look like:
-/
def double (n : Nat) : { m : Nat // m = 2 * n } :=
  {val := 2 * n, property := rfl}

/-
The result is the number (`val`) and evidence the number is twice the argument
(`property`, where the evidence here is simply shown by reflexivity). In some
situations Lean can coerce, automatically, an element of the subtype to the embedded
data value. When this is not possible, the value must be referenced explicitly.

We can then check that `double` does indeed implement the specification `Double₃`.
That is `double n` is of type `Double₃ n` for any `n`:
-/
variable (n : Nat)
#check (double n : Double₃ n)

/-
We also have:
-/
#check (double : Double₂)

/-
A program that corresponds directly to a specification includes not just the computational
component, but the evidence that it meets the specified constraints. With large specifications
that have multiple, nested subtypes, this evidence becomes rather large. From a purely programming
perspective we are only interested in the computational content. In the case of `double` the
function we really want is:
-/
def double₁ (n : Nat) : Nat :=
  2 * n

/-
The non-computational content is not problematic. It does not intrude when constructing
specifications, and it is essential for deriving/verifying programs. Removal of the
non-computational content can be automated at the compilation stage. In fact, the evaluation
-/
#eval double 4
/-
outputs the value `8`, not the complete subtype structure.

Notes:

- While the subtype is used extensively in program specification, the dependent product type turns out
to be of less use than might be expected.

- This tutorial has been developed as a Lean script that can be
loaded into a Lean IDE such as Visual Studio Code. Lean requires that any value
be defined before it is used, which imposes a strict constraint on how a
specification is presented. Often it is preferable to present in a top-down manner,
starting with higher level concepts that are iteratively broken down into their
components. The Lean definition-before-use requirement means that specifications are
presented in a bottom-up manner.

- The specifications in this tutorial use definitions from core Lean and the Lean 4
standard library ([std4](https://github.com/leanprover/std4)).

- Standard Lean naming convention is adopted. Type and proposition names are camel case
with initial upper case. Function names are camel case with initial lower case.
-/