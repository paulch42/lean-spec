# Specification in Lean

[Lean](https://leanprover.github.io) is a dependently typed functional programming language that incorporates
the correspondence between propositions and types (and between proofs and programs).
As such it is able to serve as a basis for the formalisation of mathematics (i.e., the
statement and proof of theorems). Indeed, a considerable body of mathematics has
been formalised in Lean, and is packaged as
[mathlib4](https://github.com/leanprover-community/mathlib4). A good introduction to the
use of Lean for the formalisation of mathematics is
[Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean4/).

The programming language component of Lean (version 4) is a comprehensive functional programming language, in the style
of [Haskell](https://www.haskell.org). A good introduction to the
use of Lean as a programming language is
[Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/). While Haskell has a more traditional type system, the dependently typed system of Lean
and its underlying logic bring a number of benefits from a software perspective:
* Lean is a fully featured specification language. It can be used to specify the
functionality of software that can be implemented in Lean or other languages.
* Lean software can be verified in Lean itself (using the same logic employed for
mathematical proof).
* When a Lean specification is viewed as a theorem in the Lean logic, a proof of that
theorem yields a program that satisfies the specification.

The cost of this capability is that the type system is undecidable: the system cannot,
given a program and a type (specification), determine automatically whether the program
meets the specification. A proof is required. When the dependent type theory of Lean is
used to its full capacity, _type correctness = program correctness_.

This tutorial is an introduction to the use of Lean for the specification of software
functionality. The aim is to express what a function is intended to achieve, not how
it is achieved. How one might verify or derive a program that meets a specification using the Lean
logic is not addressed here. The contents of this tutorial are:

|   |   |
| - | - |
| [Introduction](md/Introduction.md)    | Introduction to Lean as a specification language |
| [Quotient & Remainder](md/QuotRem.md) | Quotient and remainder on division |
| [Sort](md/Sort.md)                    | Sorting a list of items |
| [Knapsack](md/Knapsack.md)            | Knapsack: an optimisation problem |
| [Graph](md/Graph.md)                  | Graph searching |
| [TMI](md/TMI.md)                      | A scheduling example from the aviation industry |
| [Flight Planning](md/FPL.md)          | Flight planning message processing example from the aviation industry |

The following supplementary modules support the example specifications:

|   |   |
| - | - |
| [Util](md/lib/Util.md)         | General purpose functions that could in future appear in a standard library |
| [Temporal](md/lib/Temporal.md) | A simple theory of dates, times, durations and intervals |
| [Geo](md/lib/Geo.md)           | Basic geospatial entities |

Some discussion on the use of Lean for specifications is [here](Discussion.md) (__to do__).

## Creating The Markdown Files

The files are Lean scripts from which markdown is generated using the [mdgen](https://github.com/Seasawher/mdgen) tool.

Build the markdown files with `lake exe mdgen LeanSpec md`.

## Acknowledgement

Thanks to Kevin Buzzard, Mario Caneiro and Partick Massot for their valuable comments.