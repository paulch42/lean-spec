/-
# Example: Quotient and Remainder

Computing the quotient and remainder is a basic function provided by all languages, including Lean.
However, it is a simple example that nicely demonstrates some basic features of Lean as a
specification language.

A specification of the property a function computing the quotient and remainder
should have is captured by the following proposition:
-/
def qr₁ := ∀ n d : Nat, d ≠ 0 → ∃ q r : Nat, n = d * q + r ∧ r < d

/-
As noted earlier, being a proposition, the specification has no computational
content. A proof of the proposition verifies a function computing the quotient and
remainder exists, but does not yield such a function. We need a type for the argument, a type
for the result, and a proposition to capture the relationship between the argument and result.
The dependent function type captures the functional nature, and the subtype captures the
the result and the property relating the result to the argument.
-/
def Qr₁ := (n d : Nat) → (d ≠ 0) →
           { qr : Nat × Nat // n = d * qr.1 + qr.2 ∧ qr.2 < d }

/-
`Qr₁` is the type of functions that take a natural  number `n`, a natural number `d`, evidence that `d` is non-zero,
and produce a pair of values that are the quotient and remainder when `n` is divided by `d`.
The data value in the result type is a pair (`Nat × Nat`) whose first element (`qr.1`) is the quotient
and second element (`qr.2`) is the remainder. (Note: `qr.fst` and `qr.snd` can be used respectively for `qr.1` and `qr.2`.)

It is interesting to note there is no fundamental difference between dependent functions and
the universal quantifier. We could write `Qr₁` as:
-/
def Qr₂ := ∀ n d : Nat, d ≠ 0 →
           { qr : Nat × Nat // n = d * qr.1 + qr.2 ∧ qr.2 < d }

/-
Despite the use of `∀`, `Qr₂` is still a type, not a proposition. `∀` is simply notation defined
in terms of the dependent function type. The presentation we choose is a matter of taste. The
convention usually adopted is to employ the dependent function type for a computable function,
and the universal quantifier when specifying a property.

The one difference is the type annotation is mandatory in a dependent function type,
but optional in a universal quantifier (if Lean is able to infer the type). For example,
`Qr₂` can be shortened to:
-/
def Qr₃ := ∀ n d, d ≠ 0 →
           { qr : Nat × Nat // n = d * qr.1 + qr.2 ∧ qr.2 < d }

/-
A function derived from the specification `Qr₂` has three arguments: the numerator,
the denominator, and evidence the denominator is non-zero. Alternatively, we could make
further use of the subtype to specify a function of two arguments:
-/
def Qr₄ := (n : Nat) → (d : { x : Nat // x ≠ 0 }) →
           { qr : Nat × Nat // n = d * qr.1 + qr.2 ∧ qr.2 < d }

/-
In this case the second argument is the subtype of natural numbers that excludes `0`, obviating
the need for the third argument. The two specifications are equivalent.

Moving the function arguments to the left of the `:=`:
-/
def Qr₅ (n : Nat) (d : { x : Nat // x ≠ 0 }) :=
           { qr : Nat × Nat // n = d * qr.1 + qr.2 ∧ qr.2 < d }
/-
`Qr₅` is the type of functions that take a natural number `n`, then a non-zero natural number `d`,
and produce a pair of numbers `(q,r)` such that `n = d * q + r ∧ r < d`.

## Exercises

- Specify a property that determines if a number is a prime number. Use the Lean remainder on division operator (`%`).

- Specify a property that determines if a number is a prime factor of another number.

- Specify a function that computes that maximum prime factor of a natural number greater than 1.
-/