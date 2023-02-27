# Example: Knapsack

This is a simple example of the specification of an optimisation problem: the
[knapsack problem](https://en.wikipedia.org/wiki/Knapsack_problem).

```lean
import LeanSpec.lib.Util
```

Given is a set of items each with a weight (cost) and a value. The aim is to choose
the optimal set of items that maximises the value but whose weight does not exceed the
capacity of the knapsack.

## Item

First, define a structure that represents an item in the knapsack.

```lean
structure Item where
  value : Nat
  cost  : Nat
deriving BEq
```

Each item simply has a value and a cost. Note there may be multiple items in the
knapsack with the same value and cost.

A `structure` is Lean's equivalent of a `record` or a `struct` in other languages; it 
packages separate elements into a single unit. However, as we shall see later, Lean's
structures are rather more powerful.

## cost

The cost of an item list is the sum of the costs of the individual items.

```lean
def cost (items : List Item) : Nat :=
  (items.map Item.cost).add 0
```

Map the function that extracts the cost of an item over the list, and sum the
resulting costs.

## value

The value of an item list is the sum of the values of the individual items.

```lean
def value (items : List Item) : Nat :=
  (items.map Item.value).add 0
```

## subList

A list `as` is a sublist of `bs` if every element in `as` is also an element of `bs`,
taking account of duplicates. For example, if `as` has two copies of an item, `bs` must
contain at least two copies of the same item.

```lean
def subList [BEq α] (as bs : List α) :=
  ∀ a : α, as.numOccurs a ≤ bs.numOccurs a
```

## candidate

A list of items is a candidate solution to the knapsack problem if its elements are
all drawn from the source items, and its cost does not exceed the capacity.

```lean
def candidate (capacity : Nat) (source : List Item) (candidate : List Item) :=
  subList candidate source ∧ cost candidate ≤ capacity
```

## Knapsack

With these definitions, we can specify the knapsack problem.

The optimal solution is a (not necessarily unique) candidate solution such that
no better candidate exists.

```lean
def knapsack₁ (capacity : Nat) (source : List Item) :=
  { opt : List Item
    // candidate capacity source opt ∧
       ∀ is : List Item, candidate capacity source is → value is ≤ value opt }
```

This is a nice example of where formal specification works very well.
We capture a problem by characterising the properties it must exhibit with no
thought for how how it might be implemented. In this case we define the nature
of a potential solution, then specify the result as the (not necessarily unique)
solution that is at least as good as any other solution. This is a fairly typical
pattern for specifying optimisation problems.

There are always multiple ways to specify the same problem. Below,
rather than a predicate that determines if a list of items is a potential
solution, we define the type of potential solutions.

```lean
def Candidate (capacity : Nat) (source : List Item) :=
  { cand : List Item // subList cand source ∧ cost cand ≤ capacity }
```

A element of type `Candidate capacity source` is any list whose elements are drawn from
`source` and whose cost does not exceed `capacity`.

With this definition of `Candidate`, the knapsack problem can be specified as:

```lean
def Knapsack₂ (capacity : Nat) (source : List Item) :=
  { opt : Candidate capacity source
    // ∀ cand : Candidate capacity source, value cand.val ≤ value opt.val }
```

In this approach the subtype property can assume `opt` is a candidate solution.
In the first definition the subtype property could only assume `opt` is an
arbitrary list of items.
