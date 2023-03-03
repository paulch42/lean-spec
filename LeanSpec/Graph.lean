/-
# Example: Graph Search

This example looks at searching for paths through a graph.
-/
import LeanSpec.lib.Util

/-
## Non-Empty Lists

Before we get on to graphs, sometimes it is useful to know when working with lists
that a list is guaranteed to be non-empty. A possible model of such lists is:
-/
structure List₁ (α : Type) where
  list : List α
  inv  : list ≠ []

/-
An element of `List₁` is a structure containing a core Lean list (which may be empty),
and a proof the list is non-empty.

This example shows how Lean `structure`s are more powerful than records of traditional languages.
The second element `inv : list ≠ []` is not data, but rather a constraint on the first element.
The empty list is not a member of the type because we can never prove `[] ≠ []`.

If a type is an instance of the `HasSubset` class, we can use `⊆` notation.
-/
instance : HasSubset (List₁ α) where
  Subset l₁ l₂ := l₁.list ⊆ l₂.list

/-
The definition simply delegates to the underlying `List`, which is already an instance of `HasSubset`.

Since the list is guaranteed non-empty, functions that extract the first and last element are
total.
-/
def first : List₁ α → α
  | ⟨a::_, _⟩ => a 

def last : List₁ α → α
  | ⟨[a], _⟩      => a
  | ⟨_::a::as, _⟩ => last ⟨a::as, by simp⟩ 

/-
## Graphs

All we need for a node in the graph is to be able to distinguish it from other nodes,
so `String` is adequate for our needs.
-/
abbrev Node := String

/-
An edge has a start and an end node, hence is directed, and a cost to traverse from
the start to the end.
-/
structure Edge where
  starts : Node
  ends   : Node
  cost   : Nat

/-
A graph is simply a non-empty list of edges. We don't consider empty graphs here.
-/
abbrev Graph := List₁ Edge

/-
With the above definitions we can define a path over a graph.
-/
structure Path (g : Graph) where
  path   : List₁ Edge
  inv₁   : path ⊆ g
  inv₂   : ∀ ee ∈ path.list.consecutivePairs, ee.1.ends = ee.2.starts

/-
`Path` is dependent on `Graph`, so given `g : Graph`, `Path g` is the type of paths
over the graph `g`. The elements are:
- `path` is the ordered list of edges that constitute the path;
- `inv₁` states every edge in the path is also in the graph;
- `inv₂` states that given two consecutive edges, the end node of the first is the start node
of the second. (Refer to function `consecutivePairs` defined in `lib/Util`.)

Notes:
- The fields named `inv`, possibly subscripted, specify invariants. That is, they
specify the constraints any instance of the type must satisfy. The `inv` fields
themselves contain no data or computational content, they serve to restrict the
values allowed in the other fields.
- In subsequent definitions, the convention adopted is that fields named `inv`
always capture constraints on the type.

Let's define a couple of convenience functions to identify the nodes at the start and end
of a path.
-/
def pathStart (p : Path g) : Node :=
  (first p.path).starts

def pathEnd (p : Path g) : Node :=
  (last p.path).ends

/-
## Graph Search

We can now specify a function that finds a path through a graph. A first attempt
might be:
-/
def FindPath₁ (g : Graph) (s e : Node) :=
  { p : Path g // pathStart p = s ∧ pathEnd p = e }

/-
Given a graph `g` and a pair of nodes `s` and `e`, find a path over `g` whose start is `s` and end is `e`.
Seems reasonable, but a program meeting this specification cannot be derived. The goal is to find a path
but there is no guarantee such a path exists. The are two possible reasons:

- the specification does not require `s` or `e` to be in the graph;
- even if `s` and `e` are in the graph, there is no guarantee a path between them exists.

What about:
-/
def FindPath₂ (g : Graph) (s e : Node) :=
  Option { p : Path g // pathStart p = s ∧ pathEnd p = e }

/-
This at least accommodates the failure cases described above, but it has a trivial implementation that
is not what is intended:
-/
def findPath (g : Graph) (s e : Node) :
  Option { p : Path g // pathStart p = s ∧ pathEnd p = e } := none

/-
If we always choose the `none` option the specification is satisfied.

Going back to the first attempt, `FindPath₁`, let's give it a more meaningful name since it doesn't
guarantee a solution exists: 
-/
def IsPath (g : Graph) (s e : Node) := { p : Path g // pathStart p = s ∧ pathEnd p = e }

/-
In the case a path exists we want to create an element of `IsPath g s e` (the type of paths from
`s` to `e` over `g`). If no path exists, we need to provide evidence for said fact. At the
propositional level this would be `¬ P`, which is definitionally equal to `P → False`, and when
working at the type level this becomes `T → Empty`. Consequently, we are led to the definition: 
-/
def FindPath₃ (g : Graph) (s e : Node) :=
  IsPath g s e ⊕ (IsPath g s e → Empty)

/-
`⊕` is the disjoint/discriminated union type, also called `Sum`.

`FindPath₃` returns a disjoint sum. If a path exists it is returned as the left injection.
If no path exists, evidence is returned as the right injection.

## Shortest Path

The cost of a path is the sum of the cost of the edges in the path.
-/
def pathCost (p : Path g) : Nat :=
  (p.path.list.map (·.cost)).add 0

/-
Finding the shortest path through a graph is an optimisation problem so we have
the same pattern as `Knapsack`:
-/
def ShortestPath (g : Graph) (s e : Node) (_ : IsPath g s e) :=
  { p : IsPath g s e // ∀ q : IsPath g s e, pathCost p.val ≤ pathCost q.val }

/-
The solution is a path over `g` from `s` to `e` with the constraint that any other path
costs at least as much as the solution.

One difference here is the precondition `(_ : IsPath g s e)`. We have avoided the disjoint
sum in the specification of `ShortestPath` by requiring there is at least one path.

## Exercises

- Modify the specification of `ShortestPath` such that it does not assume the existence of a path.

- Specify the property that a graph has no edges with identical start and end nodes.

- Specify the property that a graph is acyclic.
-/