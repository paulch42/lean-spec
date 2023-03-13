# General Purpose Functions

This module defines generic functions and types. The nature of the definitions is such that
they could reasonably appear in the Lean standard library at a future date. Items are
included only if needed in support of the examples in the tutorial.

The focus of this tutorial is specification, not proof or implementation. Most instances
where a proof is required are left as `sorry`.

```lean
import Std.Data.AssocList
```

## Restricted Basic Types

Length constrained strings.

```lean
def Str (m n : Nat) := { s : String // m ≤ s.length ∧ s.length ≤ n }

instance : DecidableEq (Str m n) :=
  sorry
```

The `<` order relation on `Str`.

```lean
instance (m n : Nat) : LT (Str m n) where
  lt s₀ s₁ := s₀.val < s₁.val
```

The `<` relation is decidable.

```lean
instance (m n : Nat) (x y : Str m n) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))
```

Non-zero natural numbers.

```lean
def Nat₁ := { n : Nat // n ≠ 0 }
```

Range restricted natural numbers.

```lean
def NatMN (m n : Nat) := { x : Nat // m ≤ x ∧ x < n }
```

State decidable equality for `Float`.

```lean
instance : DecidableEq Float :=
  sorry
```

Non-negative floats.

```lean
def Float₀ := { x : Float // x ≥ 0 }
deriving DecidableEq
```

The `<` order relation on `Float₀`.

```lean
instance : LT Float₀ where
  lt f₀ f₁ := f₀.val < f₁.val
```

The `<` relation is decidable.

```lean
instance (x y : Float₀) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.val < y.val))
```

The `≤` order relation on `Float₀`.

```lean
instance : LE Float₀ where
  le f₀ f₁ := f₀.val ≤ f₁.val
```

The `≤` relation is decidable.

```lean
instance (x y : Float₀) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val))
```

Addition of two `Float₀`s.

```lean
instance : Add Float₀ where
  add := fun ⟨f₁,_⟩ ⟨f₂,_⟩ ↦ ⟨f₁ + f₂, sorry⟩
```

Range restricted floats.

```lean
def FloatMN (m n : Float) := { x : Float // m ≤ x ∧ x < n }
```

## List

```lean
namespace List
```

The number of occurrences of an element in a list.

```lean
def numOccurs [BEq α] (a : α) : List α → Nat
  | []    => 0
  | b::as => if a == b then numOccurs a as + 1 else numOccurs a as
```

The sum of the elements of a list. The base type must be an instance of `Add`, and the identity is provided as an argument.

```lean
def add [Add α] (as : List α) : α → α :=
  as.foldr (· + ·)
```

The product of the elements of a list. The base type must be an instance of `Mul`, and the identity is provided as an argument.

```lean
def mul [Mul α] (as : List α) : α → α :=
  as.foldr (· * ·)
```

The maximum of the elements of a list. The base type must be an instance of `Max`, and the empty case is provided as an argument.

```lean
def max [Max α] (as : List α) : α → α :=
  as.foldr Max.max
```

The minimum of the elements of a list. The base type must be an instance of `Min`, and the empty case is provided as an argument.

```lean
def min [Min α] (as : List α) : α → α :=
  as.foldr Min.min
```

The minimum element of a list, returning default value for empty list.

```lean
def minimumD [Min α] (as : List α) (a : α) : α :=
  match as.minimum? with
  | none   => a
  | some a => a
```

Set equality relation on lists: same elements regardless of order or multiplicity.

```lean
def seteq (as bs : List α) :=
  ∀ a : α, a ∈ as ↔ a ∈ bs
```

Are the elements of a list in ascending order?

```lean
def ascending [LE α] : List α → Prop
 | [] | [_] => True
 | a::b::as => a ≤ b ∧ ascending (b::as)
```

Are the elements of a list in strict ascending order?

```lean
def ascendingStrict [LT α] : List α → Prop
 | [] | [_] => True
 | a::b::as => a < b ∧ ascendingStrict (b::as)
```

Are the elements of a list in descending order?

```lean
def descending [LE α] : List α → Prop
 | [] | [_] => True
 | a::b::as => a ≥ b ∧ descending (b::as)
```

Are the elements of a list in strict descending order?

```lean
def descendingStrict [LT α] : List α → Prop
 | [] | [_] => True
 | a::b::as => a > b ∧ descendingStrict (b::as)

end List
```

## AssocList

Elements of type `AssocList` are lists whose elements are key/value pairs.
`AssocList` is defined in [std4](https://github.com/leanprover/std4).

```lean
namespace Std.AssocList
```

The domain of an `AssocList` is the list of the first elements in the pairs.

```lean
def domain (al : AssocList α β) : List α :=
  al.toList.map (·.fst)
```

The range of an `AssocList` is the list of the second elements in the pairs.

```lean
def range (al : AssocList α β) : List β :=
   al.toList.map (·.snd)
```

An `AssocList` is a finite map if there are no duplicate elements in its domain.

```lean
def isMap [BEq α] (al : AssocList α β) : Bool :=
  let dom := al.domain
  dom.length = dom.eraseDups.length
```

Find the value associated with a key, knowing the key is in the list.

```lean
def find [BEq α] (a : α) (al : AssocList α β) (h : al.contains a) :  β :=
  sorry
```

Find the entry (key and value) associated with a key, knowing the key is in the list.

```lean
def findEntry [BEq α] (a : α) (al : AssocList α β) (h : al.contains a) : α × β :=
  sorry
```

Filter an association list by a predicate on the key.

```lean
def filter [BEq α] (p : α → Bool) : AssocList α β → AssocList α β
  | nil          => nil
  | cons a b abs => if p a then cons a b (abs.filter p) else abs.filter p

end Std.AssocList
```

## Map

Definition of a type of finite maps.

Map is defined in terms of association lists in which keys are associated with
only one value.

```lean
namespace Std
```

A `Map` is an `AssocList` whose domain contains no duplicates.

```lean
def Map α β [BEq α] := { al : AssocList α β // al.isMap }
```

Infix operator for finite maps. Precedence just lower than `×`.

```lean
infixr:34 " ⟹ "  => Map

instance [BEq α] : EmptyCollection (α ⟹ β) where
  emptyCollection := ⟨∅, rfl⟩
```

Many of the functions are `Map` versions of the corresponding `AssocList` functions.

Question: could some of these definitions be avoided through coercion?

```lean
namespace Map
```

Does a map contain a key?

```lean
def contains [BEq α] (a : α) (m : α ⟹ β) : Bool :=
  m.val.contains a
```

Remove an entry with a key from a map.

```lean
def erase [BEq α] (m : α ⟹ β) (a : α) : α ⟹ β :=
  ⟨m.val.erase a, sorry⟩
```

Add an item to a map.

```lean
def add [BEq α] (m : α ⟹ β) (a : α) (b : β) : α ⟹ β :=
  ⟨(m.erase a).val.cons a b, sorry⟩
```

Find the entry (key and value) associated with a key, if in the map.

```lean
def findEntry? [BEq α] (a : α) (m : α ⟹ β) : Option (α × β) :=
  m.val.findEntry? a
```

Find the entry (key and value) associated with a key, knowing the key is in the map.

```lean
def findEntry [BEq α] (a : α) (m : α ⟹ β) (h : m.contains a) : α × β :=
  m.val.findEntry a h
```

Find the value associated with a key, if the key is in the map.

```lean
def find? [BEq α] (a : α) (m : α ⟹ β) : Option β :=
  m.val.find? a
```

Find the value associated with a key, knowing the key is in the map.

```lean
def find [BEq α] (a : α) (m : α ⟹ β) (h : m.contains a) :  β :=
  (m.findEntry a h).2
```

`Map` is an instance of `Membership`, allowing notation `entry ∈ map`.
Note membership is based on the full entry, not just the key.

```lean
instance [BEq α] : Membership (α × β) (α ⟹ β)  where
  mem ab m := (m.findEntry? ab.1).isSome
```

The list of pairs extracted from a map.

```lean
def toList [BEq α] (m : α ⟹ β) : List (α × β) :=
  m.val.toList
```

Is a map empty?

```lean
def isEmpty [BEq α] (m : α ⟹ β) : Bool :=
  m.val.isEmpty
```

Filter a map by a predicate on the key.

```lean
def filter [BEq α] (p : α → Bool) (m : α ⟹ β) : α ⟹ β :=
  ⟨m.val.filter p, sorry⟩
```

The domain of a finite map: guaranteed to contain no duplicates.

```lean
def domain {α: Type} [BEq α] (m : α ⟹ β) : List α :=
  m.val.domain
```

The range of a finite map.

```lean
def range [BEq α] (m : α ⟹ β) : List β :=
  m.val.range 

end Map

end Std
```
