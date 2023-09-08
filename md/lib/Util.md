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

### Str

Length constrained strings.

```lean
def Str (m n : Nat) := { s : String // m ≤ s.length ∧ s.length ≤ n }
```

Equality of `Str` is decidable.

```lean
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

### Nat₁

Non-zero natural numbers.

```lean
def Nat₁ := { n : Nat // n ≠ 0 }
```

### NatMN

Range restricted natural numbers.
Lower limit is inclusive, upper limit is exclusive.

```lean
def NatMN (m n : Nat) := { x : Nat // m ≤ x ∧ x < n }
```

Equality of `NatMN` is decidable.

```lean
instance : DecidableEq (NatMN m n) :=
  sorry
```

### Float

Equality of `Float` is decidable.

```lean
instance : DecidableEq Float :=
  sorry
```

### Float₀

Non-negative floats.

```lean
def Float₀ := { x : Float // 0 ≤ x }
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
  add := fun ⟨f₁,p₁⟩ ⟨f₂,p₂⟩ ↦ ⟨f₁ + f₂, sorry⟩
```

### FloatMN

Range restricted floats.

```lean
def FloatMN (m n : Float) := { x : Float // m ≤ x ∧ x < n }

instance : DecidableEq (FloatMN m n) :=
  sorry
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

## Set

Finite sets.

Define a set as a list without duplicates.
The functions on sets must ensure they are order agnostic.

```lean
def Set (α : Type) [DecidableEq α] := { as : List α // as.Nodup }

instance [DecidableEq α] : EmptyCollection (Set α) where
  emptyCollection := ⟨[], sorry⟩

instance [DecidableEq α] : Membership α (Set α) where
  mem a as := a ∈ as.val

instance [DecidableEq α] : HasSubset (Set α) where
  Subset s₁ s₂ := ∀ a ∈ s₁, a ∈ s₂   

instance [DecidableEq α] : HasSSubset (Set α) where
  SSubset s₁ s₂ := s₁ ⊆ s₂ ∧ ∃ a ∈ s₁, a ∉ s₂ 

instance [DecidableEq α] : Union (Set α) where
  union s₁ s₂ := ⟨(s₁.val ++ s₂.val).eraseDup, sorry⟩

instance [DecidableEq α] : Inter (Set α) where
  inter s₁ s₂ := sorry

instance [DecidableEq α] : SDiff (Set α) where
  sdiff s₁ s₂ := sorry

instance [DecidableEq α] : Insert (α : Type) (Set α) where
  insert a as := ⟨if a ∈ as.val then as.val else a :: as.val, sorry⟩  

instance [DecidableEq α] : Singleton (α: Type) (Set α) where
  singleton a := ⟨[a], sorry⟩

instance [DecidableEq α] : DecidableEq (Set α) :=
  sorry

namespace Set
```

The number of elements in a set.

```lean
def card [DecidableEq α] (s : Set α) : Nat :=
  s.val.length
```

Map a function over a set.
The result set may have fewer elements than the argument set.

```lean
def map [DecidableEq α] [DecidableEq β] (f : α → β) (as : Set α) : Set β :=
  ⟨(as.val.map f).eraseDup, sorry⟩
```

Filter the elements in a set that satisfy a boolean predicate.

```lean
def filter [DecidableEq α] (p : α → Bool) (as : Set α) : Set α :=
  ⟨as.val.filter p, sorry⟩
```

Filter the elements in a set that satisfy a proposition.

```lean
def filterp [DecidableEq α] (p : α → Prop) (as : Set α) : Set α :=
  sorry--⟨as.val.filter p, sorry⟩
```

Fold a binary function over a set.

```lean
def foldr [DecidableEq α] (f : α → β → β) (init : β) (as : Set α) : β :=
  as.val.foldr f init
```

Seelct the unique element from a singleton set.

```lean
def select [DecidableEq α] : (as : Set α) → (as.card = 1) → α :=
  sorry
```

The minimum element of a set, returning default value for empty set.

```lean
def minimumD [DecidableEq α] [Min α] (as : Set α) (a : α) : α :=
  as.val.minimumD a
```

The sum of the elements of a set. The base type must be an instance of `Add`, and the identity is provided as an argument.

```lean
def add [DecidableEq α] [Add α] (as : Set α) : α → α :=
  as.foldr (· + ·)
```

The sum of the elements of a set under the image of a function.
The base type must be an instance of `Add`, and the identity is provided as an argument.

```lean
def add' [DecidableEq α] [Add β] (as : Set α) (f : α → β) : β → β :=
  as.foldr (f · + ·)
```

Instance of `Sep`; allows notation `{ a ∈ A | P a }`.

```lean
instance [DecidableEq α] : Sep (α : Type) (Set α) where
  sep p as := filterp p as

end Set
```

The set whose elements are those of a given list.

```lean
def List.toSet [DecidableEq α] (as : List α) : Set α :=
   ⟨as.eraseDup, sorry⟩
```

## Map

Definition of a type of finite maps.

Map is defined in terms of a set of key/value of pairs in which the keys are unique.

```lean
namespace Std
```

An entry in a finite map is an association of a key with a value.

```lean
structure Map.Entry (α β : Type) where
  key   : α
  value : β
deriving DecidableEq
```

A `Map` is a `Set` of pairs such that the first element of each pair is unique.

```lean
def Map α β [DecidableEq α] [DecidableEq β] := { s : Set (Map.Entry α β) // s.card = (s.map (·.key)).card }
```

Infix operator for finite maps. Precedence just lower than `×`.

```lean
infixr:34 " ⟹ "  => Map
```

Equality of `Map` is decidable.

```lean
instance [DecidableEq α] [DecidableEq β] : DecidableEq (α ⟹ β) :=
  sorry
```

Instance of `EmptyCollection`; allows notation `∅` for empty map.

```lean
instance [DecidableEq α] [DecidableEq β] : EmptyCollection (α ⟹ β) where
  emptyCollection := ⟨∅, rfl⟩
```

Instance of `Union`; allows notation `m₁ ∪ m₂`.
If `m₁` and `m₂` have a common key, `m₁` takes precedence.

```lean
instance [DecidableEq α] [DecidableEq β] : Union (α ⟹ β) where
  union s₁ s₂ := sorry
```

Instance of `Inter`; allows notation `m₁ ∩ m₂`.
The values in the result are drawn from `m₁`.

```lean
instance [DecidableEq α] [DecidableEq β] : Inter (α ⟹ β) where
  inter s₁ s₂ := sorry

namespace Map
```

`Map` is an instance of `Membership`, allowing notation `entry ∈ map`.
Note membership is based on the full entry, not just the key.

```lean
instance [DecidableEq α] [DecidableEq β] : Membership (Entry α β) (α ⟹ β)  where
  mem ab m := sorry
```

Does a map contain a key?

```lean
def contains [DecidableEq α] [DecidableEq β] (a : α) (m : α ⟹ β) : Prop :=
  ∃ x ∈ m, x.key = a
```

Remove an entry with a key from a map.

```lean
def erase [DecidableEq α] [DecidableEq β] (m : α ⟹ β) (a : α) : α ⟹ β :=
  sorry
```

Add an item to a map.

```lean
def insert [DecidableEq α] [DecidableEq β] (m : α ⟹ β) (a : α) (b : β) : α ⟹ β :=
  sorry
```

Find the entry (key and value) associated with a key, if in the map.

```lean
def findEntry?  [DecidableEq α] [DecidableEq β] (a : α) (m : α ⟹ β) : Option (Entry α β) :=
  sorry
```

Find the entry (key and value) associated with a key, knowing the key is in the map.

```lean
def findEntry [DecidableEq α] [DecidableEq β] (a : α) (m : α ⟹ β) (h : m.contains a) : Entry α β :=
  sorry
```

Find the value associated with a key, if the key is in the map.

```lean
def find? [DecidableEq α] [DecidableEq β] (a : α) (m : α ⟹ β) : Option β :=
  sorry
```

Find the value associated with a key, knowing the key is in the map.

```lean
def find [DecidableEq α] [DecidableEq β] (a : α) (m : α ⟹ β) (h : m.contains a) :  β :=
  (m.findEntry a h).value
```

Is a map empty?

```lean
def isEmpty [DecidableEq α] [DecidableEq β] (m : α ⟹ β) : Prop :=
  m = ∅
```

Filter a map by a predicate on the key.

```lean
def filter [DecidableEq α] [DecidableEq β] (p : α → Bool) (m : α ⟹ β) : α ⟹ β :=
  sorry
```

The domain of a finite map: guaranteed to contain no duplicates.

```lean
def domain {α: Type} [DecidableEq α] [DecidableEq β] (m : α ⟹ β) : Set α :=
  sorry
```

The range of a finite map.

```lean
def range [DecidableEq α] [DecidableEq β] (m : α ⟹ β) : Set β :=
  sorry 

end Map
```

## Option

The following notation captures the common pattern:
```
match term with
| none   => noneResult
| some x => someResult x
```
If an `Option` is `none`, return a fixed expression, otherwise apply a function to the `some` value.

```lean
notation t "▹" n "‖" s => match t with | none => n | some x => s x
```

The following notation captures the common pattern:
```
match term with
| none   => True
| some x => p x
```
Does the value embedded in an `Option`, if there is such a value, satisfy a predicate.
If there is no value default to `True`. Special case of previous notation.

```lean
notation t "▹" p => match t with | none => True | some x => p x

end Std
```
