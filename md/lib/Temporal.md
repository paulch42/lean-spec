# Temporal Definitions

This module is a very simple model of temporal entities: date, time, duration, interval.
It draws from [ISO 8601](https://www.iso.org/iso-8601-date-and-time-format.html) and
[RFC 3339](https://www.rfc-editor.org/rfc/rfc3339), but would need considerable
work to serve as a serious model. It provides sufficient detail to serve as a basis
for the specifications presented in this tutorial.

```lean
import Std.Classes.SetNotation

namespace Temporal
```

## General Definitions

```lean
def secondsPerMinute := 60

def minutesPerHour := 60

def secondsPerHour := secondsPerMinute * minutesPerHour

def hoursPerDay := 24

def secondsPerDay := secondsPerHour * hoursPerDay
```

## DTG

DTG (Date/Time Group) models a combined date and time type and its core properties and functions.

A DTG is the number of seconds since the epoch (year 0 in the Gregorian calendar). Note the
granularity of values is to the nearest second.

```lean
structure DTG where
  dtg : Nat
deriving Repr, Ord, DecidableEq

namespace DTG
```

Allow natural numbers to be interpreted as DTGs (the number of seconds since the epoch).

```lean
instance : OfNat DTG n where
  ofNat := ⟨n⟩
```

The `<` order relation on DTG.

```lean
instance : LT DTG where
  lt := fun ⟨d₁⟩ ⟨d₂⟩ ↦ d₁ < d₂
```

The `<` relation is decidable.

```lean
instance (x y : DTG) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.dtg < y.dtg))
```

The `≤` order relation on DTG.

```lean
instance : LE DTG where
  le := fun ⟨d₁⟩ ⟨d₂⟩ ↦ d₁ ≤ d₂
```

The `≤` relation is decidable.

```lean
instance (x y : DTG) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.dtg ≤ y.dtg))
```

The minimum function on DTG.

```lean
instance : Min DTG where
  min := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨min d₁ d₂⟩
```

The maximum function on DTG.

```lean
instance : Max DTG where
  max := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨max d₁ d₂⟩
```

Addition of two DTGs.

```lean
instance : Add DTG where
  add := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨d₁ + d₂⟩

end DTG
```

## Duration

Define the duration type and its core properties and functions.

A duration is expressed as a number of seconds.

```lean
structure Duration where
   dur : Nat
deriving Repr, Ord, DecidableEq

namespace Duration
```

Allow natural numbers to be interpreted as durations (the number of seconds in the duration).

```lean
instance : OfNat Duration n where
  ofNat := ⟨n⟩
```

The `<` order relation on Duration.

```lean
instance : LT Duration where
  lt := fun ⟨d₁⟩ ⟨d₂⟩ ↦ d₁ < d₂
```

The `<` relation is decidable.

```lean
instance (x y : Duration) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.dur < y.dur))
```

The `≤` order relation on Duration.

```lean
instance : LE Duration where
  le := fun ⟨d₁⟩ ⟨d₂⟩ ↦ d₁ ≤ d₂
```

The `≤` relation is decidable.

```lean
instance (x y : Duration) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.dur ≤ y.dur))
```

The minimum function on Duration.

```lean
instance : Min Duration where
  min := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨min d₁ d₂⟩
```

The maximum function on Duration.

```lean
instance : Max Duration where
  max := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨max d₁ d₂⟩
```

Addition of two durations.

```lean
instance : Add Duration where
  add := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨d₁ + d₂⟩
```

Difference of two durations.

Note: `d₁ - d₂ = d₂ - d₁ = max d₁ d₂ - min d₁ d₂`, hence it is magnitude of the difference.

```lean
instance : Sub Duration where
  sub := fun ⟨d₁⟩ ⟨d₂⟩ ↦ if d₁ < d₂ then ⟨d₂ - d₁⟩ else ⟨d₁ - d₂⟩
```

The duration of a day.

```lean
def oneDay : Duration := ⟨secondsPerDay⟩
```

The duration of an hour.

```lean
def oneHour : Duration := ⟨secondsPerHour⟩

end Duration
```

## Heterogenous Operations on DTG/Duration

Add a duration to a DTG.

```lean
instance : HAdd DTG Duration DTG where
  hAdd := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨d₁ + d₂⟩
```

Subtract a duration from a DTG. Natural number subtraction ensures the result cannot be
earlier than the start of the epoch.

```lean
instance : HSub DTG Duration DTG where
  hSub := fun ⟨d₁⟩ ⟨d₂⟩ ↦ ⟨d₁ - d₂⟩
```

The duration between two DTGs.

- `d₁ - d₂ = d₂ - d₁ = max d₁ d₂ - min d₁ d₂` (magnitude of the difference).

```lean
instance : HSub DTG DTG Duration where
  hSub := fun ⟨d₁⟩ ⟨d₂⟩ ↦ if d₁ < d₂ then ⟨d₂ - d₁⟩ else ⟨d₁ - d₂⟩
```

Multiply a duration by a number.

```lean
instance : HMul Duration Nat Duration where
  hMul := fun ⟨d⟩ n ↦ ⟨d * n⟩
```

Divide a duration by a number.

```lean
instance : HDiv Duration Nat Duration where
  hDiv := fun ⟨d⟩ n ↦ ⟨d / n⟩
```

## Interval

Define the type of intervals: the points in time between a start and end point.

The interval consists of a start and an end time, with evidence the end time is
not earlier than the start time. The start time is inclusive, the end time is
exclusive, so the empty interval has _start time = end time_.

```lean
structure Interval where
  starts : DTG
  ends   : DTG
  inv    : starts ≤ ends
deriving Repr, Ord, DecidableEq

namespace Interval
```

Default instance of an interval.

```lean
instance : Inhabited Interval where
  default := ⟨0, 0, by simp⟩
```

The `<` order relation on Interval.
- `i₁ < i₂ ↔ i₁.ends ≤ i₂.starts` (`i₁` ends before `i₂` starts).

```lean
instance : LT Interval where
  lt i₁ i₂ := i₁.ends ≤ i₂.starts
```

The `<` relation is decidable.

```lean
instance (i₁ i₂ : Interval) : Decidable (i₁ < i₂) :=
  inferInstanceAs (Decidable (i₁.ends ≤ i₂.starts))
```

Is a DTG contained within an interval?

```lean
def contains (i : Interval) (d : DTG) : Bool :=
  i.starts ≤ d ∧ d < i.ends
```

Instance of `Membership`; allows notation `dtg ∈ interval`.

```lean
instance : Membership DTG Interval  where
  mem d i := i.contains d
```

Do two intervals overlap? That is, have at least one common point in time.

```lean
def overlap (i₁ i₂ : Interval) : Bool :=
  i₁.starts < i₂.ends ∧ i₂.starts < i₁.ends
```

The intersection of two intervals. If they do not overlap the result is the empty interval.

```lean
def inter : Interval → Interval → Interval
  | ⟨s₁, e₁, _⟩, ⟨s₂, e₂, _⟩ =>
      let istart := max s₁ s₂
      let iend := if min e₁ e₂ < istart then istart else min e₁ e₂
      if istart = iend then default else ⟨istart, iend, sorry⟩
```

Instance of `Inter`; allows notation `i₁ ∩ i₂`.

```lean
instance : Inter Interval := ⟨inter⟩
```

Is one interval fully contained within another?

```lean
def within (i₁ i₂ : Interval) : Prop :=
  i₂.starts ≤ i₁.starts ∧ i₁.ends ≤ i₂.ends
```

Instance of `HasSubset`; allows notation `i₁ ⊆ i₂`.

```lean
instance : HasSubset Interval := ⟨within⟩
```

The `⊆` relation is decidable.

```lean
instance (x y : Interval) : Decidable (x ⊆ y) :=
  sorry
```

Instance of `EmptyCollection`; allows notation `∅` for empty interval.

```lean
instance : EmptyCollection Interval where
  emptyCollection := default
```

The duration of an interval.

```lean
def durationOf (i : Interval) : Duration :=
  i.ends - i.starts
```

The interval commencing at a date/time lasting for a given duration.

```lean
def intervalOf (dtg : DTG) (dur : Duration) : Interval :=
  ⟨dtg, dtg+dur, sorry⟩

end Interval

end Temporal
```
