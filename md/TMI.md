# Example: Aviation Resource Management

The previous examples have been typical problems from computing science. This
example is drawn from industry, and is a simplified version of a problem that
occurs globally on a daily basis. It concerns resource allocation in the aviation
industry. Specifically, scheduling aircraft for take off at an airport.

The number of passengers undertaking air travel is continually increasing, with a
corresponding increase in the number of aircraft movements. However, the resources
available to facilitate these flights are not growing at the same rate. In
particular, airports and their runways, taxiways and gates are becoming ever more
congested. If we cannot grow the resources to match the increase in passenger
numbers and flights, it is necessary to improve the efficiency with which the
available resources are used.

[Air Traffic Flow Management (ATFM)](https://www.icao.int/airnavigation/IMP/Documents/9971%20Collaborative%20Flight%20and%20Flow%20Informaiton.pdf)
is the discipline that assesses future air traffic movements, and schedules that
traffic to make best use of available resources. The application of a set of rules
that schedules aircraft across resources over a period of time is known as a
Traffic Management Initiative (TMI). There are different kinds of TMIs, one being
a Ground Delay Program (GDP): hold aircraft on the ground at their departure point
such that after take off they are able to proceed to their destination without
being placed in a holding pattern prior to arrival. An aircraft holding in the air
is using significant amounts of fuel, increasing costs for the operator and
increasing environmental impact due to greater emissions.

A GDP assesses the aircraft bound for an airport based on flight schedules, allocates
landing times, and then back calculates to determine the best take off time for an
aircraft to ensure when it reaches its destination it will not be in conflict with
other aircraft attempting to land.

## The Problem Statement

The particular TMI we will look at is a departure program; that is, scheduling
aircraft departing an airport. Such a program may be conducted to ensure an
ordered sequence of departures. For example, during the mining boom in Western
Australia, many aircraft would depart the capital, Perth, for remote mining
sites. We have many aircraft departing one airport, and heading to a variety of
destinations with low traffic volumes. In a free for all situation, the aircraft
will leave their gates according to their schedule, resulting in congestion on
taxiways as aircraft queue for take off. Individual flights have no motivation to
wait for a suitable slot, since others will simply leave their gate to fill the
gap. Congestion is not the only problem; aircraft sitting on the taxiway burn fuel
hence there is increased cost for the aircraft operator, and greater environmental
impact from the increased emissions.

A departure program allocates a take off time to each aircraft so the operator is
informed beforehand when they are allowed to take off. This provides the aircraft
operator with more certainty since they know exactly when the flight will depart
and hence can better predict arrival time for planning of subsequent flight legs.
A number of constraints must be satisfied by the departure program:
- Specified flights wish to depart an airport.
  - The flights that plan to depart during the period of the TMI.
- Each flight may only take off from certain runways.
  - Larger aircraft may not be able to take off from shorter runways.
- Each flight has a preferred take off time.
  - The time the aircraft operator would ideally like their flight to depart.
- Each flight must take off in a nominated time window.
  - Aircraft operators have schedules to meet; the allocated take off time must not be too
  far from the scheduled time.
- Only certain runways are available.
  - The configuration of resources dictates which of the runways at an airport are available
  for use.
- Each runway has a maximum rate at which departures can occur.
  - The rates may differ for different runways. Rate is impacted by factors such as the forecast
  weather and airport noise restrictions.
- The program occurs over a fixed interval.
  - A program need only run at times when there is likely to be competition for resources.

Given these constraints, the problem then is to:
- Allocate a runway and target take off time to as many flights as possible such that the
constraints are satisfied. Flights should be allocated a time as close as possible to their
preferred time.

## The Specification

```lean
import LeanSpec.lib.Temporal
import LeanSpec.lib.Util

open Std Std.Map Temporal

namespace TMI
```

First some basic types that identify airports, flights and runways. There are rules
around how these identifiers are formed, but for this specification it is sufficient
that different identifiers can be distinguished.

### Designator of an Airport

```lean
abbrev AirportDesig := String
```

### Identifier of a Flight

```lean
abbrev FlightId := String
```

### Designator of a Runway

```lean
abbrev RunwayDesig := String
```

### Flight Departure

The `FlightDeparture` type captures information concerning a flight that is pertinent to the
determination of departure slot allocation for a TMI. In a wider context, there is far more
information relevant to a flight, but here we abstract only the necessary details.

```lean
structure FlightDeparture where
  -- The runways the flight is able to use.
  canUse    : List RunwayDesig
  -- The operator's preferred take off time for the flight.
  preferred : DTG
  -- The period of time during which the flight can reasonably take off.
  window    : Interval
  -- The flight must be able to use at least one runway.
  inv₁      : canUse ≠ ∅  
  -- The preferred take off time must occur within the window.
  inv₂      : preferred ∈ window
```

Notes:
- Field `canUse` is the runways (with respect to the departure TMI airport) the
flight is able to use. A flight, based on the type of aircraft used, may only be
able to use certain runways; an A380, for example, would not be able to take off
or land on short runways.
- It is not possible to allocate every flight its preferred take off time, but
operators have schedules to adhere to, and subsequent legs the aircraft must
conduct, so an acceptable take off window is specified. The flight must not be
allocated a time outside the window.

Traditionally, structures (records) are used to model data consisting of multiple disparate elements.
Dependent types introduce the capability to directly encode constraints that relate the
elements of a type. The consequence is that instances of the type that structurally look
like elements of the type are excluded because they fail to satisfy the constraints.

In the case of `FlightDeparture`, the empty list is of type `List RunwayDesig`, but field
`canUse` will never be the empty list as `inv₁` would not be satisfied. The consequence of
the invariant is a flight cannot be considered if it does not nominate at least one runway
from which it can take off.

### Runway Rate

The runway rate determines how frequently an aircraft can take off from a runway.
This is modelled as a duration, being the minimum period of time between successive
take offs.

```lean
abbrev Rate := Duration
```

Each relevant runway is mapped to the rate it can accommodate.

```lean
abbrev RunwayRates := RunwayDesig ⟹ Rate
```

Note: `A ⟹ B` is the type of finite maps from `A` to `B` (defined in `lib/Util`).

### TMI Configuration

A TMI configuration is all the information necessary to calculate a departure TMI,
consisting of information relevant to the airport, and the flights that wish to
depart from the airport during the TMI.

```lean
structure TMIConfig where
  -- The designator of the airport at which the TMI is run.
  airport : AirportDesig
  -- The period of time over which the TMI runs.
  period  : Interval
  -- The flights that desire to take off within the period of the TMI.
  flights : FlightId ⟹ FlightDeparture
  -- The rates of the runways that participate in the TMI.
  rates   : RunwayRates
  -- The take off window of a proposed flight must fall within the TMI period.
  inv₁    : ∀ f ∈ flights.range, f.window ∩ period ≠ ∅ 
  -- A flight must be able to take off from one of the participating runways.
  inv₂    : ∀ f ∈ flights.range, f.canUse ∩ rates.domain ≠ ∅
```

### Slot

A slot is a point in time at which a runway is available to an aircraft for take off.

```lean
structure Slot where
  -- The runway designator.
  rwy  : RunwayDesig
  -- The target take off time.
  ttot : DTG
```

### Flight Allocation

The result of running a departure TMI (GDP) is a map from flights to their slots
(allocated runways and take off times) such that the problem constraints are satisfied.

```lean
structure FlightAllocation (cfg : TMIConfig) where
  -- The allocation of flight departures to slots.
  gdp  : FlightId ⟹ Slot
  -- Any flight in the GDP must be drawn from the TMI configuration.
  inv₁ : gdp.domain ⊆ cfg.flights.domain
  -- The runway allocated to a flight must be a participant in the TMI.
  inv₂ : ∀ slot ∈ gdp.range, slot.rwy ∈ cfg.rates.domain
  -- The runway allocated to a flight must be one of the runways it can use.
  inv₃ : ∀ fsl ∈ gdp, ∀ fdep ∈ cfg.flights,
           fsl.1 = fdep.1 → fsl.2.rwy ∈ fdep.2.canUse
  -- The target time allocated to a flight must fall within its window.
  inv₄ : ∀ fsl ∈ gdp, ∀ fdep ∈ cfg.flights,
           fsl.1 = fdep.1 → fsl.2.ttot ∈ fdep.2.window
  -- The target time allocated to a flight must fall within the TMI period.
  inv₅ : ∀ slot ∈ gdp.range, slot.ttot ∈ cfg.period
  -- Two flights allocated the same runway must depart at least the minimum duration apart.
  inv₆ : ∀ fsl₁ ∈ gdp, ∀ fsl₂ ∈ gdp, ∀ fr ∈ cfg.rates,
           fsl₁.1 ≠ fsl₂.1 ∧ fsl₁.2.rwy = fsl₂.2.rwy ∧ fr.1 = fsl₁.2.rwy → 
             fsl₁.2.ttot - fsl₂.2.ttot ≥ fr.2
```

As noted earlier, structures can contain constraints to which the instances must adhere.
Dependent types allow us to take this a step further. `FlightAllocation` is dependent on
(parameterised by) `TMIConfig`. As a result, the constraints of the type are not just
restricted to the fields of the type being defined, they can also specify relationships
between the argument type and the type being defined. In the case of `FlightAllocation`, every
constraint is concerned with the relationship to `TMIConfig`.

Field `gdp` of `FlightAllocation` is the only _data_ field; all others are invariants. The effect
of this definition is that for a given `cfg : TMIConfig`, the elements of type
`FlightAllocation cfg` are all, and only, those allocations of flights to slots that satisfy
the problem constraints.

### Cost

To complete the specification, we need the concept of a cost of a departure TMI.
There are many possible allocations that meet the constraints. The cost function
decides which one to select.

In an operational situation, the best cost function is far from clear, and would
likely require some investigation and prototyping. In this specification,
we adopt a fairly simple cost function for demonstration purposes. The cost function
needs to take account of both those flights that are allocated slots in the GDP, and
those that are omitted:
- the cost of an included flight increases the further the allocated time is from the preferred time;
- the cost of an excluded flight is generally greater than the cost of an included flight.

The deviation assigned to a flight that was allocated a slot in the TMI is
the duration between its preferred time and its allocated time. Duration is
expressed in seconds, so the greater the duration, the greater the cost.

```lean
def allocatedDeviation (flight : FlightDeparture) (slot : Slot) : Duration :=
  flight.preferred - slot.ttot
```

If an omitted flight's window only partly overlaps the TMI period, there is still the
possibility it may be able to take off in its operational window, but outside the
TMI period. If an omitted flight's window is wholly within the TMI period, the
aircraft operator has a scheduling problem to solve. Consequently, for an omitted flight:

- if its window is fully within the TMI period, the cost is the duration of the window;
- if the window is partly outside the TMI period, the cost is half the duration of the window.

```lean
def omittedDeviation (period window : Interval) : Duration :=
  let d := window.durationOf
  if window ⊆ period then d else d/2
```

The deviations for all flights that requested a take off during the period of the TMI.

```lean
def deviations (cfg : TMIConfig) (alloc : FlightAllocation cfg) : List Duration :=
  let deviation (fdep : FlightId × FlightDeparture) : Duration :=
        match find? fdep.1 alloc.gdp with
        | none      => omittedDeviation cfg.period fdep.2.window
        | some slot => allocatedDeviation fdep.2 slot
  cfg.flights.toList.map deviation
```

The `cost` of a TMI is the sum of the costs of the flights that requested a take off
during the TMI.

```lean
def cost (cfg : TMIConfig) (alloc : FlightAllocation cfg) : Duration :=
  (deviations cfg alloc).add 0
```

### Departure TMI

Combining the components above, the departure TMI can be specified as:
- the optimal TMI, that is, of all TMIs that satisfy the configuration, the (not
necessarily unique) TMI whose cost is no greater than any other TMI.

```lean
def DepartureTMI (cfg : TMIConfig) :=
  { opt : FlightAllocation cfg // ∀ alloc : FlightAllocation cfg, cost cfg opt ≤ cost cfg alloc }
```

## Further Discussion

We finish with some further discussion on aspects of the specification.

### More Concise Specification

There is a great deal of repetition in the specification of the invariants of type
`FlightAllocation`, which generally occur in the quantified variables and pre-conditions.
We can reduce that repetition by merging invariants as follows:

```lean
structure FlightAllocation₁ (cfg : TMIConfig) where
  -- The allocation of flights to slots.
  gdp  : FlightId ⟹ Slot
  -- Any flight in the GDP must be drawn from the TMI configuration.
  inv₁ : gdp.domain ⊆ cfg.flights.domain
  -- The runway allocated to a flight must be a participant in the TMI.
  -- The target time allocated to a flight must fall within the TMI period.
  -- The runway allocated to a flight must be one of the runways it can use.
  -- The target time allocated to a flight must fall within its window.
  inv₂ : ∀ fsl ∈ gdp,
           fsl.2.rwy ∈ cfg.rates.domain ∧
           fsl.2.ttot ∈ cfg.period ∧
           ∀ fdep ∈ cfg.flights, fsl.1 = fdep.1 →
             fsl.2.rwy ∈ fdep.2.canUse ∧
             fsl.2.ttot ∈ fdep.2.window
  -- Two flights allocated the same runway must depart at least the minimum duration apart.
  inv₃ : ∀ fsl₁ ∈ gdp, ∀ fsl₂ ∈ gdp, ∀ fr ∈ cfg.rates,
           fsl₁.1 ≠ fsl₂.1 ∧ fsl₁.2.rwy = fsl₂.2.rwy ∧ fr.1 = fsl₁.2.rwy → 
             fsl₁.2.ttot - fsl₂.2.ttot ≥ fr.2
```

There are now three rather than six invariants, and it is more concise. The separate approach
was taken to provide a clearer map from the specification to the informal description of the
constraints. In addition, keeping them separate makes it easier to focus on individual
constraints.

### Non-Dependent Approach

`FlightAllocation` is a dependent type that only admits an element if it satisfies the invariants.
The initial approach was more traditional with `FlightAllocation` defined as a simple map:

```lean
abbrev FlightAllocation₂ := FlightId ⟹ Slot
```

This type admits anything that is structurally a map from `FlightId` to `Slot`,
hence includes things like:
- identifiers that do not relate to a flight;
- slots referring to runways that do not exist.

It is then necessary to define a function `satisfies`, external to the type definition,
that specifies when a flight allocation satisfies a TMI configuration (that is, the
`FlightAllocation` is a valid solution to the `TMIConfig`).

```lean
def satisfies (cfg : TMIConfig) (alloc : FlightAllocation₂) : Prop :=
  alloc.domain ⊆ cfg.flights.domain ∧
  (∀ slot ∈ alloc.range, slot.rwy ∈ cfg.rates.domain) ∧
  (∀ fsl ∈ alloc, ∀ fdep ∈ cfg.flights,
    fsl.1 = fdep.1 → fsl.2.rwy ∈ fdep.2.canUse) ∧
  (∀ fsl ∈ alloc, ∀ fdep ∈ cfg.flights,
    fsl.1 = fdep.1 → fsl.2.ttot ∈ fdep.2.window) ∧
  (∀ slot ∈ alloc.range, slot.ttot ∈ cfg.period) ∧
  (∀ fsl₁ ∈ alloc, ∀ fsl₂ ∈ alloc, ∀ fr ∈ cfg.rates,
    fsl₁.1 ≠ fsl₂.1 ∧ fsl₁.2.rwy = fsl₂.2.rwy ∧ fr.1 = fsl₁.2.rwy → 
      fsl₁.2.ttot - fsl₂.2.ttot ≥ fr.2)
```

Note that, other than some minor syntactic differences, the constraints expressed by
`satisfies` are exactly the invariants of type `FlightAllocation`.

The dependent approach allows the constraints to be located with the data they refer to,
rather than elsewhere in the specification, which aids comprehension. Further, the dependent
approach allows the types to be more tightly defined, and as a result the specification of
functions over those types tends to be simpler.

## Exercises

- Small changes to specifications can have major effects. What would happen if the
specification was changed such that the cost function only considered flights that
are included in the TMI? That is, change `deviations` to:

```lean
def deviations₁ (cfg : TMIConfig) (alloc : FlightAllocation cfg) : List Duration :=
  let deviation (fdep : FlightId × FlightDeparture) : Duration :=
        match find? fdep.1 alloc.gdp with
        | none      => 0
        | some slot => allocatedDeviation fdep.2 slot
  cfg.flights.toList.map deviation
```

- There has been a requirements change. A flight must not take off prior to its
preferred time, though it can after its preferred time. Change the specification to
satisfy the new requirement.

- It is always instructive to consider boundary cases. Say a TMI was run with a configuration
in which no flights are specified. That is, `flights : FlightId ⟹ FlightDeparture` is the empty map.
Is a solution that meets the specification still possible?

- Another boundary case is when no runways rates are specified. That is, `rates : RunwayRates` is
the empty map. Is a solution that meets the specification still possible? Is there any relationship
between this and the `flights` item?

- What is the impact on the specification if the constraint `inv₁ : canUse ≠ ∅` on type
`FlightDeparture` is removed?

- An alternative approach to evaluation of cost is to maximise the number of
passengers that are able to depart during the TMI. Modify the specification to
implement this approach to cost. Hint: you will have to change `FlightDeparture`.
(If you are a freight carrier you are out of luck.)

```lean
end TMI
```
