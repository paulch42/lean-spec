# Flight Planning Messages

This module defines the content and properties of the flight plan related ATS messages defined in PANS-ATM.

```lean
import LeanSpec.FPL.Field

set_option autoImplicit false

open Temporal Core FPL.Field

namespace FPL
```

## Flight Identification

The flight identifier is used for when matching a message against known flights. The match is based on:
- aircraft identification (field 7a);
- departure aerodrome (field 13a);
- flight time  a period of time based on the departure time (13b) and flight duration (16b).

```lean
structure FlightId where
  acid   : AircraftIdentification
  adep   : Option ADep
  period : Interval
deriving DecidableEq
```

If two flight identifiers match they may refer to the same flight. Information can be received from
multiple sources, and it is not always 100% consistent. Matching attempts to find the best fit.
Two identifiers match if they have:

- same aircraft identification;
- same departure point;
- overlapping flight times.

```lean
def FlightId.match : FlightId → FlightId → Bool
  | ⟨a₁,d₁,p₁⟩, ⟨a₂,d₂,p₂⟩ => a₁ = a₂ ∧ d₁ = d₂ ∧ p₁.overlap p₂
```

Instances of class `FlightTime` are entities that have an identifiable period of flight.

```lean
class FlightTime (α: Type) where
  period : α → Interval
```

Default maximum time of flight when full information is not available.

```lean
def maxFlightTime := Duration.oneHour * 20
```

Default maximum time of a round trip flight (departure = destination) when full information
is not available.

```lean
def maxRoundTripTime := Duration.oneHour * 6
```

Estimated flight time based on departure time, estimated flight duration, and whether
departure = destination.

```lean
def adepAdesFlightTime : Field13a → DTG → Field16a → Option Duration → Interval
  |  f13a, f13b, f16a, none      => if adepIsAdes f13a f16a then
                                      Interval.intervalOf f13b maxRoundTripTime
                                    else
                                      Interval.intervalOf f13b maxFlightTime
  |  f13a, f13b, f16a, some teet => if adepIsAdes f13a f16a then
                                      Interval.intervalOf f13b (min teet maxRoundTripTime)
                                    else
                                      Interval.intervalOf f13b (min (teet * 2) maxFlightTime)
```

Instances of class `Identity` are identifiable as flights.
To be identifiable as a flight, an entity must have a `FlightTime`.

```lean
class Identity (α : Type) [FlightTime α] where
  idOf : α → FlightId
```

## Filed Flight Plan: FPL

The content and constraints of a FPL (filed flight plan) message.

```lean
structure FPL where
  f7    : Field7
  f8    : Field8
  f9    : Field9
  f10   : Field10
  f13   : Field13
  f15   : Field15
  f16   : Field16
  f18   : Option Field18
  inv₁  : f8_f15_level f8 f15
  inv₂  : f8_f15_frul f8 f15
  inv₃  : f9_f18_typ f9 f18
  inv₄  : f10_f18_rvsm f10 f18
  inv₅  : f10_f18_pbn f10 f18
  inv₆  : f10_f18_z f10 f18
  inv₇  : f13_f18_dep f13.f13a f18
  inv₈  : f15_f18_dle f15.f15c f18
  inv₉  : f16_f18_dest f16.f16a f18
  inv₁₀ : f16_f18_altn f16.f16c f18
  inv₁₁ : f16_f18_eet f16.f16b f18
  inv₁₂ : f16_f18_dle f16.f16b f18
```

Note there are many constraints to which the FPL data must adhere. This is a good example
of how dependent types allow constraints to be packaged with the data elements to give
a precise characterisation. The constraints are as defined in `FPL.Field`.

The flight time derived from a FPL.

```lean
instance : FlightTime FPL where
  period fpl := adepAdesFlightTime fpl.f13.f13a fpl.f13.f13b fpl.f16.f16a fpl.f16.f16b
```

Flight identification derived from a FPL.

```lean
instance : Identity FPL where
  idOf fpl := ⟨fpl.f7.f7a, fpl.f13.f13a, FlightTime.period fpl⟩
```

## Modification: CHG

The content and constraints of a CHG (modification) message.

```lean
structure CHG where
  f7  : Field7
  f13 : Field13
  f16 : Field16a
  f22 : Field22
```

The flight time derived from a CHG.

```lean
instance : FlightTime CHG where
  period chg := adepAdesFlightTime chg.f13.f13a chg.f13.f13b chg.f16 none
```

Flight identification derived from a CHG.

```lean
instance : Identity CHG where
  idOf chg := ⟨chg.f7.f7a, chg.f13.f13a, FlightTime.period chg⟩
```

## Cancellation: CNL

The content and constraints of a CNL (cancellation) message.

```lean
structure CNL where
  f7  : Field7
  f13 : Field13
  f16 : Field16a
```

The flight time derived from a CNL.

```lean
instance : FlightTime CNL where
  period cnl := adepAdesFlightTime cnl.f13.f13a cnl.f13.f13b cnl.f16 none
```

Flight identification derived from a CNL.

```lean
instance : Identity CNL where
  idOf cnl := ⟨cnl.f7.f7a, cnl.f13.f13a, FlightTime.period cnl⟩
```

## Delay: DLA

The content and constraints of a DLA (delay) message.

```lean
structure DLA where
  f7  : Field7
  f13 : Field13
  f16 : Field16a
```

The flight time derived from a DLA.

```lean
instance : FlightTime DLA where
  period dla := adepAdesFlightTime dla.f13.f13a dla.f13.f13b dla.f16 none
```

Flight identification derived from a DLA.

```lean
instance : Identity DLA where
  idOf dla := ⟨dla.f7.f7a, dla.f13.f13a, FlightTime.period dla⟩
```

## Departure: DEP

The content and constraints of a DEP (departure) message.

```lean
structure DEP where
  f7  : Field7
  f13 : Field13
  f16 : Field16a
```

The flight time derived from a DEP.

```lean
instance : FlightTime DEP where
  period dep := adepAdesFlightTime dep.f13.f13a dep.f13.f13b dep.f16 none
```

Flight identification derived from a DEP.

```lean
instance : Identity DEP where
  idOf dep := ⟨dep.f7.f7a, dep.f13.f13a, FlightTime.period dep⟩
```

## Arrival: ARR

The content and constraints of an ARR (arrival) message.

```lean
structure ARR where
  f7  : Field7
  f13 : Field13
  f16 : Field16a
  f17 : Field17
  inv : f16_f17_dest f16 f17
```

The flight time derived from an ARR.

```lean
instance : FlightTime ARR where
  period arr := let ades := -- use the planned destination if available, otherwise the actual arrival
                            match arr.f16, arr.f17.f17a with
                            | none, aarr => aarr
                            | parr, _    => parr
                adepAdesFlightTime arr.f13.f13a arr.f13.f13b ades none
```

Flight identification derived from an ARR.

```lean
instance : Identity ARR where
  idOf arr := ⟨arr.f7.f7a, arr.f13.f13a, FlightTime.period arr⟩
```

## Message

A flight plan related message is then the union of the different types of message.

```lean
inductive Message
  | fpl (_ : FPL)
  | chg (_ : CHG)
  | cnl (_ : CNL)
  | dla (_ : DLA)
  | dep (_ : DEP)
  | arr (_ : ARR)
```

The flight time derived from a message.

```lean
instance : FlightTime Message where
  period | .fpl x => FlightTime.period x
         | .chg x => FlightTime.period x
         | .cnl x => FlightTime.period x
         | .dla x => FlightTime.period x
         | .dep x => FlightTime.period x
         | .arr x => FlightTime.period x
```

Flight identification derived from a message.

```lean
instance : Identity Message where
  idOf | .fpl x => Identity.idOf x
       | .chg x => Identity.idOf x
       | .cnl x => Identity.idOf x
       | .dla x => Identity.idOf x
       | .dep x => Identity.idOf x
       | .arr x => Identity.idOf x

end FPL
```
