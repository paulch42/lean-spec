/-
# Flight

A flight data entity captures the totality of information that is known about a flight.
Since the purpose of the specification is flight plan message processing, and those messages
are defined by different combinations of fields, a flight is simply the union of all fields.
-/
import LeanSpec.FPL.Field

open Temporal Core FPL.Field

namespace FPL

/-
## Flight Identification

The flight identifier is used when matching received flight information against known flights. The match is based on:

- Aircraft identification (field 7a).
- Departure aerodrome (field 13a).
- Flight time - a period of time based on the departure time (field 13b) and flight duration (field 16b).
-/
structure FlightId where
  acid   : AircraftIdentification
  adep   : Option ADep
  period : Interval
deriving DecidableEq

/-
If two flight identifiers match they may refer to the same flight. Information can be received from
multiple sources, and it is not always 100% consistent. Matching attempts to find the best fit.
Two identifiers match if they have:

- the same aircraft identification;
- the same departure point; and
- overlapping flight times.
-/
def FlightId.match : FlightId → FlightId → Bool
  | ⟨a₁,d₁,p₁⟩, ⟨a₂,d₂,p₂⟩ => a₁ = a₂ ∧ d₁ = d₂ ∧ p₁.overlap p₂

/-
Instances of class `FlightTime` are entities that have an identifiable period of flight.
-/
class FlightTime (α: Type) where
  period : α → Interval  

/-
Default maximum time of a flight when full information is not available.
-/
def maxFlightTime := Duration.oneHour * 20

/-
Default maximum time of a round trip flight (departure = destination) when full information
is not available.
-/
def maxRoundTripTime := Duration.oneHour * 6

/-
Estimated flight time based on departure time, estimated flight duration, and whether
departure = destination.
-/
def adepAdesFlightTime (f13a : Field13a) (f13b : DTG) (f16a : Field16a) : Option Duration → Interval
  | none      => -- flight duration not known
                 .intervalOf f13b (if adepIsAdes f13a f16a then maxRoundTripTime else maxFlightTime)
  | some teet => -- flight duration known
                 if adepIsAdes f13a f16a then
                   .intervalOf f13b (min teet maxRoundTripTime)
                 else
                   .intervalOf f13b (min (teet * 2) maxFlightTime)

/-
Instances of class `IsFlight` are identifiable as being associated with flights. Specifically, a
`FlightId` can be derived from the type. To be identifiable as a flight, an entity must have a `FlightTime`.
-/
class IsFlight (α : Type) [FlightTime α] where
  idOf : α → FlightId

/-
## Flight Status

The status of a flight is based on the state it has reached in its lifecycle.
-/
inductive FlightStatus
  | filed
  | airborne
  | cancelled
  | completed

/-
## Flight Information Content

The information held on a flight is assembled from the messages received for the flight.
Consequently a flight is defined as the combined fields that make up the messages, and
the constraints between fields defined in [Field](Field.md) ensure integrity of data.
Field 22 is the exception; its purpose is to communicate changes, and those changes are
incorporated in the other fields, hence it is excluded from `Flight`.

In addition to the message fields, a flight is also assigned a status based on the point it has reached
in its lifecycle. For example, if a departure message has just been received for a flight, the status is
set to `airborne`.
-/
structure Flight where
  status : FlightStatus
  f7     : Field7
  f8     : Field8
  f9     : Field9
  f10    : Field10
  f13    : Field13
  f15    : Field15
  f16    : Field16
  f17    : Option Field17
  f18    : Option Field18
  inv    : f8_f15_level f8 f15 ∧
           f8_f15_frul f8 f15 ∧
           f9_f18_typ f9 f18 ∧
           f10_f18_sts f10 f18 ∧
           f10_f18_pbn f10 f18 ∧
           f10_f18_z f10 f18 ∧
           f13_f18_dep f13 f18 ∧
           f15_f18_dle f15 f18 ∧
           f16_f18_dest f16 f18 ∧
           f16_f18_altn f16 f18 ∧
           f16_f18_eet f16 f18 ∧
           f16_f18_dle f16 f18 ∧
           f16_f17_dest f16.f16a f17 ∧
           -- Field 17 is populated if and only if the flight is completed.
           f17.isSome ↔ status = .completed

/-
Note there are many constraints to which the flight data must adhere. This is a good example
of how dependent types allow constraints to be packaged with the data elements to give
a precise characterisation. All but the last constraint are as defined in [Field](Field.md).

The flight time derived from a flight.
-/
instance : FlightTime Flight where
  period flt := adepAdesFlightTime flt.f13.f13a flt.f13.f13b flt.f16.f16a flt.f16.f16b

/-
Flight identification derived from a flight.
-/
instance : IsFlight Flight where
  idOf flight := ⟨flight.f7.f7a, flight.f13.f13a, FlightTime.period flight⟩

/-
Instances of `ToFlight` can be used to generate a `Flight`.
-/
class ToFlight (α : Type) where
  toFlight : α → Flight

end FPL