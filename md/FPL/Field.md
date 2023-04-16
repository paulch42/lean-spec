# Message Fields

Building on the basic data definitions in [Core](Core.md), this module defines the message
fields that group together related information, and which in turn are combined to
define the messages.

For each field example text from an ATS message is provided, together with the corresponding
Lean value. Lean has a variety of ways to populate structure values, and all variants are
demonstrated.

```lean
import LeanSpec.FPL.Core
import LeanSpec.lib.Temporal

open Core Temporal

namespace FPL.Field
```

## Field 7: Aircraft identification and SSR mode and code

Field 7 is concerned with how a flight is identified for communication with air traffic control.

```lean
structure Field7 where
  f7a  : AircraftIdentification
  f7bc : Option SsrCode
deriving DecidableEq
```

### Field 7 Example

`-SAS912/A5100`

```lean
example := Field7.mk ⟨"SAS912", by simp⟩ (some ⟨"5100", by simp⟩)
```

## Field 8: Flight rules and type of flight

Field 8 provides information that determines how a flight is handled.

```lean
structure Field8 where
  f8a : FlightRules
  f8b : Option TypeOfFlight
deriving DecidableEq
```

### Field 8 Example

`-IS`

```lean
example := Field8.mk .i (some .s)
```

## Field 9: Number and type of aircraft and wake turbulence category

Field 9 provides information about the aircraft that will be used to conduct the flight.

```lean
structure Field9 where
  f9a : Option NumberOfAircraft    -- only included for formation flights
  f9b : Option Doc8643.Designator  -- `none` indicates ZZZZ (refer field 18 TYP)
  f9c : WakeTurbulenceCategory
deriving DecidableEq
```

`-2FK27/M`

```lean
example := Field9.mk (some ⟨2, by simp⟩) (some ⟨"FK27", by simp⟩) .m
```

### Field 9 Example

`-ZZZZ/L`

```lean
example := Field9.mk none none .l
```

## Field 10: Equipment and capabilities

Field 10 documents what equipment and capabilities the flight/aircraft has.
These items communicate what air traffic control can expect of the flight,
and limitations placed on the flight.

```lean
structure Field10 where
  f10a : Set CommNavAppCode    -- empty list indicates `N`
  f10b : Set SurveillanceCode  -- empty list indicates `N`
  -- Exclude invalid combinations.
  inv  : ¬ (.b1 ∈ f10b ∧ .b2 ∈ f10b) ∧
         ¬ (.u1 ∈ f10b ∧ .u2 ∈ f10b) ∧
         ¬ (.v1 ∈ f10b ∧ .v2 ∈ f10b)
deriving DecidableEq
```

### Field 10 Example

`-SAFR/SV1`

```lean
example := (⟨{.s, .a, .f, .r}, {.s, .v1}, sorry⟩ : Field10)
```

## Field 13: Departure aerodrome and time

Field 13 concerns the departure point and departure time of the flight.

A flight plan can be filed in the air, in which case AFIL is specified in the
departure point field.

```lean
inductive ADep
  | adep (_ : Doc7910.Designator)
  | afil
deriving DecidableEq

def Field13a := Option ADep  -- `none` indicates ZZZZ (refer field 18 DEP)
deriving DecidableEq

structure Field13 where
  f13a : Field13a
  f13b : DTG
deriving DecidableEq
```

### Field 13 Examples

`-EHAM0730`

```lean
example := Field13.mk (some (.adep ⟨"EHAM", by simp⟩)) 63072027000
```

`-AFIL1625`

```lean
example : Field13 := ⟨some .afil, 63072059100⟩
```

The designator in Field 13, if there is one.

```lean
def Field13.desigOf : Field13 → Option Doc7910.Designator
  | {f13a := some (.adep desig), ..} => desig
  | _                                => none
```

## Field 15: Route

Field 15 describes the route the aircraft will follow to go from departure to destination.
This includes the level/altitude the flight operates at, and the speed of the aircraft.

Climbing between two levels, the upper limit can be specified, or _PLUS_ used to
indicate there is no nominated upper level.

```lean
inductive UpperLevel
  | level (_ : VerticalPositionOfAircraft)
  | plus
deriving DecidableEq
```

Indication of the change in speed and level.

```lean
structure SpeedLevelChange where
  speed : TrueAirspeed
  level : VerticalPositionOfAircraft
  upper : Option UpperLevel
deriving DecidableEq
```

### Speed/Level Change Example

`N0540A055PLUS`

```lean
example : SpeedLevelChange where
  speed := ⟨⟨⟨540, sorry⟩, .kt, .ias, by simp⟩, sorry⟩
  level := ⟨5500, .feet, .altitude⟩
  upper := some .plus
```

A specific point along the route, together with changes to speed, level and flight rules
planned to occur at the point.

```lean
structure RoutePoint where
  pos  : Position
  chg  : Option SpeedLevelChange
  frul : Option FlightRule
deriving DecidableEq
```

Between two points on a route, the aircraft can follow a documented ATS route, or
proceed directly.

```lean
inductive Connector
  | rte (_ : RouteDesignator)
  | dct
deriving DecidableEq
```

A route element is a point (and associated data) followed by the path to
the next element. Either, but not both, may be omitted.

```lean
structure RouteElement where
  point : Option RoutePoint
  rte   : Option Connector
  -- At least one of point or connecting route must be populated.
  inv   : ¬ (point.isNone ∧ rte.isNone)
deriving DecidableEq
```

The named waypoint in a route element, if there is one.

```lean
def RouteElement.waypointOf : RouteElement → Option Waypoint
  | {point := some rp, ..} => rp.pos.waypointOf
  | _                      => none
```

The ATS route designator in a route element, if there is one.

```lean
def RouteElement.atsRteOf : RouteElement → Option RouteDesignator
  | {rte := some (.rte rd), ..} => rd
  | _                           => none
```

Does the route element indicate _direct_ to the next point?

```lean
def RouteElement.isDct : RouteElement → Bool
  | {rte := some .dct, ..} => true
  | _                      => false
```

The flight rules change in a route element, if there is one.

```lean
def RouteElement.ruleOf : RouteElement → Option FlightRule
  | {point := some rp, ..} => rp.frul
  | _                      => none
```

Indicator the route description has been truncated.

```lean
inductive Truncate | t
deriving DecidableEq
```

The route consists of:
- optional standard instrument departure (SID);
- the non-empty list of elements;
- optional standard arrival route (STAR) or truncation indicator.

```lean
structure Route where
  sid            : Option RouteDesignator
  elements       : List RouteElement
  starOrTruncate : Option (RouteDesignator ⊕ Truncate)
  -- Must be at least one route element.
  inv            : elements ≠ ∅ ∧
  -- Consecutive flight rules changes must be distinct.
                   let rules := (elements.map RouteElement.ruleOf).reduceOption
                   rules.Chain' (· ≠ ·) ∧
  -- DCT must be followed by an explicit point.
                   elements.Chain' (·.isDct → ·.point.isSome) ∧
  -- An ATS route designator must connect to another designator or a named point.
                   elements.Chain'
                     (fun re₁ re₂ ↦ re₁.atsRteOf.isSome →
                        re₂.waypointOf.isSome ∨ (re₂.point.isNone ∧ re₂.atsRteOf.isSome))
deriving DecidableEq
```

The set of named waypoints in a route.

```lean
def Route.waypoints (rte : Route) : Set Waypoint :=
  (rte.elements.map RouteElement.waypointOf).reduceOption.toSet
```

Field 15 consists of:
- the initial requested cruising speed;
- the initial requested cruising level;
- the route description.

```lean
structure Field15 where
  f15a : TrueAirspeed
  f15b : Option VerticalPositionOfAircraft  -- `none` indicates VFR
  f15c : Route
deriving DecidableEq
```

### Field 15 Example

`-M079F380 DCT WOL H65 RAZZI Q29 LIZZI DCT`

```lean
def exElems := [
  RouteElement.mk none (some .dct) (by simp),
  RouteElement.mk (mkWpt ⟨"WOL", by simp⟩) (some (.rte ⟨"H65", by simp⟩)) (by simp),
  RouteElement.mk (mkWpt ⟨"RAZZI", by simp⟩) (some (.rte ⟨"Q29", by simp⟩)) (by simp),
  RouteElement.mk (mkWpt ⟨"LIZZI", by simp⟩) (some .dct) (by simp)
]
where mkWpt (wpt : Waypoint) : Option RoutePoint :=
  some ⟨.wpt wpt, none, none⟩

example := {
  f15a := ⟨⟨⟨0.79, sorry⟩, .mach, .tas, by simp⟩, by simp⟩,  -- M079
  f15b := some ⟨380, .feet, .flightLevel⟩,                   -- F380
  f15c := ⟨none, exElems, none, sorry⟩ : Field15             -- DCT WOL H65 RAZZI Q29 LIZZI DCT
}
```

## Field 16: Destination aerodrome and total estimated elapsed time, destination alternate aerodrome(s)

Field 16 concerns the destination aerodrome, the flight time, and alternate destinations in the event
diversion is required.

```lean
abbrev Field16a := Option Doc7910.Designator  -- `none` indicates ZZZZ (refer field 18 DEST)
```

Up to two alternates are allowed.

```lean
def maxAlternateDestinations := 2
```

Field 16 consists of:
- the planned destination aerodrome;
- the total estimated elapsed time (TEET) - i.e. the estimated flight duration;
- alternate destination aerodromes in case of a diversion.

```lean
structure Field16 where
  f16a : Field16a
  f16b : Duration
  f16c : List Field16a
  -- TEET must be less than one day.
  inv  : f16b < Duration.oneDay ∧
  -- Upper limit on number of alternate aerodromes.
         f16c.length ≤ maxAlternateDestinations
deriving DecidableEq
```

### Field 16 Example

`-EHAM0645 EBBR ZZZZ`

```lean
example := Field16.mk (some ⟨"EHAM", by simp⟩) 24300 [some ⟨"EBBR", by simp⟩, none] sorry
```

Are a departure and destination aerodrome the same?

```lean
def adepIsAdes : Field13a → Field16a → Bool
  | none, none                       => True
  | some (.adep desig₁), some desig₂ => desig₁ = desig₂
  | _, _                             => False
```

## Field 17: Arrival aerodrome and time

Field 17 concerns the actual arrival point and time, which will differ from the
planned destination in the event of a diversion.

Field 17 consists of:
- the actual arrival aerodrome designator;
- the actual arrival time;
- the name of the arrival aerodrome, if it has no designator.

```lean
structure Field17 where
  f17a : Option Doc7910.Designator  -- `none` indicates ZZZZ
  f17b : DTG
  f17c : Option FreeText
  -- Exactly one of designator and aerodrome name must be populated.
  inv  : f17a.isNone ↔ f17c.isSome
deriving DecidableEq
```

### Field 17 Example

`-ZZZZ1620 DEN HELDER`

```lean
example := Field17.mk none 63072058800 (some ⟨"DEN HELDER", by simp⟩)
```

## Field 18: Other information

Field 18 contains diverse other information about the flight.

The flight plan framework is presently undergoing major revision to benefit from the latest
information management best practices. The extant flight plan format has largely remained
unchanged for over 50 years. Allowed changes are limited by the the need for backwards
compatibility. As a result, additional information has typically been added as extra
data in field 18, with the result it is a rather disparate collection. It also means
that related information is recorded in separate parts of the message. For example, codes
that indicate navigation capability are presented in field 10a, but more recent Performance
Based Navigation (PBN) codes appears in item _PBN_ of field 18.

Up to 8 PBN codes may be specified.

```lean
def maxPbnCodes := 8
```

The elapsed time from departure to a point en-route. Usually a point where control is passed
between ATS providers.

```lean
structure ElapsedTimePoint where
  point    : Doc7910.FIRDesignator ⊕ Position
  duration : Duration
deriving DecidableEq
```

The `<` order relation on EET points. Ordered by the duration.

```lean
instance : LT ElapsedTimePoint where
  lt et₁ et₂ := LT.lt et₁.duration et₂.duration
```

The `<` relation is decidable.

```lean
instance (x y : ElapsedTimePoint) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.duration < y.duration))
```

A point on the route where a delay occurs. The flight goes _off plan_ for
the duration. An example is a law enforcement flight that intends to conduct
covert operations and does not want to provide details of where it is flying.

```lean
structure DelayPoint where
  point    : Waypoint
  duration : Duration
deriving DecidableEq
```

The route to an alternate destination if the flight decides to divert en-route.

```lean
structure RouteToRevisedDestination where
  destination : Doc7910.Designator
  route       : FreeText
deriving DecidableEq
```

Field 18 DEP may contain the name and position of the departure (if it has no ICAO designator),
or the responsible ATS Unit if it is an air filed flight plan.

```lean
inductive F18Dep
  | namePos (_ : NameAndPosition)
  | unit (_ : ATSUnit)
deriving DecidableEq
```

The various items that make up field 18.

```lean
structure Field18 where
  sts  : Set SpecialHandling
  pbn  : Set PBNCode
  nav  : Option FreeText
  com  : Option FreeText
  dat  : Option FreeText
  sur  : Option FreeText
  dep  : Option F18Dep
  dest : Option NameAndPosition
  reg  : Set Registration
  eet  : List ElapsedTimePoint
  sel  : Option SelcalCode
  typ  : Set (Option NumberOfAircraft × AircraftType)
  code : Option AircraftAddress
  dle  : Set DelayPoint
  opr  : Option FreeText
  orgn : Option FreeText
  per  : Option AircraftPerformance
  altn : List NameAndPosition
  ralt : Set LandingSite
  talt : Set LandingSite
  rif  : Option RouteToRevisedDestination
  rmk  : Option FreeText
  -- Upper limit on number of PBN codes.
  inv  : pbn.card ≤ maxPbnCodes ∧
  -- Upper limit on number of alternate aerodromes.
         altn.length ≤ maxAlternateDestinations ∧
  -- EETs must be presented in ascending order.
         eet.ascendingStrict
deriving DecidableEq
```

### Field 18 Example

`-PBN/A1B1C1D1O2S2T1 NAV/RNP2 REG/VHXYZ SEL/AFPQ CODE/7C6DDF OPR/FLYOU ORGN/YSSYABCO PER/C`

```lean
example : Field18 := {
  sts := ∅,
  pbn := {.a1, .b1, .c1, .d1, .o2, .s2, .t1},
  nav := some ⟨"RNP2", by simp⟩,
  com := none,
  dat := none,
  sur := none,
  dep := none,
  dest := none,
  reg := {⟨"VHXYZ", by simp⟩}
  eet := [],
  sel := some ⟨"AFPQ", by simp⟩,
  typ := ∅,
  code := some ⟨"7C6DDF", by simp⟩,
  dle := ∅,
  opr := some ⟨"FLYOU", by simp⟩,
  orgn := some ⟨"YSSYABCO", by simp⟩,
  per := some .c,
  altn := [],
  ralt := ∅,
  talt := ∅,
  rif := none,
  rmk := none,
  inv := sorry
}
```

## Consistency checks between fields

The legacy nature of the flight planning messages means related information is spread across
disparate fields. As a result a number of constraints are required to ensure consistency
between fields. The majority of these relate to the relationship between field 18 other fields.

### Fields 8 and 15 (requested level)

- If initial requested cruising level is VFR, initial flight rules must be V or Z.

```lean
def F8F15Level (f8 : Field8) (f15 : Field15) : Prop :=
  f15.f15b ▹ f8.f8a ∈ [.v, .z] ‖ (fun _ ↦ True)
```

The notation `x ▹ y ‖ z` is defined in [Util](lib/Util.md).

### Fields 8 and 15 (flight rules)

- Rule changes only allowed if initial rules is Y or Z.
- If initial rules is Y (IFR first), first change must be to VFR.
- If initial rules is Z (VFR first), first change must be to IFR.

```lean
def F8F15Rule (f8 : Field8) (f15 : Field15) : Prop :=
  match (f15.f15c.elements.map RouteElement.ruleOf).reduceOption with
  | []        => f8.f8a ∈ [.i, .v]
  | .vfr :: _ => f8.f8a = .y
  | .ifr :: _ => f8.f8a = .z
```

### Fields 9 and 18 (TYP)

- If designator in field 9b, field 18 TYP not populated.
- If ZZZZ in field 9b, aircraft type in field 18 TYP.

```lean
def F9F18Typ : Field9 → Option Field18 → Prop
  | -- If designator in 9b, 18 TYP not populated.
    {f9b := some _, ..}, none                 => True
  | {f9b := some _, ..}, some {typ := ts, ..} => ts = ∅
  | -- If ZZZZ in 9b, must have aircraft type in 18 TYP.
    {f9b := none, ..}, some {typ := ts, ..}   => ts ≠ ∅
  | -- Any other combination is invalid.
    {f9b := none, ..}, none                   => False
```

### Fields 10 and 18 (STS)

- Can't specify W (RVSM capable) in Field 10a and NONRVSM on Field 18 STS.

```lean
def F10F18Sts (f10 : Field10) (f18 : Option Field18) : Prop :=
  f18 ▹ (.w ∉ f10.f10a ∨ .nonrvsm ∉ ·.sts)
```

### Fields 10 and 18 (PBN)

- If R specified in field 10a, PBN capability must be provided in Field 18 PBN.

```lean
def F10F18Pbn (f10 : Field10) (f18 : Option Field18) : Prop :=
  f18 ▹ .r ∉ f10.f10a ‖ (.r ∈ f10.f10a ↔ ·.pbn ≠ ∅)
```

### Fields 10 and 18 (COM/NAV/DAT)

- If Z specified in field 10a, other information must be provided in at least one of COM,
NAV or DAT in Field 18.

```lean
def F10F18Z (f10 : Field10) (f18 : Option Field18) : Prop :=
  f18 ▹ .z ∉ f10.f10a
      ‖ (fun f18 ↦ .z ∈ f10.f10a ↔ f18.com.isSome ∨ f18.nav.isSome ∨ f18.dat.isSome)
```

### Fields 13 and 18 (DEP)

- If designator in field 13a, field 18 DEP not populated.
- If ZZZZ in field 13a, departure point in field 18 DEP.
- If AFIL in field 13a, ATS unit in field 18 DEP.

```lean
def F13F18Dep : Field13 → Option Field18 → Prop
  | -- If designator in 13a, 18 DEP not populated.
    ⟨(some (.adep _)), _⟩, none
  | ⟨some (.adep _), _⟩, some {dep := none, ..}
  | -- If ZZZZ in 13a, must have departure point in 18 DEP.
    ⟨none, _⟩, some {dep := some (.namePos _), ..}
  | -- If AFIL in 13a, must have ATS unit in 18 DEP.
    ⟨some .afil, _⟩, some {dep := some (.unit _), ..} => True
  | -- Any other combination is invalid.
    _, _                                              => False
```

### Fields 15 and 18 (DLE)

- A delay point must be explicitly named in the route.

```lean
def F15F18Dle (f15 : Field15) (f18 : Option Field18) : Prop :=
  f18 ▹ (·.dle.map (·.point) ⊆ f15.f15c.waypoints)
```

### Fields 16 and 18 (DEST)

- If designator in field 16a, field 18 DEST not populated.
- If ZZZZ in field 16a, destination point in field 18 DEST.

```lean
def F16F18Dest : Field16 → Option Field18 → Prop
  | -- If designator in 16a, 18 DEST not populated.
    {f16a := some _, ..}, none
  | {f16a := some _, ..}, some {dest := none, ..}
  | -- If ZZZZ in 16a, must have destination point in 18 DEST.
    {f16a := none, ..}, some {dest := some _, ..} => True
  | -- Any other combination is invalid.
    _, _                                          => False
```

### Fields 16 and 18 (EET)

- All EETs must be less than the flight duration.

```lean
def F16F18Eet (f16 : Field16) (f18 : Option Field18) : Prop :=
  f18 ▹ (·.eet.all (·.duration < f16.f16b))
```

### Fields 16 and 18 (DLE)

- The sum of the delays at the route points must be less than the flight duration.

```lean
def F16F18Dle (f16 : Field16) (f18 : Option Field18) : Prop :=
  f18 ▹ (fun x ↦ (x.dle.map (·.duration)).add 0 < f16.f16b)
```

### Fields 16 and 18 (ALTN)

- For each ZZZZ entry in Field 16c, there must be a corresponding entry in Field 18 ALTN.

```lean
def F16F18Altn : Field16 → Option Field18 → Prop
  | {f16c := [], ..}, none => True
  | {f16c := altn16, ..}, some {altn := altn18, ..}
                           => (altn16.filter (·.isNone)).length = altn18.length
  | _, _                   => False
```

### Fields 16 and 17 (destination and arrival)

- Destination, if provided, must differ from actual arrival aerodrome.

```lean
def F16F17Dest (f16a : Field16a) (f17 : Option Field17) : Prop :=
  f17 ▹ (f16a ≠ ·.f17a)
```

## Field 22: Amendment

Field 22 specifies changes to an existing flight plan.
If any part of a field changes, the entire content of the new field
must be included in field 22, not just the sub-item that is changing.

```lean
structure Field22 where
  f7  : Option Field7
  f8  : Option Field8
  f9  : Option Field9
  f10 : Option Field10
  f13 : Option Field13
  f15 : Option Field15
  f16 : Option Field16
  f18 : Option Field18
  -- At least one amendment must be specified.
  inv : (f7.isSome ∨ f8.isSome ∨ f9.isSome ∨ f10.isSome ∨ f13.isSome ∨ f15.isSome ∨ f16.isSome ∨ f18.isSome) ∧
        (f8 ▹ fun f8 ↦ f15 ▹ (F8F15Level f8 ·)) ∧
        (f8 ▹ fun f8 ↦ f15 ▹ (F8F15Rule f8 ·)) ∧
        (f9 ▹ (F9F18Typ · f18)) ∧
        (f10 ▹ (F10F18Sts · f18)) ∧
        (f10 ▹ (F10F18Pbn · f18)) ∧
        (f10 ▹ (F10F18Z · f18)) ∧
        (f13 ▹ (F13F18Dep · f18)) ∧
        (f15 ▹ (F15F18Dle · f18)) ∧
        (f16 ▹ (F16F18Dest · f18)) ∧
        (f16 ▹ (F16F18Eet · f18)) ∧
        (f16 ▹ (F16F18Dle · f18)) ∧
        (f16 ▹ (F16F18Altn · f18))
deriving DecidableEq
```

### Field 22 Example

`-8/IX-13/EDDN1230`

```lean
example : Field22 where
  f7  := none
  f8  := some ⟨.i, some .x⟩
  f9  := none
  f10 := none
  f13 := some ⟨some (.adep ⟨"EDDN", by simp⟩), 63072027000⟩
  f15 := none
  f16 := none
  f18 := none
  inv := sorry

end FPL.Field
```
