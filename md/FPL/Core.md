# Core Definitions

This module contains basic definitions of data that are the building blocks of the flight planning messages.
The definitions are of a general nature and are applicable beyond the narrow focus of flight plan processing.

These definitions are required in support of the flight planning specification, but it is sufficient to skim
this module to understand the remainder of the specification.

```lean
import LeanSpec.lib.Util
import LeanSpec.lib.Geo

namespace Core
```

## General Purpose

A number of message fields are free text. While there is a restricted subset of ASCII
characters allowed in the fields, for the purposes of this specification we will ignore
such limitations.

```lean
def maxTextLength := 200

def FreeText := Str 1 maxTextLength
```

## Flight Related

Definitions that relate to the flight that is the subject of a message.

The identifier used by air traffic control to identify the flight.

```lean
def AircraftIdentification := Str 2 7
deriving DecidableEq
```

The SSR (Secondary Surveillance Radar) is a code of four octal characters that is
used to communicate with and track the flight. It is typically allocated by air
traffic control shortly before take off.

```lean
def SsrCode := Str 4 4
```

Depending on the level of equipment held, a flight can operate under instrument flight
rules or visual flight rules.

```lean
inductive FlightRule
  | ifr  -- instrument flight rules
  | vfr  -- visual flight rules
deriving DecidableEq
```

The operating rules for the duration of a flight can be IFR, or VFR, or they may change during the flight.

```lean
inductive FlightRules
  | i  -- IFR
  | v  -- VFR
  | y  -- IFR first, but changing during flight
  | z  -- VFR first, but changing during flight
deriving DecidableEq
```

Flights are categorised to assist with handling.

```lean
inductive TypeOfFlight
  | s  -- Scheduled flight
  | n  -- Non-scheduled flight
  | g  -- General Aviation (GA)
  | m  -- Military
  | x  -- Other
deriving DecidableEq
```

Some flights receive special handling by air traffic control due to their nature.
For example, medical evacuation, head of state, and search and rescue.

```lean
inductive SpecialHandling
  | altrv
  | atfmx
  | ffr
  | fltck
  | hazmat
  | head
  | hosp
  | hum
  | marsa
  | medevac
  | nonrvsm
  | sar
  | state
deriving DecidableEq
```

## Aircraft Related

Definitions that relate to the aircraft used to conduct a flight. Note the
distinction between _flight_ and _aircraft_: _flight_ is the operation between
departure and destination that transports passengers and/or freight, _aircraft_ is
the physical airframe that carries the passengers and/or freight.

The registration identifies the physical aircraft as allocated by the authorising body.
It appears as the tail markings on an aircraft. For GA flights, the aircraft identification
is often the registration mark.

```lean
def Registration := Str 2 7
```

The number of aircraft that participate if the flight is a formation.

```lean
def NumberOfAircraft := NatMN 2 99
```

An aircraft type identifies the type of aircraft. For example, _A388_ is the type
designator for an Airbus A380-800. Such designators are documented in
[ICAO Doc 8643](https://www.icao.int/publications/doc8643/Pages/default.aspx).

```lean
def Doc8643.Designator := Str 2 4
```

Not all aircraft types are listed in Doc 8643. In such case they are presented as free text.

```lean
def AircraftType := Doc8643.Designator ⊕ FreeText
```

The aircraft address is six hexadecimal characters, and uniquely identifies the airframe.

```lean
def AircraftAddress := Str 6 6
```

Performance data relating to the aircraft.

```lean
inductive AircraftPerformance
  | a
  | b
  | c
  | d
  | e
  | h
deriving DecidableEq
```

The wake turbulence category indicates the disturbance of the air caused by the aircraft,
which affects other air traffic.

```lean
inductive WakeTurbulenceCategory
  | h  -- high
  | m  -- medium
  | l  -- low
deriving DecidableEq
```

## Distance: Horizontal and Vertical

Vertical distance may be expressed in metric or imperial measures.

```lean
inductive UnitOfVerticalDistance 
  | feet
  | metres
deriving DecidableEq
```

Vertical distance may be expressed as a flight level (above the transition level)
or an altitude (below the transition level).

```lean
inductive FlightLevelOrAltitude
  | flightLevel
  | altitude
deriving DecidableEq
```

Expression of the vertical position of an aircraft.

```lean
structure VerticalPositionOfAircraft where
  value : Float
  uom   : UnitOfVerticalDistance
  type  : FlightLevelOrAltitude
```

Unit of horizontal distance. For this specification only nautical miles is required.

```lean
inductive UnitOfHorizontalDistance
  | nm
```

Expression of horizontal distance.

```lean
structure HorizontalDistance where
  value : Float₀
  uom   : UnitOfHorizontalDistance
```

## Speed

Speed can be expressed in knots, kilometres per hour, or mach (fraction of the speed of sound).

```lean
inductive UnitOfSpeed
  | kt
  | kph
  | mach
deriving DecidableEq
```

Speed can be:
- true airspeed - how fast the aircraft is moving through the body of air;
- indicated airspeed - the speed as indicated by the aircraft instruments;
- groundspeed - the speed of the aircraft with respect to the ground.

```lean
inductive SpeedDatum
  | tas
  | ias
  | gspd
deriving DecidableEq
```

Aircraft speed is a value with respect to a unit of measurement and a datum.

```lean
structure AircraftSpeed where
  value : Float₀
  uom   : UnitOfSpeed
  datum : SpeedDatum
  inv   : -- Ground speed cannot be expressed as a mach number
          datum = .gspd → uom ≠ .mach
```

True airspeed (TAS) is how fast the aircraft is moving through the body of air.

```lean
def TrueAirspeed := { spd : AircraftSpeed // spd.datum = .tas }
```

## Location Related

Landing sites are recorded and assigned a unique identifier in
[ICAO Doc 7910](https://store.icao.int/en/location-indicators-doc-7910).

```lean
def Doc7910.Designator := Str 4 4
deriving DecidableEq
```

A waypoint is a named point used for identifying the path an aircraft follows.

```lean
def Waypoint := Str 2 5
```

A relative point is a point indicated by its bearing and distance from a known point.

```lean
structure RelativePoint where
  point    : Waypoint
  bearing  : Geo.Direction
  distance : HorizontalDistance
```

Position can be expressed by:

- the geographic position (latitude/longitude);
- a named (and documented) waypoint;
- a relative point.

```lean
inductive Position
  | geo (_ : Geo.Point)
  | wpt (_ : Waypoint)
  | rel (_ : RelativePoint)
```

The named waypoint in a position (if there is one).

```lean
def Position.waypointOf : Position → Option Waypoint
  | .wpt pt => pt
  | _       => none
```

An aircraft needn't always take off or land at a documented point.
Sometimes a descriptive name and lat/long are given.

```lean
structure NameAndPosition where
  name     : FreeText
  position : Position
```

A landing site is identified by its ICAO designator or name and position.

```lean
def LandingSite := Doc7910.Designator ⊕ NameAndPosition
```

The air space through which aircraft transit is divided into areas called
Flight Information Regions (FIR). They are documented in ICAO Doc 7910.

```lean
def Doc7910.FIRDesignator := Str 4 4
```

## Equipment and Capabilities

The communication, navigation and surveillance equipment held by aircraft
and the capabilities of the equipment are identified by codes documented
in PANS-ATM.

Communication, navigation and approach aid equipment and capabilities.

```lean
inductive CommNavAppCode
  | s
  | a
  | b
  | c
  | d
  | e1
  | e2
  | e3
  | f
  | g
  | h
  | i
  | j1
  | j2
  | j3
  | j4
  | j5
  | j6
  | j7
  | k
  | l
  | m1
  | m2
  | m3
  | o
  | p1
  | p2
  | p3
  | p4
  | p5
  | p6
  | p7
  | p8
  | p9
  | r
  | t
  | u
  | v
  | w
  | x
  | y
  | z
deriving DecidableEq
```

Surveillance equipment and capabilities.

```lean
inductive SurveillanceCode
  | a
  | c
  | e
  | h
  | i
  | l
  | p
  | s
  | x
  | b1
  | b2
  | u1
  | u2
  | v1
  | v2
  | d1
  | g1
deriving DecidableEq
```

Performance Based Navigation (PBN) codes.

```lean
inductive PBNCode
  | a1
  | b1
  | b2
  | b3
  | b4
  | b5
  | b6
  | c1
  | c2
  | c3
  | c4
  | d1
  | d2
  | d3
  | d4
  | l1
  | o1
  | o2
  | o3
  | o4
  | s1
  | s2
  | t1
  | t2
deriving DecidableEq
```

Selective Calling (SELCAL) code.

```lean
def SelcalCode := Str 4 4
```

## Route Related

A designator for an air route (a fixed route in 3D space that an aircraft can follow).

```lean
def RouteDesignator := Str 2 7
```

Indicator that a flight will proceed directly between two points.

```lean
inductive Dct | dct
```

## Stakeholder Communication

Designator for an Air Traffic Services authority.

```lean
def ATSUnit := Str 4 4
```

Address on the global Aeronautical Fixed Telecommunications Network (AFTN).

```lean
def AFTNAddress := Str 8 8

end Core
```
