# Flight Planning

This example is significantly larger than the previous examples and is in many ways more typical of the
type of system that would be encountered in industry. It is characterised by:
- a state of information on flights is held;
- messages are received concerning new and existing flights;
- the state is updated based on the content of the received messages;
- maintenance is performed on the state to, for example, remove expired entries;
- the state is queried for information.

## Background

One of the tasks required of an aircraft operator is to report an intent to fly to the Air Traffic
Services (ATS) provider. The operator must indicate where and when they intend to fly, and provide
various items of information concerning the flight and the aircraft with which the flight will
be conducted.

The reporting is carried out via a number of standard flight planning messages. These messages
are defined by the International Civil Aviation Organisation (ICAO) and documented in the
[Procedures for Air Navigation Services: Air Traffic Management (PANS-ATM)](https://store.icao.int/en/procedures-for-air-navigation-services-air-traffic-management-doc-4444).
It is document number 4444 published by ICAO, so is often referred to as _Doc 4444_.

Appendix 3 of PANS-ATM describes a number of messages employed for communicating flight information.
A subset of those specifically relate to flight planning:

| Message Type | Purpose |
| - | - |
| FPL | File a plan for an intended flight |
| DLA | Report a delay to a previously filed flight |
| CHG | Modify a previously filed flight plan |
| CNL | Cancel a planned flight |
| DEP | Report a flight has departed |
| ARR | Report a flight has arrived |

An example FPL message is:
```
(FPL-ABC123-IS
-B738/M-SADE2E3GHIRWZ/LB1
-YSSY0400
-M079F380 DCT WOL H65 RAZZI Q29 LIZZI DCT
-YMML0100
-PBN/A1B1C1D1O2S2T1 NAV/RNP2 DOF/230220 REG/VHXYZ SEL/AFPQ CODE/7C6DDF OPR/FLYOU ORGN/YSSYABCO PER/C)
```
Flight _ABC123_ is flying from _YSSY_ (Sydney) to _YMML_ (Melbourne) departing _0400_ on _20/2/2023_ with an
expected flight time of one hour. The aircraft is a Boeing 737-800 (_B738_). The text _WOL H65 RAZZI Q29 LIZZI DCT_
is a description of the route the flight will follow. The last line contains various pieces of additional information
such as the aircraft registration (_VHXYZ_).

A collection of numerically labelled fields are defined, each containing a subset of the information that relates to a flight.
Different messages are then defined by selecting the appropriate set of fields for
the purpose of the message. In the above FPL, those fields are:

| Field Number | Content |
| - | - |
| 7 | ABC123 |
| 8 | IS |
| 9 | B738/M |
| 10 | SADE2E3GHIRWZ/LB1 |
| 13 | YSSY0400 |
| 15 | M079F380 DCT WOL H65 RAZZI Q29 LIZZI DCT |
| 16 | YMML0100 |
| 18 | PBN/A1B1C1D1O2S2T1 NAV/RNP2 DOF/230220 REG/VHXYZ SEL/AFPQ CODE/7C6DDF OPR/FLYOU ORGN/YSSYABCO PER/C |

## The Specification

The specification is concerned with the processing of flight plan and related messages, and consists of:

- a model of the data elements, fields, flights and messages;
- definition of invariants on the flights and messages, which primarily capture consistency constraints between the different fields;
- the definition of a state that models a collection of flight information that might be held by a system;
- given a state and a received message, the specification of how a revised state is created from the supplied state and the message;
- some maintenance activities on the state;
- querying the state.

The model and program specification are contained in five modules:

| Module | Purpose |
| - | - |
| [Core](FPL/Core.md)       | The core data elements from which higher level entities are built |
| [Field](FPL/Field.md)     | The fields from which the messages are assembled |
| [Flight](FPL/Flight.md)   | Data entity capturing all information on a flight |
| [Message](FPL/Message.md) | The various messages employed for flight planning purposes |
| [State](FPL/State.md)     | The processing of messages with respect to a state |

These modules depend on the general purpose definitions in [Util](lib/Util.md), [Geo](lib/Geo.md) and [Temporal](lib/Temporal.md).
