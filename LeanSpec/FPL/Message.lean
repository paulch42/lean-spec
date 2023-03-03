/-
# Flight Planning Messages

This module defines the content and properties of the flight plan related ATS messages defined in PANS-ATM.
-/
import LeanSpec.FPL.Flight

open Temporal Core FPL.Field

namespace FPL

/-
## IsConsistent

Instances of class `IsConsistent` have a method that determines if the instance is consistent with a flight.
-/
class IsConsistent (α : Type) (_ : Flight) where
  isConsistent : α → Prop

/-
## Filed Flight Plan: FPL

The content and constraints of a FPL (filed flight plan) message.
-/
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
  inv₄  : f10_f18_sts f10 f18
  inv₅  : f10_f18_pbn f10 f18
  inv₆  : f10_f18_z f10 f18
  inv₇  : f13_f18_dep f13 f18
  inv₈  : f15_f18_dle f15 f18
  inv₉  : f16_f18_dest f16 f18
  inv₁₀ : f16_f18_altn f16 f18
  inv₁₁ : f16_f18_eet f16 f18
  inv₁₂ : f16_f18_dle f16 f18

/-
The flight time derived from a FPL.
-/
instance : FlightTime FPL where
  period fpl := adepAdesFlightTime fpl.f13.f13a fpl.f13.f13b fpl.f16.f16a fpl.f16.f16b

/-
Flight identification derived from a FPL.
-/
instance : IsFlight FPL where
  idOf fpl := ⟨fpl.f7.f7a, fpl.f13.f13a, FlightTime.period fpl⟩

/-
Flight generated from a FPL. Most of the flight fields are identical to the corresponding FPL fields.
-/
instance : ToFlight FPL where
  toFlight fpl := ⟨.filed, fpl.f7, fpl.f8, fpl.f9, fpl.f10, fpl.f13, fpl.f15, fpl.f16, none, fpl.f18, sorry⟩

/-
## Modification: CHG

The content and constraints of a CHG (modification) message.
-/
structure CHG where
  f7  : Field7
  f13 : Field13
  f16 : Field16a
  f22 : Field22

/-
Fields 7, 13 and 16 are used for matching, field 22 specifies the modification.

The flight time derived from a CHG.
-/
instance : FlightTime CHG where
  period chg := adepAdesFlightTime chg.f13.f13a chg.f13.f13b chg.f16 none

/-
Flight identification derived from a CHG.
-/
instance : IsFlight CHG where
  idOf chg := ⟨chg.f7.f7a, chg.f13.f13a, FlightTime.period chg⟩ 

/-
Is a CHG consistent with the flight to which it is applied?
The consistency checks are those defined in [FPL.Field](Field.md).
If a field changes it must be checked for consistency with any related fields.
If a related field is also in the CHG, check there, otherwise check against
the related field in the flight.
-/
instance (f : Flight) : IsConsistent CHG f where
  isConsistent | {f22 := ⟨_,f8,f9,f10,f13,f15,f16,f18,_⟩, ..} =>
                 checkOpt f8_f15_level f8 f15 f.f8 f.f15 ∧
                 checkOpt f8_f15_frul f8 f15 f.f8 f.f15 ∧
                 checkOpt f9_f18_typ f9 f18 f.f9 f.f18 ∧
                 checkOpt f10_f18_sts f10 f18 f.f10 f.f18 ∧
                 checkOpt f10_f18_pbn f10 f18 f.f10 f.f18 ∧
                 checkOpt f10_f18_z f10 f18 f.f10 f.f18 ∧
                 checkOpt f13_f18_dep f13 f18 f.f13 f.f18 ∧
                 checkOpt f15_f18_dle f15 f18 f.f15 f.f18 ∧
                 checkOpt f16_f18_dest f16 f18 f.f16 f.f18 ∧
                 checkOpt f16_f18_eet f16 f18 f.f16 f.f18 ∧
                 checkOpt f16_f18_dle f16 f18 f.f16 f.f18 ∧
                 checkOpt f16_f18_altn f16 f18 f.f16 f.f18
where checkOpt {α β : Type} (p : α → β → Prop) : Option α → Option β → Option α → Option β → Prop
      | some chga, some chgb, _, _    => p chga chgb
      | some chga, none, _, some fltb => p chga fltb
      | none, some chgb, some flta, _ => p flta chgb
      | _, _, _, _                    => True

/-
## Cancellation: CNL

The content and constraints of a CNL (cancellation) message.
-/
structure CNL where
  f7  : Field7
  f13 : Field13
  f16 : Field16a

/-
The flight time derived from a CNL.
-/
instance : FlightTime CNL where
  period cnl := adepAdesFlightTime cnl.f13.f13a cnl.f13.f13b cnl.f16 none

/-
Flight identification derived from a CNL.
-/
instance : IsFlight CNL where
  idOf cnl := ⟨cnl.f7.f7a, cnl.f13.f13a, FlightTime.period cnl⟩ 

/-
## Delay: DLA

The content and constraints of a DLA (delay) message.
-/
structure DLA where
  f7  : Field7
  f13 : Field13
  f16 : Field16a

/-
Field 13b contains the new estimated departure time.

The flight time derived from a DLA.
-/
instance : FlightTime DLA where
  period dla := adepAdesFlightTime dla.f13.f13a dla.f13.f13b dla.f16 none

/-
Flight identification derived from a DLA.
-/
instance : IsFlight DLA where
  idOf dla := ⟨dla.f7.f7a, dla.f13.f13a, FlightTime.period dla⟩ 

/-
## Departure: DEP

The content and constraints of a DEP (departure) message.
-/
structure DEP where
  f7  : Field7
  f13 : Field13
  f16 : Field16a

/-
Field 13b conatins the actual time of departure.

The flight time derived from a DEP.
-/
instance : FlightTime DEP where
  period dep := adepAdesFlightTime dep.f13.f13a dep.f13.f13b dep.f16 none

/-
Flight identification derived from a DEP.
-/
instance : IsFlight DEP where
  idOf dep := ⟨dep.f7.f7a, dep.f13.f13a, FlightTime.period dep⟩ 

/-
## Arrival: ARR

The content and constraints of an ARR (arrival) message.
-/
structure ARR where
  f7  : Field7
  f13 : Field13
  f16 : Field16a
  f17 : Field17
  inv : f16_f17_dest f16 f17

/-
The flight time derived from an ARR.
-/
instance : FlightTime ARR where
  period arr := let dest := -- Use the planned destination if available, otherwise the actual arrival.
                            match arr.f16, arr.f17.f17a with
                            | none, actual  => actual
                            | planned, _    => planned
                adepAdesFlightTime arr.f13.f13a arr.f13.f13b dest none

/-
The flight time is typically used to match the ARR with a flight. The original flight time
was dervied from the planned destination, hence the planned destination (if available) is
preferred over the actual arrival for flight time calculation.

Flight identification derived from an ARR.
-/
instance : IsFlight ARR where
  idOf arr := ⟨arr.f7.f7a, arr.f13.f13a, FlightTime.period arr⟩ 

/-
## Message

A flight plan related message is then the union of the different types of message.
-/
inductive Message
  | fpl (_ : FPL)
  | chg (_ : CHG)
  | cnl (_ : CNL)
  | dla (_ : DLA)
  | dep (_ : DEP)
  | arr (_ : ARR)

/-
The flight time derived from a message.
-/
open FlightTime in
instance : FlightTime Message where
  period | .fpl x => period x
         | .chg x => period x
         | .cnl x => period x
         | .dla x => period x
         | .dep x => period x
         | .arr x => period x

/-
Flight identification derived from a message.
-/
open IsFlight in
instance : IsFlight Message where
  idOf | .fpl x => idOf x
       | .chg x => idOf x
       | .cnl x => idOf x
       | .dla x => idOf x
       | .dep x => idOf x
       | .arr x => idOf x

/-
Is a message consistent with the flight to which it applies.
CHG is the only message that may not be consistent.
-/
open IsConsistent in
instance (flt : Flight) : IsConsistent Message flt where
  isConsistent | .chg chg => isConsistent flt chg
               | _        => True

end FPL