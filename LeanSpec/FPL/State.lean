/-
# Flight Plan Processing

The `Core`, `Field`, `Flight` and `Message` modules capture the content, structure and constraints
of flight information and the messages used to communicate information about the flights.
This module models the processing of flight plan messages with respect to a state of flights.
The specification consists of:

- Definition of a state in which information on known flights is maintained.
- The processing of received messages against the state and how it is updated, including the
handling of invalid messages.
- Maintenance activities on the state such as purging of expired flights.
-/
import LeanSpec.FPL.Message

open Temporal Core FPL.Field FPL.Flight

namespace FPL

/-
## Timestamped Message

For auditing purposes it is necessary to record when a message is received.
-/
structure TimestampedMessage where
  timestamp : DTG
  message   : Message

/-
The `<` order relation on `TimestampedMessage`. Order by time of reception.
-/
instance : LT TimestampedMessage where
  lt := fun ⟨t₁,_⟩ ⟨t₂,_⟩ ↦ t₁ < t₂

/-
The `<` relation is decidable.
-/
instance (x y : TimestampedMessage) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.timestamp < y.timestamp))

/-
## Flight History

For investigation and analysis purposes, the latest information is maintained together
with the sequence of messages received for that flight, hence consists of:

- The current accumulated information on the flight.
- The sequence of messages received for the flight.
-/
structure FlightHistory where
  flight  : Flight
  history : List TimestampedMessage
  inv₁    : -- the history must include at least one message
            history ≠ []
  inv₂    : -- messages are in descending timestamp order (i.e. most recent first)
            history.descendingStrict

/-
The flight time derived from a flight history.
-/
instance : FlightTime FlightHistory where
  period fhist := FlightTime.period fhist.flight

/-
Flight identification derived from a flight history.
-/
instance : Identity FlightHistory where
  idOf fhist := Identity.idOf fhist.flight

/-
## Flight Store

A flight store is a mapping from flight identifiers to historical information about the flight.
-/
def FlightStore := FlightId ⟹ FlightHistory
deriving Membership

/-
## Failed Messages

The reasons why a received message may not match with the flights already held.
-/
inductive FailureReason
  | outOfSequence  -- the received message is out of sequence with respect to its timestamp
  | badMatch       -- matching failed; could be failure to match, unexpected match,
                   -- or match with multiple entries
  | inconsistent   -- the content of the message, if applied, would be inconsistent

/-
The information maintained about a received message that failed to process.
-/
structure FailedMessage where
  msg    : TimestampedMessage
  reason : FailureReason
  fmatch : List FlightId  -- list of matching messages (if any) that caused the failure

/-
The `fmatch` item is the list of flights that matched the failed message. Such information
is valuable when investigating why messages could not be processed, and may suggest
improvements to how matching is performed.

## State

The `State` maintains all information about known flights. The state consists of:
- Currently active flights.
- Inactive flights. That is, flights that have expired or completed but are still maintained for analysis purposes. 
- Received messages that could not be processed.
-/
structure State where
  active   : FlightStore
  inactive : FlightStore
  failed   : List FailedMessage
  inv      : -- two different active flights cannot match
             ∀ x ∈ active.domain, ∀y ∈ active.domain, x ≠ y → ¬ x.match y

namespace State

/-
The `State` constraint is fundamental: two active flights cannot match. Failure to comply
with the constraint would result in a duplicate flights, which is a problem encountered in
flight planning systems in operation. Separating active and inactive flights reduces the
opportunity for false matches.

The active flights in a state that match the supplied identifier.
-/
def activeMatch (fid : FlightId) (state : State) : Std.AssocList FlightId FlightHistory :=
  state.active.val.filter fid.match

/-
The identifiers of the active flights in a state that match the supplied identifier.
-/
def activeMatchId (fid : FlightId) (state : State) : List FlightId :=
  (state.activeMatch fid).domain

/-
The active flights in a state.
-/
def activeFlights (state : State) : List Flight :=
  state.active.range.map (·.flight)

/-
## Message Processing

Relationship between the pre and post state when a message cannot be processed.
-/
def failure (pre post : State) (ref : DTG) (msg : Message) (reason : FailureReason) (fids : List FlightId) :=
  -- no change to active flights
  post.active = pre.active ∧
  -- no change to inactive flights
  post.inactive = pre.inactive ∧ 
  -- received message added to failed messages
  (∀f, f ∈ post.failed ↔ f ∈ pre.failed ∨ f = ⟨⟨ref, msg⟩, reason, fids⟩)

/-
Relationship between the pre and post state when a message causes a new flight to be added.
-/
def added (pre post : State) (ref : DTG) (msg : Message) (flight : Flight):=
  -- new flight added to active store
  (∀ flt, flt ∈ post.active ↔ flt ∈ pre.active ∨ (flt.1 = Identity.idOf flt.2 ∧
                                                  flt.2.flight = flight ∧
                                                  flt.2.history = [⟨ref, msg⟩])) ∧
  -- no change to inactive flights
  post.inactive = pre.inactive ∧
  -- no change to failed messages
  post.failed = pre.failed

/-
Process a message that, if successful, adds a new flight to the state.
-/
def ProcessAdd (ref : DTG) (msg : Message) (pre : State) (newFlight : Flight) :=
  { post : State // -- match received message against active flights
                    match pre.activeMatchId (Identity.idOf msg) with 
                    | -- no matching flight
                      [] => -- new flight added to active store
                            added pre post ref msg newFlight
                    | -- one or more matching flights
                      fs => failure pre post ref msg .badMatch fs }

-- Process a message that, if successful, modifies an existing flight in the state.
-- (This should be a block comment but `lean2md` aborts claiming nested comment.)
def ProcessMod (ref : DTG) (msg : Message) (pre : State) (modFlight : Flight → Flight) :=
  { post : State // -- match received message against active flights
                    match pre.activeMatch (Identity.idOf msg) with
                    | -- single matching flight
                      .cons fid fh .nil =>
                            let inSeq := -- is the message temporally sequenced wrt matching flight
                                         ref > (fh.history.head fh.inv₁).timestamp
                            let consistent := -- is the message consistent wrt matching flight
                                              IsConsistent.isConsistent fh.flight msg
                            (inSeq ∧ consistent → 
                               updated pre post fh msg) ∧
                            (inSeq ∧ ¬ consistent →
                               failure pre post ref msg .inconsistent [fid]) ∧
                            (¬ inSeq →
                               failure pre post ref msg .outOfSequence [fid])
                    | -- no or multiple matching flights
                      fs  => failure pre post ref msg .badMatch fs.domain }

  where -- relationship between pre and post state for successful message update
        updated (pre post : State) (prehist : FlightHistory) (msg : Message) :=
          ∀ flt, flt ∈ post.active ↔ xformFlight pre prehist msg flt ∧
          post.inactive = pre.inactive ∧ 
          post.failed = pre.failed

        -- relationship between a flight and its transformation under a message
        xformFlight (pre : State) (prehist : FlightHistory) (msg : Message)
                    (flt : FlightId × FlightHistory) :=
          let isMatch := flt.1.match (Identity.idOf msg)
          (isMatch ↔ flt.1 = Identity.idOf flt.2 ∧
                     flt.2.flight = modFlight prehist.flight ∧
                     flt.2.history = ⟨ref, msg⟩ :: prehist.history) ∧
          (¬ isMatch ↔ flt ∈ pre.active)

/-
The `Flight` created from a `FPL`.
-/
def fplFlight (fpl : FPL) :=
  ToFlight.toFlight fpl

/-
How a `CHG` modifies a `Flight`.
-/
def chgFlight (chg : CHG) (flt : Flight) : Flight :=
  let ⟨f7, f8, f9, f10, f13, f15, f16, f18, _⟩ := chg.f22 
  { flt with f7  := chg.f22.f7.getD flt.f7,
             f8  := chg.f22.f8.getD flt.f8,
             f9  := chg.f22.f9.getD flt.f9,
             f10 := chg.f22.f10.getD flt.f10,
             f13 := chg.f22.f13.getD flt.f13,
             f15 := chg.f22.f15.getD flt.f15,
             f16 := chg.f22.f16.getD flt.f16,
             f18 := match chg.f22.f18 with
                    | none   => flt.f18
                    | some x => x,
             inv := sorry }

/-
How a `DLA` modifies a `Flight`.
-/
def dlaFlight (dla : DLA) (flt : Flight)  : Flight :=
  { flt with f13.f13b := (Identity.idOf dla).period.starts,
             f16.f16a := dla.f16,
             inv := sorry }

/-
How a `CNL` modifies a `Flight`.
-/
def cnlFlight (cnl : CNL) (flt : Flight) : Flight :=
  { flt with status := .cancelled,
             f13.f13b := (Identity.idOf cnl).period.starts,
             f16.f16a := cnl.f16,
             inv := sorry }

/-
How a `DEP` modifies a `Flight`.
-/
def depFlight (dep : DEP) (flt : Flight) : Flight :=
  { flt with status := .airborne,
             f13.f13b := (Identity.idOf dep).period.starts,
             f16.f16a := dep.f16,
             inv := sorry }

/-
How an `ARR` modifies a `Flight`.
-/
def arrFlight (arr : ARR) (flt : Flight) : Flight :=
  { flt with status := .completed,
             f13.f13b := (Identity.idOf arr).period.starts,
             f16.f16a := match arr.f16 with
                         | none => flt.f16.f16a
                         | some ades => arr.f16
             f17 := arr.f17,
             inv := sorry }

/-
Given a message and its time of reception, how is the state transformed.
-/
def Process (ref : DTG) (msg : Message) (state : State) :=
  match msg with
  | .fpl fpl => ProcessAdd ref msg state (fplFlight fpl)
  | .chg chg => ProcessMod ref msg state (chgFlight chg)
  | .dla dla => ProcessMod ref msg state (dlaFlight dla)
  | .cnl cnl => ProcessMod ref msg state (cnlFlight cnl)
  | .dep dep => ProcessMod ref msg state (depFlight dep)
  | .arr arr => ProcessMod ref msg state (arrFlight arr)

/-
Note the definition is a dependent type. Given a reference timestamp (`ref`), a message (`msg`),
and a state (`state`), `Process ref msg state` is a type, the type of states that result from
processing `msg` at time `ref` against `state`. An element of the type is an updated state that
satisfies all the constraints.

## State Management

Two examples of state management are presented.

How long is a flight held in the active store after it expires.
-/
def expirePeriod : Duration := Duration.oneHour

/-
Transform a state by moving expired active flights to the inactive store.
-/
def Expire (ref : DTG) (pre : State) :=
  let threshold := -- an active flight with timestamp prior to the threshold is expired
                   ref - expirePeriod
  let expired := -- the active flights that have expired
                 pre.active.filter (·.period.ends < threshold)
  { post : State // (∀ idh, idh ∈ post.active ↔ idh ∈  pre.active ∧ idh ∉ expired) ∧
                    (∀ idh, idh ∈ post.inactive ↔ idh ∈ pre.inactive ∨ idh ∈ expired ) ∧
                    post.failed = pre.failed }

/-
How long is a data held in the state when it is no longer active.
-/
def purgePeriod : Duration := Duration.oneDay

/-
Transform a state by purging entries (inactive flights and failed messages) that have expired.
-/
def Purge (ref : DTG) (pre : State) :=
  let threshold := -- an inactive flight with timestamp prior to the threshold is purged
                   ref - purgePeriod
  { post : State // post.active = pre.active ∧
                    (∀ idh, idh ∈ post.inactive ↔ idh ∈ pre.inactive ∧ idh.1.period.ends > threshold) ∧
                    (∀ f, f ∈ post.failed ↔ f ∈ pre.failed ∧ f.msg.timestamp > threshold) }

/-
## Flight Query

The final section specifies a simple querying function. Retrieve all active flights from the state
that match query parameters. Something very similar to this occurs in operation on a daily basis.

The query parameters are:

- aircraft identification;
- departure point;
- take off interval;
- destination point.
-/
structure Query where
  acid : Option AircraftIdentification
  adep : Option Doc7910.Designator
  eobt : Option Interval
  ades : Option Doc7910.Designator

/-
Any of the query fields may be omitted, in which case any value matches.

Does a flight match against a query?
-/
def queryMatch (q : Query) (f : Flight) : Bool :=
  matchAcid q.acid f.f7.f7a ∧
  matchLoc q.adep f.f13.desigOf ∧
  matchEobt q.eobt f.f13.f13b ∧
  matchLoc q.ades f.f16.f16a
where -- match on aircraft identification
      matchAcid (q : Option AircraftIdentification) (f : AircraftIdentification) : Bool :=
        q.isNone ∨ q = f
      -- matching on location (departure and destination)
      matchLoc (q : Option Doc7910.Designator) (f : Option Doc7910.Designator) : Bool :=
        q.isNone ∨ q = f
      -- matching on departure time
      matchEobt : Option Interval → DTG → Bool
        | none, _     => True
        | some i, dtg => i.contains dtg

/-
The active flights in the state that match a query.
-/
def QueryMatch (state : State) (query : Query) :=
  { fs : List Flight // ∀ f, f ∈ fs ↔ f ∈ activeFlights state ∧ queryMatch query f }

end State