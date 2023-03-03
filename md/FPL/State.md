# State Management

The [Core](Core.md), [Field](Field.md), [Flight](Flgiht.md) and [Message](Message.md) modules
capture the content, structure and constraints of flight information and the messages used to
communicate information about the flights. This module models the processing of flight plan
messages with respect to a state of flights. The specification consists of:

- Definition of a state in which information on known flights is maintained.
- The processing of received messages against the state and how it is updated, including the
handling of invalid messages.
- Maintenance activities on the state such as purging of expired flights.
- Querying the state for flight information.

```lean
import LeanSpec.FPL.Message

open Temporal Core FPL.Field FPL.Flight

namespace FPL
```

## Timestamped Message

For auditing purposes it is necessary to record when a message is received.

```lean
structure TimestampedMessage where
  timestamp : DTG
  message   : Message
```

The `<` order relation on `TimestampedMessage`. Order by time of reception.

```lean
instance : LT TimestampedMessage where
  lt tm₁ tm₂ := tm₁.timestamp < tm₂.timestamp
```

The `<` relation is decidable.

```lean
instance (x y : TimestampedMessage) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.timestamp < y.timestamp))
```

## Flight History

For investigation and analysis purposes, the latest information is maintained together
with the sequence of messages received for that flight, hence consists of:

- The current accumulated information on the flight.
- The sequence of messages received for the flight.

```lean
structure FlightHistory where
  flight  : Flight
  history : List TimestampedMessage
  -- The history must include at least one message.
  inv₁    : history ≠ []
  -- Messages are in descending timestamp order (i.e. most recent first).
  inv₂    : history.descendingStrict
```

The flight time derived from a flight history.

```lean
instance : FlightTime FlightHistory where
  period fhist := FlightTime.period fhist.flight
```

Flight identification derived from a flight history.

```lean
instance : IsFlight FlightHistory where
  idOf fhist := IsFlight.idOf fhist.flight
```

## Flight Store

A flight store is a mapping from flight identifiers to historical information about the flight.

```lean
def FlightStore := FlightId ⟹ FlightHistory
deriving Membership
```

## Failed Messages

The reasons why a received message may not match with the flights already held.

```lean
inductive FailureReason
  | outOfSequence  -- the received message is out of sequence with respect to its timestamp
  | badMatch       -- matching failed; could be failure to match, unexpected match,
                   -- or match with multiple entries
  | inconsistent   -- the content of the message, if applied, would be inconsistent
```

The information maintained about a received message that failed to process.

```lean
structure FailedMessage where
  msg    : TimestampedMessage
  reason : FailureReason
  fmatch : List FlightId  -- list of matching messages (if any) that caused the failure
```

The `fmatch` item is the list of flights that matched the failed message. Such information
is valuable when investigating why messages could not be processed, and may suggest
improvements to how matching is performed.

## State

The `State` maintains all information about known flights. The state consists of:
- Currently active flights.
- Inactive flights. That is, flights that have expired or completed but are still maintained for analysis purposes. 
- Received messages that could not be processed.

```lean
structure State where
  active   : FlightStore
  inactive : FlightStore
  failed   : List FailedMessage
  -- Two different active flights cannot match.
  inv      : ∀ x ∈ active.domain, ∀y ∈ active.domain, x ≠ y → ¬ x.match y

namespace State
```

The `State` constraint is fundamental: two active flights cannot match. Failure to comply
with the constraint would result in duplicate flights, which is a problem encountered in
flight planning systems in operation. Separating active and inactive flights reduces the
opportunity for false matches.

The active flights in a state that match the supplied identifier.

```lean
def activeMatch (fid : FlightId) (state : State) : FlightId ⟹ FlightHistory :=
  state.active.filter fid.match
```

The identifiers of the active flights in a state that match the supplied identifier.

```lean
def activeMatchId (fid : FlightId) (state : State) : List FlightId :=
  (state.activeMatch fid).domain
```

The active flights in a state.

```lean
def activeFlights (state : State) : List Flight :=
  state.active.range.map (·.flight)
```

## Message Processing

This section specifies how a received message is processed with respect to a state.
It is the most complex part of the specification.

Specify the relationship between the pre and post state when a message cannot be processed, given the
message and reason for failure.

```lean
def failure (pre post : State) (ref : DTG) (msg : Message) (reason : FailureReason) (fids : List FlightId) :=
  -- No change to active flights.
  post.active = pre.active ∧
  -- No change to inactive flights.
  post.inactive = pre.inactive ∧ 
  -- Received message added to failed messages.
  (∀f, f ∈ post.failed ↔ f ∈ pre.failed ∨ f = ⟨⟨ref, msg⟩, reason, fids⟩)
```

Specify the relationship between the pre and post state when a FPL causes a new flight to be added.

```lean
def flightAdded (pre post : State) (ref : DTG) (fpl : FPL) :=
  -- New flight added to active store.
  (∀ flt, flt ∈ post.active ↔ flt ∈ pre.active ∨ (flt.1 = IsFlight.idOf flt.2 ∧
                                                  flt.2.flight = ToFlight.toFlight fpl ∧
                                                  flt.2.history = [⟨ref, .fpl fpl⟩])) ∧
  -- No change to inactive flights.
  post.inactive = pre.inactive ∧
  -- No change to failed messages.
  post.failed = pre.failed
```

Specify the relationship between pre and post state for update of an existing flight.

```lean
def flightUpdated (pre post : State) (ref : DTG) (prehist : FlightHistory) (msg : Message) (modFlight : Flight → Flight) :=
  -- Matching flight updated in active store.
  (∀ flt, flt ∈ post.active ↔ let isMatch := flt.1.match (IsFlight.idOf msg)
                              (isMatch ↔ flt.1 = IsFlight.idOf flt.2 ∧
                                         flt.2.flight = modFlight prehist.flight ∧
                                         flt.2.history = ⟨ref, msg⟩ :: prehist.history) ∧
                              (¬ isMatch ↔ flt ∈ pre.active)) ∧
  -- No change to inactive flights.
  post.inactive = pre.inactive ∧
  -- No change to failed messages.
  post.failed = pre.failed
```

Process a message that, if successful, adds a new flight to the state.
The message must not match with an existing active flight.

```lean
def ProcessAdd (ref : DTG) (fpl : FPL) (pre : State) :=
  { post : State // -- Match received message against active flights.
                    match pre.activeMatchId (IsFlight.idOf fpl) with 
                    | -- No matching flight.
                      [] => -- New flight added to active store.
                            flightAdded pre post ref fpl
                    | -- One or more matching flights.
                      fs => -- Record as a failed message.
                            failure pre post ref (.fpl fpl) .badMatch fs }
```

Process a message that, if successful, modifies an existing flight in the state.
The message must match with exactly one flight in the active store.

```lean
def ProcessMod (ref : DTG) (msg : Message) (pre : State) (modFlight : Flight → Flight) :=
  { post : State // -- Match received message against active flights.
                    match (pre.activeMatch (IsFlight.idOf msg)).val with
                    | -- Single matching flight.
                      .cons fid fh .nil =>
                            let inSeq := -- Is the message temporally sequenced wrt matching flight?
                                         ref > (fh.history.head fh.inv₁).timestamp
                            let consistent := -- Is the message consistent wrt matching flight?
                                              IsConsistent.isConsistent fh.flight msg
                            (inSeq ∧ consistent → 
                               flightUpdated pre post ref fh msg modFlight) ∧
                            (inSeq ∧ ¬ consistent →
                               failure pre post ref msg .inconsistent [fid]) ∧
                            (¬ inSeq →
                               failure pre post ref msg .outOfSequence [fid])
                    | -- No or multiple matching flights.
                      fs  => failure pre post ref msg .badMatch fs.domain }
```

How a `CHG` modifies a `Flight`. A field in the CHG replaces the corresponding field in the
flight, otherwise the field in the flight is unchanged.

```lean
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
```

How a `DLA` modifies a `Flight`.

```lean
def dlaFlight (dla : DLA) (flt : Flight)  : Flight :=
  { flt with f13.f13b := (IsFlight.idOf dla).period.starts,
             f16.f16a := dla.f16,
             inv := sorry }
```

How a `CNL` modifies a `Flight`.

```lean
def cnlFlight (cnl : CNL) (flt : Flight) : Flight :=
  { flt with status := .cancelled,
             f13.f13b := (IsFlight.idOf cnl).period.starts,
             f16.f16a := cnl.f16,
             inv := sorry }
```

How a `DEP` modifies a `Flight`.

```lean
def depFlight (dep : DEP) (flt : Flight) : Flight :=
  { flt with status := .airborne,
             f13.f13b := (IsFlight.idOf dep).period.starts,
             f16.f16a := dep.f16,
             inv := sorry }
```

How an `ARR` modifies a `Flight`.

```lean
def arrFlight (arr : ARR) (flt : Flight) : Flight :=
  { flt with status := .completed,
             f13.f13b := (IsFlight.idOf arr).period.starts,
             f16.f16a := match arr.f16 with
                         | none => flt.f16.f16a
                         | some ades => arr.f16
             f17 := arr.f17,
             inv := sorry }
```

Given a message and its time of reception, how is the state transformed.

```lean
def Process (ref : DTG) (msg : Message) (state : State) :=
  match msg with
  | .fpl fpl => ProcessAdd ref fpl state
  | .chg chg => ProcessMod ref msg state (chgFlight chg)
  | .dla dla => ProcessMod ref msg state (dlaFlight dla)
  | .cnl cnl => ProcessMod ref msg state (cnlFlight cnl)
  | .dep dep => ProcessMod ref msg state (depFlight dep)
  | .arr arr => ProcessMod ref msg state (arrFlight arr)
```

Note the definition is a dependent type. Given a reference timestamp (`ref`), a message (`msg`),
and a state (`state`), `Process ref msg state` is a type, the type of states that result from
processing `msg` at time `ref` against `state`. An element of the type is an updated state that
satisfies all the constraints.

## State Management

Two examples of state management are presented.

How long is a flight held in the active store after it expires.

```lean
def expirePeriod := Duration.oneHour
```

Transform a state by moving expired active flights to the inactive store.

```lean
def Expire (ref : DTG) (pre : State) :=
  let threshold := -- Threshold below which active flights are expired.
                   ref - expirePeriod
  let expired := -- The active flights that have expired.
                 pre.active.filter (·.period.ends < threshold)
  { post : State // (∀ idh, idh ∈ post.active ↔ idh ∈  pre.active ∧ idh ∉ expired) ∧
                    (∀ idh, idh ∈ post.inactive ↔ idh ∈ pre.inactive ∨ idh ∈ expired ) ∧
                    post.failed = pre.failed }
```

How long is a data held in the state when it is no longer active.

```lean
def purgePeriod := Duration.oneDay
```

Transform a state by purging entries (inactive flights and failed messages) that have expired.

```lean
def Purge (ref : DTG) (pre : State) :=
  let threshold := -- Threshold below which inactive and failed flights are purged.
                   ref - purgePeriod
  { post : State // post.active = pre.active ∧
                    (∀ idh, idh ∈ post.inactive ↔ idh ∈ pre.inactive ∧ idh.1.period.ends > threshold) ∧
                    (∀ f, f ∈ post.failed ↔ f ∈ pre.failed ∧ f.msg.timestamp > threshold) }
```

## Flight Query

The final section specifies a simple querying function. Retrieve all active flights from the state
that match query parameters. Something very similar to this occurs in operation on a daily basis.

The query parameters are:

- aircraft identification;
- departure point;
- take off interval;
- destination point.

```lean
structure Query where
  acid : Option AircraftIdentification
  adep : Option Doc7910.Designator
  eobt : Option Interval
  ades : Option Doc7910.Designator
```

Any of the query fields may be omitted, in which case any value matches.

Does a flight match against a query?

```lean
def queryMatch (q : Query) (f : Flight) : Bool :=
  matchOpt q.acid f.f7.f7a ∧
  matchOpt q.adep f.f13.desigOf ∧
  matchEobt q.eobt f.f13.f13b ∧
  matchOpt q.ades f.f16.f16a
where -- If query specifies `none`, anything matches, otherwise exact match required.
      matchOpt {α : Type} [DecidableEq α] (q : Option α) (f : Option α) : Bool :=
        q.isNone ∨ q = f
      -- Matching on departure time.
      matchEobt : Option Interval → DTG → Bool
        | none, _     => True
        | some i, dtg => i.contains dtg
```

The active flights in the state that match a query.

```lean
def QueryMatch (state : State) (query : Query) :=
  { fs : List Flight // ∀ f, f ∈ fs ↔ f ∈ activeFlights state ∧ queryMatch query f }

end State
```
