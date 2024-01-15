# Geospatial Definitions

This module contains basic geospatial definitions. Items are included only if needed
in support of the examples in the tutorial.

```lean
import LeanSpec.lib.Util

namespace Geo

def degrees2Seconds (deg : Nat) : Nat :=
   deg * 60 * 60
```

Latitude in range -90..90 degrees, expresssed as a number of seconds.
+ve North, -ve South

```lean
def Latitude := IntMN (-(degrees2Seconds 90)) (degrees2Seconds 90)
deriving DecidableEq
```

Latitude in range -180..100 degrees, expresssed as a number of seconds.
+ve East, -ve West

```lean
def Longitude := IntMN (-(degrees2Seconds 180)) (degrees2Seconds 180)
deriving DecidableEq

structure Point where
  latitude  : Latitude
  longitude : Longitude
deriving DecidableEq

inductive DirectionDatum
  | true
  | magnetic
deriving DecidableEq

structure Direction where
  datum : DirectionDatum
  value : NatMN (degrees2Seconds 0) (degrees2Seconds 360)
deriving DecidableEq

end Geo
```
