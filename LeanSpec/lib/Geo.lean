/-
# Geospatial Definitions

This module contains basic geospatial definitions. Items are included only if needed
in support of the examples in the tutorial.
-/
import LeanSpec.lib.Util

namespace Geo

def Latitude := FloatMN (-90) 90

def Longitude := FloatMN (-180) 180

structure Point where
  latitude  : Latitude
  longitude : Longitude

inductive DirectionDatum
  | true
  | magnetic

structure Direction where
  datum : DirectionDatum
  value : FloatMN 0 360

end Geo