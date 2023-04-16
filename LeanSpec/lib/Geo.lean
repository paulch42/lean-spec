/-
# Geospatial Definitions

This module contains basic geospatial definitions. Items are included only if needed
in support of the examples in the tutorial.
-/
import LeanSpec.lib.Util

namespace Geo

def Latitude := FloatMN (-90) 90
deriving DecidableEq

def Longitude := FloatMN (-180) 180
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
  value : FloatMN 0 360
deriving DecidableEq

end Geo