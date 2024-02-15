import PolySat.NP.variadic
import PolySat.basic2
import Init.Data.List
import Std.Data.List
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Join
import Mathlib.Data.Bool.Basic
open Classical

--special constraints applicable to multiple problem types go here

def allConstraint (l : List (variadic α pred)) : List (List (Bool × normalizable α pred)) :=
  [l.map (fun x => (true, tonormalizable x))]

def oneConstraint (l : List (variadic α pred)) : List (List (Bool × normalizable α pred)) :=
  l.map (fun x => (true, toNormalizable x) :: (l.erase x).map (fun y => (false,tonormalizable y)))

def neConstraint (l : List (variadic α pred × variadic α pred)) : List (List (List (Bool × normalizable α pred))) :=
  normalize (vAnd [l.map (fun x => vAnd [x.fst,x.snd])])
