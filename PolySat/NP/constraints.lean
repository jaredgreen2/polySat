import PolySat.NP.variadic
import PolySat.basic2
import Init.Data.List
--import Std.Data.List
import Init.Data.List.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Join
import Mathlib.Data.Bool.Basic
open Classical

--special constraints applicable to multiple problem types go here
variable {α : Type}[h : DecidableEq α]
def allConstraint (l : List (variadic α pred)) : List (List (Bool × normalizable α pred)) :=
  [l.map (fun x => (true, variadic.toNormalizable x))]

def oneConstraint (l : List (variadic α pred)) : List (List (Bool × normalizable α pred)) :=
  l.map (fun x => (true, variadic.toNormalizable x) :: (l.filter (fun y => y == x) ).map (fun y => (false,variadic.toNormalizable y)))

def neConstraint (l : {l : List (variadic α pred × variadic α pred) // l ≠ []}) : List (List (List (Bool × normalizable α pred))) :=
  variadic.normalize (variadic.vAnd (IList.ofList ⟨ l.1.map
  (fun x => variadic.vAnd (IList.ofList ⟨ [x.fst,x.snd],by simp⟩) ),by aesop⟩ ))
