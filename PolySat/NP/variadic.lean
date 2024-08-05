import Init.Data.List
import Init.Prelude
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Join
import Mathlib.Data.Bool.Basic
import PolySat.basic2
import PolySat.IList
open Classical

--universe u
variable  {α : Type}[h : DecidableEq α]
inductive variadic (α :Type) [h : DecidableEq α]
(pred : α -> Prop)
  where
  | vatom : α -> (variadic α pred)
  | vAnd : IList (variadic α pred) -> variadic α pred
  | vOr : IList (variadic α pred) -> variadic α pred
  | vNot : variadic α pred -> variadic α pred
--deriving DecidableEq

namespace variadic

 def depth (v : variadic α pred) : Nat :=
  match v with
  | vatom _ => 1
  | vAnd l => (IList.fold l (fun x y => max (depth x) y) (fun y => depth y)) + 1
  | vOr l => (IList.fold l (fun x y => max (depth x) y) (fun y => depth y)) + 1
  | vNot a => depth a + 1

def toNormalizable (v : variadic α pred) : normalizable α pred :=
  match v with
  | vatom a => normalizable.atom a
  | vAnd (IList.single a) => toNormalizable a
  | vAnd (IList.cons a as) => normalizable.And (toNormalizable a) (toNormalizable (vAnd as))
  | vOr (IList.single a) => toNormalizable a
  | vOr (IList.cons a as) => normalizable.Or (toNormalizable a) (toNormalizable (vOr as))
  | vNot a => normalizable.Not (toNormalizable a)

def subnormalize (v : variadic α pred) : List (List (List (normalizable α pred))) :=
  match v with
  | vatom a => [[[normalizable.atom a],[normalizable.Not (normalizable.atom a)]]]
  | vAnd l => ([toNormalizable v]
  :: (l.map toNormalizable).toList.1
  :: (l.map (fun x => [normalizable.Not (toNormalizable v),normalizable.Not (toNormalizable v)])).toList.1)
  :: (l.map (fun x => subnormalize x )).toList.1.join
  | vOr l => ([normalizable.Not (toNormalizable v)]
  :: (l.map (fun x => normalizable.Not (toNormalizable x))).toList.1
  :: (l.map (fun x => [toNormalizable v, toNormalizable x])).toList.1)
  :: (l.map (fun x => subnormalize x )).toList.1.join
  | vNot x => [[toNormalizable v,normalizable.Not (toNormalizable x)],[normalizable.Not (toNormalizable v), toNormalizable x]]
  :: (subnormalize x )
  termination_by depth v


def normalize (v : variadic α pred) : List (List (List (Bool × normalizable α pred))) :=
  normalizable.booleanize ([[toNormalizable v]] :: (subnormalize v))

def satisfiable? (v : variadic α pred) : Bool :=
  normalizable.lsatisfiable? (normalize v)

def solutions (v : variadic α pred) : List (List (List (Bool × normalizable α pred))) :=
  normalizable.clean (normalize v) (normalizable.order (normalize v))

def solution (v : variadic α pred) : List (Bool × normalizable α pred) :=
  (normalizable.getS (normalizable.chose (solutions v))).filter (fun a => normalizable.isAtom a.snd)
