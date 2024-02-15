import Init.Data.List
import Std.Data.List
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Join
import Mathlib.Data.Bool.Basic
import PolySat.basic2
open Classical

variable {α : Type}[h : DecidableEq α]
inductive variadic α (pred : α -> Prop)
  where
  | vatom : α => (variadic α pred)
  | vAnd : List (variadic α pred) -> variadic α pred
  | vOr : List (variadic α pred) -> variadic α pred
  | vNot : variadic α pred -> variadic α pred

partial def toNormalizable (v : variadic α pred) -> normalizable α pred :=
  match v with
  | vatom a => atom a
  | vAnd [a] => toNormalizable a
  | vAnd (a :: as) => And (toNormalizable a) (toNormalizable (vAnd as))
  | vOr [a] => toNormalizable a
  | vOr (a :: as) => Or (toNormalizable a) (toNormalizable (vOr as))
  | vNot a => Not (toNormalizable a)

def subnormalize (v : variadic α pred) : List (List (List (normalizable α pred))) :=
  match v with
  | vAnd l => ((toNormalizable v
  :: l.map toNormalizable)
  :: (l.map (fun x => [Not (toNormalizable v),Not (toNormalizable v)])))
  :: (l.map subnormalize).Join
  | vOr l => ((Not (toNormalizable v)
  :: l.map (fun x => Not toNormalizable x))
  :: (l.map (fun x => [toNormalizable v, toNormalizable x])))
  :: (l.map subnormalize).Join
  | vNot a => [[toNormalizable v,Not (toNormalizable a)],[Not (toNormalizable v, toNormalizable a)]]
  :: (subnormalize a)
  | vatom a => [[[atom a],[Not (atom a)]]]

def normalize (v : variadic α pred) : List (List (List (Bool × normalizable α pred))) :=
  booleanize ([[toNormalizable v]] :: (subnormalize v))

def satisfiable? (v : variadic α pred) : Bool :=
  lsatisfiable? (normalize v)

def solutions (v : variadic α pred) : List (List (List (Bool × normalizable α pred))) :=
  lsolutions (normalize v)

def solution (v : variadic α pred) : List (Bool × normalizable α pred) :=
  lsolveatoms (normalize v)
