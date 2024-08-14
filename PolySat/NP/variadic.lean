import Init.Data.List
import Init.Prelude
import Init.Data.List.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Join
import Mathlib.Data.Bool.Basic
import PolySat.basic2
import PolySat.IList
import Aesop
open Classical

--universe u
variable  {α : Type}[h : DecidableEq α]
inductive variadic (α :Type) [h : DecidableEq α](pred : α -> Prop)
  where
  | vatom : α -> (variadic α pred)
  | vAnd : IList (variadic α pred) -> variadic α pred
  | vOr : IList (variadic α pred) -> variadic α pred
  | vNot : variadic α pred -> variadic α pred
deriving DecidableEq

namespace variadic


mutual
def ilist_depth  : IList (variadic α pred) -> Nat
  | .single a => variadic_depth a
  | .cons a as => max (variadic_depth a) (ilist_depth as)

@[simp]
def variadic_depth : variadic α pred → Nat
  | .vatom _ => 1
  | .vAnd l => ilist_depth l + 1
  | .vOr l => ilist_depth l + 1
  | .vNot v => variadic_depth v + 1

end

theorem depth_le_elem : ∀ l : IList (variadic α pred), ∀ x ∈ l.toList.1,
    variadic_depth x ≤ ilist_depth l := by
  intro l
  induction l with
    | single a =>
      intro x
      rw [IList.toList,ilist_depth]
      simp only [List.mem_singleton]
      rintro rfl
      exact Nat.le_refl x.variadic_depth
    | cons a l hind =>
      intro x
      rw [IList.toList,ilist_depth]
      simp only [List.mem_cons]
      rintro (rfl|r)
      · exact Nat.le_max_left x.variadic_depth (ilist_depth l)
      · exact hind x r |>.trans  <| Nat.le_max_right a.variadic_depth (ilist_depth l)

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
  :: (l.map (fun _ => [normalizable.Not (toNormalizable v),normalizable.Not (toNormalizable v)])).toList.1)
  :: (l.toList.1.attach.map (fun x => subnormalize x.1 )).join
  | vOr l => ([normalizable.Not (toNormalizable v)]
  :: (l.map (fun x => normalizable.Not (toNormalizable x))).toList.1
  :: (l.map (fun x => [toNormalizable v, toNormalizable x])).toList.1)
  :: (l.toList.1.attach.map (fun x => subnormalize x.1 )).join
  | vNot x => [[toNormalizable v,normalizable.Not (toNormalizable x)],[normalizable.Not (toNormalizable v), toNormalizable x]]
  :: (subnormalize x )
  termination_by variadic_depth v
  decreasing_by
  simp_wf
  calc
    x.1.variadic_depth ≤ ilist_depth l := depth_le_elem l x.1 x.2
    _ < ilist_depth l + 1              := Nat.lt_add_one (ilist_depth l)
  simp_wf
  calc
    x.1.variadic_depth ≤ ilist_depth l := depth_le_elem l x.1 x.2
    _ < ilist_depth l + 1              := Nat.lt_add_one (ilist_depth l)
  simp_wf

def normalize (v : variadic α pred) : List (List (List (Bool × normalizable α pred))) :=
  normalizable.booleanize ([[toNormalizable v]] :: (subnormalize v))

def satisfiable? (v : variadic α pred) : Bool :=
  normalizable.lsatisfiable? (normalize v)

def solutions (v : variadic α pred) : List (List (List (Bool × normalizable α pred))) :=
  normalizable.clean (normalize v) (normalizable.order (normalize v))

def solution (v : variadic α pred) : List (Bool × normalizable α pred) :=
  (normalizable.getS (normalizable.chose (solutions v))).filter (fun a => normalizable.isAtom a.snd)
