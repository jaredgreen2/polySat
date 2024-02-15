import Init.Data.List
import Std.Data.List
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Join
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.Bool.Basic
open Classical

--basic rewritten to not build on variadic gates. apparently taking a list messes up structural recursion.

variable {α : Type}[h : DecidableEq α]
inductive normalizable α (pred : α -> Prop)
  where
  | atom : α -> (normalizable α pred)
  | And : (normalizable α pred) -> (normalizable α pred) -> normalizable α pred
  | Or : (normalizable α pred) -> (normalizable α pred) -> normalizable α pred
  | Not : normalizable α pred -> normalizable α pred
deriving DecidableEq

namespace normalizable

--need decidable equality of normalizable. it doesn't impact the theorems, but if the code is to run, we need it.

def toProp (n : normalizable α pred) : Prop :=
  match n with
  | atom a => pred a
  | And a b =>  toProp a ∧ toProp b
  | Or a b => (toProp a) ∨ toProp b
  | Not i => ¬(toProp i)

--no, these functions absolutely should not be expecting types
def subnormalize (n : (normalizable α pred)) : List (List (List (normalizable α pred))) :=
  match n with
  | Or a b => [[a,n],[b,n],[Not a,Not b, Not n]] :: (List.append (subnormalize a) (subnormalize b))
  | And a b => [[a,b,n],[Not a,Not n],[Not b,Not n]] :: (List.append (subnormalize a) (subnormalize b))
  | Not i => [[n,Not i],[Not n, i]] :: (subnormalize i)
  | atom _ => [[[n],[Not n]]]

def normalize :  normalizable α pred -> List (List (List (normalizable α pred))) := fun o =>
  [[o]] :: (subnormalize o)

def nStrip (n : normalizable α pred) : Bool × normalizable α pred :=
  match n with
  | Not (Not i) => nStrip i
  | Not i => (false,i)
  |i => (true,i)

def booleanize (n : List (List (List (normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  n.map (fun x => x.map (fun y => y.map (fun z => nStrip z)))

def normalizel (n : normalizable α pred) : List (List (List (Bool × normalizable α pred))) :=
  booleanize (normalize n)

def wToProp (w : Bool × normalizable α pred) : Prop :=
  if w.fst then toProp w.snd else ¬(toProp w.snd)

def sToProp (s : List (Bool × normalizable α pred)) : Prop :=
  s.all (fun x => wToProp x)

def gToProp (g : List (List (Bool × normalizable α pred))) : Prop :=
  g.any (fun x => sToProp x)

def nToProp (n : List (List (List (Bool × normalizable α pred)))) : Prop :=
  n.all (fun x => gToProp x)

theorem normal : ∀ n : normalizable α pred, toProp n <-> nToProp (normalizel n) :=
  by
  sorry

def coherent (n : List (List (List (Bool × normalizable α pred)))) : Prop :=
  ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
  ∀ s : List (Bool × normalizable α pred), s ∈ g ->
  (∀ w : Bool × normalizable α pred,∀ x : Bool × normalizable α pred, w ∈ s ∧ x ∈ s ->
  w.snd == x.snd -> w.fst == x.fst) ∧ s.Nodup

def makeCoherent (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  n.map
  (fun x => (x.filter
  (fun y => y.Pairwise
  (fun a b => a.snd == b.snd -> a.fst == b.fst))).map
  (fun y => y.dedup))

theorem coherency : ∀ n : List (List (List (Bool × normalizable α pred))), coherent (makeCoherent n) :=
  by
  sorry

def nfNegate (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  n.map
  (fun x => x.map
  (fun y => y.map
  (fun z => (!z.fst, z.snd))))

theorem interesting : ∀ n : normalizable α pred, ¬(toProp n) <-> nToProp (nfNegate (normalizel n)) :=
  by
  sorry


theorem property1 : ∀ n : List (List (List (Bool × normalizable α pred))),
                    ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                    ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                    ∀ i : Bool × normalizable α pred, (nToProp n -> sToProp s -> wToProp i) ->
                    (nToProp n -> (sToProp s <-> sToProp (s.concat i))) :=
  by
  sorry

theorem property2 : ∀ n : List (List (List (Bool × normalizable α pred))),
                    ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                    ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                    ((nToProp n -> ¬(sToProp s)) -> nToProp n -> (gToProp g <-> gToProp (g.erase s))) :=
  by
  sorry

def bcompatible (s : List (Bool × normalizable α pred)) (t : List (Bool × normalizable α pred)) : Bool :=
  s.all (fun x => t.all (fun y =>  x.snd == y.snd -> x.fst == y.fst))

theorem rule1 : ∀ n : List (List (List (Bool × normalizable α pred))),
                ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                ∀ v : Bool × normalizable α pred, ¬(v ∈ s) ->
                (∃ h : List (List (Bool × normalizable α pred)), h ∈ n ->
                ∀ t : List (Bool × normalizable α pred), t ∈ h ->
                bcompatible t s -> v ∈ t) ->
                nToProp n -> sToProp s -> wToProp v :=
  by
  sorry

theorem rule2 : ∀ n : List (List (List (Bool × normalizable α pred))),
                ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                (∃ h : List (List (Bool × normalizable α pred)), h ∈ n ∧
                ∀ t : List (Bool × normalizable α pred), t ∈ h ∧
                ¬(bcompatible s t)) ->
                nToProp n -> ¬(sToProp s) :=
  by
  sorry

theorem rule3 : ∀ n : List (List (List (Bool × normalizable α pred))), [] ∈ n -> ¬(nToProp n) :=
  by
  sorry

theorem c1 : ∀ n : List (List (List (Bool × normalizable α pred))),
             ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
             ∀ s : List (Bool × normalizable α pred), s ∈ g ->
             ∀ w : Bool × normalizable α pred, ¬(w ∈ s) ->
             (nToProp n -> (sToProp s -> wToProp w)) ->
             ∃ t : List (Bool × normalizable α pred),
             (List.Subset s t) ∧ ¬(w ∈ t) ∧
             (nToProp n -> (sToProp s <-> sToProp t)) ∧
             ∃ h i : List (List (Bool × normalizable α pred)),
             h ∈ n ∧ (nToProp n -> (gToProp h <-> gToProp i)) ∧
             ∀ u : List (Bool × normalizable α pred), u ∈ i ->
             (bcompatible t u) -> w ∈ u :=
  by
  sorry

theorem c2 : ∀ n : List (List (List (Bool × normalizable α pred))),
             ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
             ∀ s : List (Bool × normalizable α pred), s ∈ g ->
             ∃ a : List (Bool × normalizable α pred),
             (List.Subset s a) ∧ (nToProp n -> (sToProp s <-> sToProp a)) ∧
             ∃ h i : List (List (Bool × normalizable α pred)),h ∈ n ∧
             (nToProp n -> (gToProp h <-> gToProp i)) ∧
             ∀ t : List (Bool × normalizable α pred), t ∈ i ->
             ¬(bcompatible a t) :=
  by
  sorry

def order (n : List (List (List (Bool × normalizable α pred))))  : Nat :=
  let count : Nat := Nat.succ (((n.map
  (fun g => (g.map
  (fun s => s.map
  (fun w => w.snd))).join)).join).dedup).length;
  (n.map
  (fun g => (g.map
  (fun s => count - (List.length s))).sum)).sum

def interl (l : List (List a)) [DecidableEq a] : List a :=
  match l with
  | [] => []
  | [a] => a
  | (a :: as) => List.inter a (interl as)

--all the messages after this are due to the lack of termination proof here. once one is here they will go away
def clean (r : List (List (List (Bool × normalizable α pred)))) (n : Nat) : List (List (List (Bool × normalizable α pred))) :=
  let s := makeCoherent r;
  match n with
  | 0 => s
  | Nat.succ a => let f := (if [] ∈ s then s else
    s.map
  (fun t => s.foldl
  (fun p q => (p.filter
  (fun u => q.any
  (fun v => bcompatible v u))).map
  (fun w => w.append
  ((interl (q.filter
  (fun v => bcompatible v w))).filter
  (fun x => ¬(x ∈ w))))) t));
  if  order f >= order s then s else clean f a
  termination_by n
  decreasing_by
  simp_wf

theorem leneqclean : ∀ n : List (List (List (Bool × normalizable α pred))), (clean n (order n)).length = n.length :=
  by
  sorry

def solutions (o : normalizable α pred) : List (List (List (Bool × normalizable α pred))) :=
  clean (normalizel o) (order (normalizel o))

def satisfiable? (o : normalizable α pred)  : Bool :=
  [] ∉ solutions o

def lsatisfiable? (n : List (List (List (Bool × normalizable α pred)))) : Bool :=
  [] ∉ clean n (order n)

def chose (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  match n with
  | [] => []
  | [[]] => []
  | ([] :: as) => []
  | (b :: _) :: as => let s := clean ([b] :: as) (order ([b] :: as)); if [] ∉ s then ([b] :: chose s.tail)  else []
  termination_by sizeOf n
  decreasing_by
  simp_wf
  sorry

def getS (o : List (List (List (Bool × normalizable α pred)))) : List (Bool × normalizable α pred) :=
  match o with
  | [] => []
  | [] :: _ => []
  | (b :: _) :: bs => (b.append (getS bs)).dedup

def solveWhole (o : normalizable α pred) : List (Bool × normalizable α pred) :=
  getS (chose (solutions o))

def lsolvewhole (n : List (List (List (Bool × normalizable α pred)))) : List (Bool × normalizable α pred) :=
  getS (chose (clean n (order n)))

theorem solveSound : ∀ n : normalizable α pred, satisfiable? n == false -> ¬ toProp n :=
  by
  sorry

theorem lsolvesound : ∀ n : List (List (List (Bool × normalizable α pred))), lsatisfiable? n == false -> ¬(nToProp n) :=
  by
  sorry

def atoms (n : normalizable α pred) : List (normalizable α pred) :=
  match n with
  | atom a => [atom a]
  | Or a b => (List.append (atoms a) (atoms b)).dedup
  | And a b => (List.append (atoms a) (atoms b)).dedup
  | Not i => atoms i

def isAtom (n : normalizable α pred) : Bool :=
  match n with
  |atom _ => true
  | _ => false

def solveAtoms (o : normalizable α pred)  : List (Bool × normalizable α pred) :=
   (solveWhole o).filter (fun a => isAtom a.snd)

def lsolveatoms (n : List (List (List (Bool × normalizable α pred)))) : List (Bool × normalizable α pred) :=
  let s := (lsolvewhole n);
  s.filter (fun a : Bool × normalizable α pred => isAtom a.snd)

theorem solveComplete : ∀ n : normalizable α pred, satisfiable? n == true ->
                        ∃ s : List (Bool × normalizable α pred), List.Subset (s.map snd) (atoms n) ∧ (s ≠ []) ∧
                        sToProp s -> toProp n :=
  by
  intro n
  intro
  use (solveAtoms n)
  --take it from here
  sorry

--same thing here
def lsolvecomplete : ∀ n : List (List (List (Bool × normalizable α pred))), lsatisfiable? n == true ->
                     ∃ s : List (Bool × normalizable α pred),
                     (∀ w: Bool × normalizable α pred, w ∈ s -> isAtom w.snd)  ∧ (s ≠ []) ∧
                     sToProp s -> nToProp n :=
  by
  sorry

def nextSolution (s : List (Bool × normalizable α pred)) (n : List (List (List (Bool × normalizable α pred))))
                   : (List (Bool × normalizable α pred)  ×    List (List (List (Bool × normalizable α pred)))) :=
  let m := (s.map (fun x => [(!x.fst,x.snd)])) :: n;
  ((lsolveatoms (m)),m)
