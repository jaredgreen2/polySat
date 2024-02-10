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

universe u

inductive normalizable (α : Type u) [DecidableEq α] (pred : α -> Prop)
  where
  | atom : α -> (normalizable α pred)
  | And : List (normalizable α pred) -> normalizable α pred
  | Or : List (normalizable α pred) -> normalizable α pred
  | Not : normalizable α pred -> normalizable α pred

namespace normalizable

mutual

def decEqListNormalizable : DecidableEq (List (normalizable α pred)) := fun
  | [],[] => .isTrue rfl
  | hd₁::tl₁, hd₂::tl₂ =>
      let inst₁ := decEqNormalizable hd₁ hd₂
      let inst₂ := decEqListNormalizable tl₁ tl₂
      if h₁ : hd₁ = hd₂ then
          if h₂ : tl₁ = tl₂ then .isTrue (by subst h₁ h₂; rfl)
          else .isFalse (by intro n; injection n; apply h₂; assumption)
      else
        .isFalse (by intro n; injection n; apply h₁; assumption)
  | [],_::_ | _::_,[] => .isFalse (by intro h; injection h)


def decEqNormalizable : DecidableEq (normalizable α pred) := fun
  | atom a, atom b =>
    if h : a = b then
      .isTrue (by subst h; rfl)
    else
      .isFalse  (by intro n; injection n; apply h; assumption)
  | And a, And b | Or a, Or b =>
    let inst := decEqListNormalizable a b
    if h : a = b then
      .isTrue (by subst h; rfl)
    else
      .isFalse  (by intro n; injection n; apply h; assumption)
  | Not a, Not b =>
    let inst := decEqNormalizable a b
    if h : a = b then
      .isTrue (by subst h; rfl)
    else
      .isFalse  (by intro n; injection n; apply h; assumption)
  | Not _, Or _  |Not _, And _ | Not _, atom _
  | Or _, Not _  | Or _, And _ | Or _, atom _
  | And _, Not _ | And _, Or _ | And _, atom _
  | atom _, Not _| atom _, And _| atom _, Or _ =>
    .isFalse (by intro h; injection h)

end

def toProp (n : normalizable α pred) : Prop :=
  match n with
  | atom a => pred a
  | And l => (l.attach.map (fun x => toProp x.val)).foldr (· ∧ ·) True
  | Or l => (l.attach.map (fun x => toProp x.val)).foldr (· ∨ ·) False
  | Not n => ¬(toProp n)
termination_by n
  decreasing_by
  all_goals
    simp_wf
    try have := Subtype.property ‹_›
  decreasing_trivial
  simp_wf
  decreasing_trivial

def subnormalizeN (n : normalizable α pred) [DecidableEq (normalizable α pred)] : List (normalizable α pred) :=
  match n with
  | Or l => ((Or (And (Not n :: (l.attach.map fun x => Not x.val))
    :: (l.map (fun x => And [n,x]) )))
    :: ((l.attach.map fun ⟨x,_⟩ => subnormalizeN x).foldr (fun x y => (x.append y).dedup) []))
  | And l => ((Or (And (n :: l)
    :: (l.attach.map (fun x => And [Not n, Not x]))))
    :: ((l.attach.map fun ⟨x,_⟩ => subnormalizeN x).foldr (fun x y => (x.append y).dedup) []))
  | Not i => (Or [And [n, Not i], And [Not n, i]]) :: (subnormalizeN i)
  | atom a => [Or [And [n], And [Not n]]]
termination_by n
  decreasing_by
  all_goals
    simp_wf
    --try have Subtype.property
    decreasing_trivial
  try have Subtype.property
  simp_wf
  sorry

def normalizeN (n : normalizable α pred) : normalizable α pred :=
  And ((Or [And [n]]) :: subnormalizeN n)
  --termination_by

def normalizeP (n : normalizable α pred) : Prop :=
  toProp (normalizeN n)

theorem normalization : ∀ n : normalizable α pred, toProp n <-> normalizeP n :=
  by
  sorry

def nStrip (n : normalizable α pred) : Bool × normalizable α pred :=
  match n with
  | Not (Not i) => nStrip i
  | Not i => (false, i)
  | i => (true, i)

def strip (n : normalizable α pred) : List (Bool × normalizable α pred) :=
  match n with
  | atom _ => [(true,n)]
  | Or l => l.map nStrip
  | And l => l.map nStrip
  | i => [nStrip i]

def normalizel (n : normalizable α pred) : List (List (List (Bool × normalizable α pred))) :=
  ((strip (normalizeN n)).map
  (fun x => strip x.snd)).map
  (fun x => x.map
  (fun y => strip y.snd))

def nToProp (n : List (List (List (Bool × normalizable α pred)))) : Prop :=
  toProp (And (n.map
  (fun x => Or (x.map
  (fun y => And (y.map
  (fun z => if z.fst
    then z.snd
    else Not z.snd)))))))

def gToProp (g : List (List (Bool × normalizable α pred))) : Prop :=
  toProp (Or (g.map
  (fun x => And (x.map
  (fun y => if y.fst
    then y.snd
    else Not y.snd)))))

def sToProp (s : List (Bool × normalizable α pred)) : Prop :=
  toProp (And (s.map
  (fun x => if x.fst
    then x.snd
    else Not x.snd)))

def wToProp (w : Bool × normalizable α pred) : Prop :=
  toProp (if w.fst
    then w.snd
    else Not w.snd)

def coherent (n : List (List (List (Bool × normalizable α pred)))) : Prop :=
  ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
  ∀ s : List (Bool × normalizable α pred), s ∈ g ->
  (∀ w : Bool × normalizable α pred,∀ x : Bool × normalizable α pred, w ∈ s ∧ x ∈ s ->
  w.snd == x.snd -> w.fst == x.fst) ∧ s.Nodup

def makeCoherent (n : List (List (List (Bool × normalizable α pred)))) [DecidableEq (normalizable α pred)]: List (List (List (Bool × normalizable α pred))) :=
  n.map
  (fun x => (x.filter
  (fun y => y.Pairwise
  (fun a b => a.snd == b.snd -> a.fst == b.fst))).map
  (fun y => y.dedup))

theorem coherency : ∀ n : List (List (List (Bool × normalizable α pred))), coherent (makeCoherent n) :=
  by
  sorry

theorem normal : ∀ n : normalizable α pred, nToProp (makeCoherent (normalizel n)) <-> normalizeP n :=
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

def compatible (s : List (Bool × normalizable α pred)) (t : List (Bool × normalizable α pred)) : Prop :=
  ∀ x y: Bool × normalizable α pred, x ∈ s ∧ y ∈ t -> x.snd == y.snd -> x.fst == y.fst

theorem rule1 : ∀ n : List (List (List (Bool × normalizable α pred))),
                ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                ∀ v : Bool × normalizable α pred, ¬(v ∈ s) ->
                (∃ h : List (List (Bool × normalizable α pred)), h ∈ n ->
                ∀ t : List (Bool × normalizable α pred), t ∈ h ->
                compatible t s -> v ∈ t) ->
                nToProp n -> sToProp s -> wToProp v :=
  by
  sorry

theorem rule2 : ∀ n : List (List (List (Bool × normalizable α pred))),
                ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                (∃ h : List (List (Bool × normalizable α pred)), h ∈ n ∧
                ∀ t : List (Bool × normalizable α pred), t ∈ h ∧
                ¬(compatible s t)) ->
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
             (compatible t u) -> w ∈ u :=
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
             ¬(compatible a t) :=
  by
  sorry

def order (n : List (List (List (Bool × normalizable α pred)))) [DecidableEq α] : Nat :=
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

def clean (r : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  let s := makeCoherent r;
  let f := (s.map
  (fun t => s.foldl
  (fun p q => (p.filter
  (fun u => q.any
  (fun v => compatible v u))).map
  (fun w => w.append
  ((interl (q.filter
  (fun v => compatible v w))).filter
  (fun x => ¬(x ∈ w))))) t));
  if [] ∈ s ∨ order f >= order s then s else clean f

def solutions (o : normalizable α pred) : List (List (List (Bool × normalizable α pred))) :=
  clean (normalizel o)

def satisfiable? (o : normalizable α pred) : Bool :=
  ¬ ([] ∈ solutions o)

def chose (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  match n with
  | [] => []
  | [[]] => []
  | ([] :: as) => []
  | (b :: _) :: as => let s := clean ([b] :: as); if [] ∈ s then [] else ([b] :: chose s.tail)

def getS (o : List (List (List (Bool × normalizable α pred)))) : List (Bool × normalizable α pred) :=
  match o with
  | [] => []
  | [] :: _ => []
  | (b :: _) :: bs => (b.append (getS bs)).dedup

def solveWhole (o : normalizable α pred) : List (Bool × normalizable α pred) :=
  getS (chose (solutions o))

theorem solveSound : ∀ n : normalizable α pred, satisfiable? n == false -> ¬ toProp n :=
  by
  sorry

def atoms (n : normalizable α pred) : List (normalizable α pred) :=
  match n with
  | atom a => [atom a]
  | Or l => ((l.map atoms).join).dedup
  | And l => ((l.map atoms).join).dedup
  | Not i => atoms i

def solveAtoms (o : normalizable α pred) : List (Bool × normalizable α pred) :=
   (solveWhole o).filter (fun a => a.snd ∈ atoms o)

theorem solveComplete : ∀ n : normalizable α pred, satisfiable? n == true ->
                        ∃ s : List (Bool × normalizable α pred), List.Subset (s.map snd) (atoms n) ∧
                        sToProp s -> toProp n :=
  by
  intro n
  intro
  use (solveAtoms n)
  --take it from here
  sorry
