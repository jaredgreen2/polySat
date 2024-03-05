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
import Mathlib.Logic.Basic
open Classical

variable {α : Type}[h : DecidableEq α]
inductive normalizable α (pred : α -> Prop)
  where
  | atom : α -> (normalizable α pred)
  | And : (normalizable α pred) -> (normalizable α pred) -> normalizable α pred
  | Or : (normalizable α pred) -> (normalizable α pred) -> normalizable α pred
  | Not : normalizable α pred -> normalizable α pred
deriving DecidableEq

namespace normalizable

@[reducible]
def toProp (n : normalizable α pred) : Prop :=
  match n with
  | atom a => pred a
  | And a b =>  toProp a ∧ toProp b
  | Or a b => (toProp a) ∨ toProp b
  | Not i => ¬(toProp i)

@[simp]
theorem toProp_not : toProp (Not n₁) ↔ ¬ toProp n₁ := Iff.rfl

@[simp]
theorem toProp_and : toProp (And n₁ n₂) ↔ toProp n₁ ∧ toProp n₂ := Iff.rfl

@[simp]
theorem toProp_or : toProp (Or n₁ n₂) ↔ toProp n₁ ∨ toProp n₂ := Iff.rfl

@[simp]
theorem toProp_atom {a : α} : toProp (atom a : normalizable α pred) ↔ pred a := Iff.rfl

def subnormalize (n : (normalizable α pred)) : List (List (List (normalizable α pred))) :=
  match n with
  | Or a b => [[a,n],[b,n],[Not a,Not b, Not n]] :: (List.append (subnormalize a) (subnormalize b))
  | And a b => [[a,b,n],[Not a,Not n],[Not b,Not n]] :: (List.append (subnormalize a) (subnormalize b))
  | Not i => [[n,Not i],[Not n, i]] :: (subnormalize i)
  | atom _ => [[[n],[Not n]]]

def normalize :  normalizable α pred -> List (List (List (normalizable α pred))) := fun o =>
  [[o]] :: (subnormalize o)

@[reducible]
def nStrip (n : normalizable α pred) : Bool × normalizable α pred :=
  match n with
  | Not i => (false,i)
  | i => (true,i)


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

def fToProp (n : List (List (List (normalizable α pred)))) : Prop :=
  n.all (fun x => x.any (fun y => y.all (fun z => toProp z)))

theorem nStrip_equiv : ∀ n : normalizable α pred, toProp n <-> wToProp (nStrip n) :=
  by
  intro n
  unfold nStrip
  induction n
  simp
  unfold wToProp
  simp
  simp
  unfold wToProp
  simp
  unfold wToProp
  simp
  simp
  unfold wToProp
  simp

theorem booleanize_eqiv : ∀ n : List (List (List (normalizable α pred))), fToProp n <-> nToProp (booleanize n) :=
  by
  intro n
  unfold nToProp
  simp
  unfold fToProp
  simp
  unfold booleanize
  simp
  unfold gToProp
  simp
  unfold sToProp
  simp
  simp [nStrip_equiv]

theorem w_neg :∀ a : Bool × normalizable α pred, wToProp (!a.1,a.2) <-> ¬ (wToProp a) :=
  by
  intro a
  cases Classical.em (a.fst = true)
  unfold wToProp
  simp
  rw [if_neg]
  apply Iff.not
  rw [if_pos]
  assumption
  simp
  assumption
  unfold wToProp
  simp
  rw [if_pos]
  rw [if_neg]
  rw [Classical.not_not]
  assumption
  rw [Bool.eq_false_iff]
  assumption

theorem andGateTaut :  (a ∧ b ∧ (a ∧ b)) ∨ (¬ a ∧ ¬(a ∧ b)) ∨ (¬ b ∧ ¬(a ∧ b)) :=
  by
  cases Classical.em a
  cases Classical.em b
  left
  constructor
  assumption
  constructor
  assumption
  constructor
  assumption
  assumption
  right
  right
  constructor
  assumption
  push_neg
  intro
  assumption
  right
  left
  constructor
  assumption
  rw [and_comm]
  push_neg
  intro
  assumption

theorem orGateTaut : (a ∧ (a ∨ b)) ∨ (b ∧ (a ∨ b)) ∨ ((¬ a) ∧ (¬b) ∧ ¬(a ∨ b)) :=
  by
  cases Classical.em a
  left
  constructor
  assumption
  left
  assumption
  right
  cases Classical.em b
  left
  constructor
  assumption
  right
  assumption
  right
  constructor
  assumption
  constructor
  assumption
  push_neg
  constructor
  assumption
  assumption

theorem all_and : List.all ( a ++ b) c <-> List.all a c ∧ List.all b c :=
  by
  simp
  constructor
  intro ha
  constructor
  intro b
  intro hb
  apply ha
  left
  exact hb
  intro c
  intro hc
  apply ha
  right
  exact hc
  intro ha
  intro b
  intro hb
  cases hb
  apply ha.left
  assumption
  apply ha.right
  assumption

theorem any_erase :∀ l : List b,∀ a: b -> Prop,
                     ∀ s : b,s ∈ l -> ¬ (a s) -> (List.any l a <-> List.any (List.erase l s) a) :=
  by
  intro l
  intro a
  intro s
  intro hs
  intro hnas
  induction' l with c d e
  simp
  constructor
  simp at hs
  cases' (Classical.em (c = s)) with hsc hsd
  have hed : List.erase (c :: d) s = d :=
  by {
    unfold List.erase
    rw [hsc]
    simp
  }
  rw [hed]
  simp
  rw [hsc]
  intro hsd
  cases' hsd with hsdl hsdr
  by_contra
  apply hnas
  exact hsdl
  exact hsdr
  cases' hs with hsl hsr
  by_contra
  apply hsd
  rw [hsl]
  simp only [Bool.or_eq_true, List.any_eq_true]
  simp at e
  intro hl
  apply e at hsr
  have hcd : List.erase (c :: d) s = c :: List.erase d s :=
  by {
    nth_rewrite 1 [ List.erase]
    rw [← ne_eq] at hsd
    apply beq_false_of_ne at hsd
    rw [hsd]
  }
  rw [hcd]
  simp
  simp at hl
  rw [← hsr]
  exact hl
  simp at hs
  cases' (Classical.em (c = s)) with hsl hsr
  have hed : List.erase (c :: d) s = d :=
  by{
    unfold List.erase
    rw [hsl]
    simp
  }
  rw [hed]
  simp
  rw [ hsl]
  intro f
  intro hf
  intro haf
  right
  use f
  have hcd : List.erase (c :: d) s = c :: List.erase d s :=
  by{
    nth_rewrite 1 [List.erase]
    rw [← ne_eq]at hsr
    apply beq_false_of_ne at hsr
    rw [hsr]
  }
  rw [hcd]
  rw [List.any_cons]
  cases' hs with hsc hsd
  by_contra
  apply hsr
  rw [hsc]
  apply e at hsd
  rw [List.any_cons]
  simp only [Bool.or_eq_true, List.any_eq_true]
  intro hcl
  simp at hsd
  simp
  rw [hsd]
  simp at hcl
  exact hcl

@[ext]
theorem beq_ext {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    (h : ∀ x y, @BEq.beq _ inst1 x y = @BEq.beq _ inst2 x y) :
    inst1 = inst2 := by
  have ⟨beq1⟩ := inst1
  have ⟨beq2⟩ := inst2
  congr
  ext x y
  exact h x y

theorem lawful_beq_subsingleton {α : Type*} (inst1 : BEq α) (inst2 : BEq α)
    [@LawfulBEq α inst1] [@LawfulBEq α inst2] :
    inst1 = inst2 := by
  ext x y
  simp only [beq_eq_decide]


theorem subnormal : ∀ n : normalizable α pred, fToProp (subnormalize n) :=
  by
  intro n
  induction' n with a b c d e f g i j k l
  unfold subnormalize
  unfold fToProp
  simp
  unfold toProp
  apply Classical.em
  unfold subnormalize
  simp
  unfold fToProp
  rw [List.all_cons]
  simp only [List.any_cons, List.all_cons, List.all_nil, Bool.and_true, List.any_nil,
    Bool.or_false, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_append, List.any_eq_true,toProp_not,toProp_and]
  constructor
  rw [toProp_not]
  rw [toProp_and]
  exact andGateTaut
  rw [all_and]
  constructor
  assumption
  assumption
  unfold fToProp
  unfold subnormalize
  rw [List.all_cons]
  simp only [List.any_cons, List.all_cons, toProp_or, List.all_nil, Bool.and_true, toProp_not,
    List.any_nil, Bool.or_false, List.append_eq, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.mem_append, List.any_eq_true]
  constructor
  rw [toProp_not]
  rw [toProp_or]
  exact orGateTaut
  rw [all_and]
  constructor
  assumption
  assumption
  unfold fToProp
  unfold subnormalize
  rw [List.all_cons]
  simp only [List.any_cons, List.all_cons, toProp_not, List.all_nil, Bool.and_true, Bool.and_self,
    not_not, List.any_nil, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
     List.any_eq_true]
  constructor
  cases Classical.em (toProp k)
  right
  assumption
  left
  assumption
  unfold fToProp at l
  exact l

theorem normal : ∀ n : normalizable α pred, toProp n <-> nToProp (normalizel n) :=
  by
  intro n
  unfold normalizel
  unfold normalize
  rw [← booleanize_eqiv]
  unfold fToProp
  simp only [List.all_cons, List.any_cons, List.all_nil, Bool.and_true, List.any_nil, Bool.or_false,
    Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, iff_self_and]
  intro
  apply subnormal

def coherent (n : List (List (List (Bool × normalizable α pred)))) : Prop :=
  ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
  ∀ s : List (Bool × normalizable α pred), s ∈ g ->
  (∀ w : Bool × normalizable α pred,∀ x : Bool × normalizable α pred, w ∈ s ∧ x ∈ s ->
  w.snd == x.snd -> w.fst == x.fst) ∧ s.Nodup

def makeCoherent (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  n.map
  (fun x => (x.filter
  (fun y => y.Pairwise
  (fun a b => a.snd = b.snd -> a.fst = b.fst))).map
  (fun y => y.dedup))

theorem coherency : ∀ n : List (List (List (Bool × normalizable α pred))), coherent (makeCoherent n) :=
  by
  intro n g hg s hs
  unfold makeCoherent at hg
  obtain ⟨a, _, ha_transformed_to_g⟩ := List.mem_map.mp hg
  subst ha_transformed_to_g
  constructor
  intros w x hw heqw
  rw [List.mem_map] at hs
  obtain ⟨b, hb_in_filtered_a, hb_eq_s⟩ := hs
  subst hb_eq_s
  rw [List.mem_filter] at hb_in_filtered_a
  obtain ⟨hb_in_a, hb_pw⟩ := hb_in_filtered_a
  have hb_pairwise : b.Pairwise (fun c d => c.snd = d.snd → c.fst = d.fst) := by simpa using hb_pw
  have snd_eq : w.snd = x.snd := by simpa using heqw
  have hp : ∀ c d, c ∈ b ∧ d ∈ b → c.2 = d.2 → c.1 = d.1 := by
    intro c d ⟨hc, hd⟩
    refine List.Pairwise.forall_of_forall ?_ (by simp) hb_pairwise hc hd
    intro x y h1 h2
    exact (h1 (h2.symm)).symm
  obtain ⟨ hw_left, hw_right⟩ := hw
  simp
  apply hp
  constructor
  rw [← List.mem_dedup]
  exact hw_left
  rw [← List.mem_dedup]
  exact hw_right
  rw [beq_iff_eq] at heqw
  exact heqw
  simp [List.nodup_dedup] at hs
  obtain ⟨b, _, hb_eq_s⟩ := hs
  rw [← hb_eq_s]
  exact List.nodup_dedup b

theorem property1 : ∀ n : List (List (List (Bool × normalizable α pred))),
                    ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                    ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                    ∀ i : Bool × normalizable α pred, (nToProp n -> sToProp s -> wToProp i) ->
                    (nToProp n -> (sToProp s <-> sToProp (s.concat i))) :=
  by
  intro n
  intro g
  intro _
  intro s
  intro _
  intro w
  intro hw
  intro hn
  simp
  unfold sToProp
  rw [all_and]
  constructor
  intro hss
  constructor
  exact hss
  simp
  apply hw
  exact hn
  unfold sToProp
  exact hss
  intro hsw
  exact hsw.left

theorem property2 : ∀ n : List (List (List (Bool × normalizable α pred))),
                    ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                    ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                    ((nToProp n -> ¬(sToProp s)) -> nToProp n -> (gToProp g <-> gToProp (g.erase s))) :=
  by
  intro n
  intro g
  intro _
  intro s
  intro hs
  intro hns
  intro hn
  unfold gToProp
  have hnos : ¬ sToProp s :=
  by {
    apply hns
    exact hn
  }
  apply any_erase at g
  apply g at hs
  apply hs at hnos
  rw [hnos]
  simp
  congr!
  apply lawful_beq_subsingleton

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
