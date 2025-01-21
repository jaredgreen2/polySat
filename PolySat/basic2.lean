import Init.Data.List
import Init.PropLemmas
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Bool.AllAny
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic
import Batteries.Data.List.Lemmas
import Batteries.Data.List.Basic
import Mathlib.Data.Lists.Sublists
import Mathlib.Data.Multiset.Basic
--import Mathlib.Algebra.BigOperators.Group.List.Basic
import Aesop
open Classical

set_option maxHeartbeats 20000000

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
theorem toProp_atom {a : α} : toProp (atom a : normalizable α pred) ↔ pred a := by unfold toProp; rfl

--@[simp]
@[reducible]
def nStrip (n : normalizable α pred) : Bool × normalizable α pred :=
  match n with
  | Not i => let j := nStrip i; (!j.1,j.2)
  | i => (true,i)

def subnormalize (n : (normalizable α pred)) : List (List (List (Bool × normalizable α pred))) :=
  match n with
  | Or a b =>  [
   [nStrip a,nStrip n] ,
   [nStrip b,nStrip n],
   [nStrip (Not n),nStrip (Not a),nStrip (Not b)] ] :: (List.append (subnormalize a) (subnormalize b))
  | And a b => [ [nStrip n,nStrip a,nStrip b] ,
   [nStrip (Not a),nStrip (Not n)] ,
   [nStrip (Not b),nStrip (Not n)] ] :: (List.append (subnormalize a) (subnormalize b))
  | Not i => [[nStrip n,nStrip (Not i)],[nStrip (Not n),nStrip i]] :: (subnormalize i)
  | atom _ => [[[(true,n)],[(false,n)]]]

def normalize :  normalizable α pred -> List (List (List (Bool × normalizable α pred))) := fun o =>
  [[(true,o)]] :: (subnormalize o)

@[aesop 90% unfold]
def wToProp (w : Bool × normalizable α pred) : Prop :=
  if w.fst then toProp w.snd else ¬(toProp w.snd)

@[aesop 90% unfold]
def sToProp (s : List (Bool × normalizable α pred)) : Prop :=
  s.all (fun x => wToProp x)

@[aesop 90% unfold]
def gToProp (g : List (List (Bool × normalizable α pred))) : Prop :=
  g.any (fun x => sToProp x)

@[aesop 90% unfold]
def nToProp (n : List (List (List (Bool × normalizable α pred)))) : Prop :=
  n.all (fun x => gToProp x)

def fToProp (n : List (List (List (normalizable α pred)))) : Prop :=
  n.all (fun x => x.any (fun y => y.all (fun z => toProp z)))

@[simp]
theorem nStrip_equiv (n : normalizable α pred) : wToProp (nStrip n) <-> toProp n  :=
  by
  induction' n with a a1 a2 andl andr a1 a2 orl orr a ha
  unfold normalizable.wToProp
  simp_all only [↓reduceIte]
  unfold normalizable.wToProp
  unfold normalizable.wToProp at andl
  unfold normalizable.wToProp at andr
  simp_all only [toProp_and, ↓reduceIte]
  unfold normalizable.wToProp
  unfold normalizable.wToProp at orl
  unfold normalizable.wToProp at orr
  simp_all only [toProp_or, ↓reduceIte]
  unfold normalizable.wToProp
  unfold normalizable.wToProp at ha
  simp_all only [toProp_not, Bool.not_eq_true']
  apply Iff.intro
  · intro a_1
    simp_all
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    simp_all only [iff_true]
    split at ha
    next h_1 =>
      split at a_1
      next h_2 => simp_all only
      next h_2 => simp_all only [Bool.false_eq_true]
    next h_1 =>
      split at a_1
      next h_2 => simp_all only [not_true_eq_false]
      next h_2 => simp_all only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false]
  · intro a_1
    simp_all only [iff_false, Bool.ite_eq_false]
    split
    next h_1 => simp_all only [↓reduceIte, not_false_eq_true]
    next h_1 => simp_all only [Bool.false_eq_true, ↓reduceIte, Decidable.not_not, Bool.not_eq_true]


theorem w_neg :∀ a : Bool × normalizable α pred, wToProp (!a.1,a.2) <-> ¬ (wToProp a) :=
  by
  intro a
  unfold normalizable.wToProp
  simp_all only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.ite_eq_false]
  obtain ⟨fst, snd⟩ := a
  simp_all only
  apply Iff.intro
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    split at a
    next h_1 =>
      split at a_1
      next h_2 =>
        subst h_1
        simp_all only [not_true_eq_false]
      next h_2 =>
        subst h_1
        simp_all only [not_true_eq_false]
    next h_1 =>
      split at a_1
      next h_2 =>
        subst h_2
        simp_all only [not_true_eq_false]
      next h_2 => simp_all only [Bool.false_eq_true, not_false_eq_true]
  · intro a
    split
    next h_1 =>
      subst h_1
      simp_all only [↓reduceIte, not_false_eq_true]
    next h_1 => simp_all only [Bool.false_eq_true, ↓reduceIte, Decidable.not_not, Bool.not_eq_true]

@[aesop 90%]
theorem all_and : List.all ( a ++ b) c <-> List.all a c ∧ List.all b c :=
  by
  simp

theorem any_erase :∀ l : List b,∀ a: b -> Prop,
                     ∀ s : b,s ∈ l -> ¬ (a s) -> (List.any l a <-> List.any (List.erase l s) a) :=
  by
  intro l a s hs hnas
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
  intro f hf haf
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

theorem any_filter : ∀ s : a -> Bool, ∀ l:List a, l.any s <-> (l.filter s).any s :=
  by
  intro s l
  induction' l with hd t _
  simp
  unfold List.filter
  cases' Classical.em (s hd) with hsh hnsh
  simp
  nth_rewrite 2 [hsh]
  simp
  simp
  simp at hnsh
  rw [hnsh]
  simp

theorem all_filter (s t : a -> Bool) : ∀ l : List a, l.all s -> (l.filter t).all s :=
  by
  intro l hl
  simp
  intro x hx
  simp at hl
  right
  apply hl
  exact hx

theorem any_filter_imp (s t : a -> Bool): (∀ x : a, ¬ (s x) -> ¬ (t x)) -> ∀ l : List a,l.any t <-> (l.filter s).any t :=
  by
  intro hst l
  simp
  induction' l with hd tl ht
  simp
  cases' Classical.em (s hd) with hsh hnsh
  simp
  rw [hsh]
  simp
  rw [ht]
  simp at hnsh
  have hnt : ¬ t hd := by {
    apply hst
    simp
    exact hnsh
  }
  simp
  simp at hnt
  rw [hnt]
  simp
  rw [ht]

@[aesop 90% unfold]
def bcompatible (s : List (Bool × normalizable α pred)) (t : List (Bool × normalizable α pred)) : Bool :=
  s.all (fun x => t.all (fun y =>  x.snd == y.snd -> x.fst == y.fst))

@[aesop 90% apply]
theorem compatibility :∀ a b : List (Bool × normalizable α pred),  (¬ bcompatible a b = true) -> ¬(sToProp a ∧ sToProp b) :=
  by
  intro a b hb hab
  unfold bcompatible at hb
  simp only [beq_iff_eq, List.all_eq_true, decide_eq_true_eq, Bool.forall_bool,
    implies_true, imp_false, true_and, and_true, not_and, not_forall, not_not, exists_prop,
    exists_eq_right'] at hb
  obtain ⟨ y,hy,z,hz,hyzl,hyzr⟩ := hb
  obtain ⟨ hsa,hsb⟩ := hab
  have hyw : wToProp y := by {
    unfold sToProp at hsa
    simp only [List.all_eq_true, decide_eq_true_eq, Bool.forall_bool] at hsa
    apply hsa
    exact hy
  }
  have hzw : wToProp z := by {
    unfold sToProp at hsb
    simp only [List.all_eq_true, decide_eq_true_eq, Bool.forall_bool] at hsb
    apply hsb
    exact hz
  }
  have hy1 : y.1 == ! z.1 := by {
    simp
    cases' Classical.em (y.1 = true) with hy hy
    cases' Classical.em (z.1 = true) with hz hz
    by_contra hzy
    simp at hzy
    apply hyzr
    exact hzy
    simp at hz
    rw [hz]
    simp
    rw [hy]
    cases' Classical.em (z.1 = true) with hz hz
    simp at hy
    rw [hz]
    rw [hy]
    simp
    rw [eq_comm]
    by_contra hyz
    simp at hyz
    apply hyzr
    rw [eq_comm]
    exact hyz
  }
  simp at hy1
  have hyp : y = (y.1,y.2) := by {
    simp
  }
  rw [hyp] at hyw
  rw [hy1] at hyw
  rw [hyzl] at hyw
  rw [w_neg] at hyw
  apply hyw
  exact hzw

@[aesop 90% apply]
theorem subnormal : ∀ n : normalizable α pred, nToProp (subnormalize n) :=
  by
  intro n
  induction' n with a b c d e f g i j k l
  unfold subnormalize
  unfold nToProp
  simp
  unfold gToProp
  simp
  unfold sToProp
  simp
  unfold wToProp
  simp
  exact Classical.em (toProp (atom a))
  unfold nToProp
  simp
  unfold subnormalize
  simp
  constructor
  unfold gToProp
  simp
  unfold sToProp
  simp
  rw [nStrip_equiv]
  rw [nStrip_equiv]
  rw [nStrip_equiv]
  rw [nStrip_equiv]
  cases' Classical.em (toProp b) with hb hnb
  cases' Classical.em (toProp c) with hc hnc
  simp_all
  apply And.intro
  · simp_all only
  · simp_all only
  simp_all
  apply Or.inr
  exact hnc
  cases' Classical.em (c.toProp) with hc hnc
  simp_all
  apply Or.inl
  exact hnb
  simp_all
  apply Or.inr
  exact hnc
  intro a a_1
  unfold normalizable.gToProp
  unfold normalizable.nToProp at d
  unfold normalizable.nToProp at e
  unfold normalizable.sToProp
  unfold normalizable.gToProp at d
  unfold normalizable.gToProp at e
  unfold normalizable.wToProp
  unfold normalizable.sToProp at d
  unfold normalizable.sToProp at e
  unfold normalizable.wToProp at d
  unfold normalizable.wToProp at e
  simp_all
  cases a_1 with
  | inl h_1 => simp_all only
  | inr h_2 => simp_all only
  unfold subnormalize
  unfold nToProp
  simp
  constructor
  unfold gToProp
  simp
  unfold sToProp
  simp
  rw [nStrip_equiv]
  rw [nStrip_equiv]
  rw [nStrip_equiv]
  rw [nStrip_equiv]
  cases' Classical.em (toProp f) with hf hnf
  cases' Classical.em (toProp g) with hg hng
  simp_all
  apply Or.inr
  simp_all only
  simp_all
  apply Or.inl
  simp_all only
  cases' Classical.em (toProp g) with hg hng
  simp_all
  apply Or.inr
  simp_all only
  simp_all
  apply And.intro
  exact hnf
  exact hng
  unfold normalizable.gToProp
  unfold normalizable.nToProp at i
  unfold normalizable.nToProp at j
  unfold normalizable.sToProp
  unfold normalizable.gToProp at i
  unfold normalizable.gToProp at j
  unfold normalizable.wToProp
  unfold normalizable.sToProp at i
  unfold normalizable.sToProp at j
  unfold normalizable.wToProp at i
  unfold normalizable.wToProp at j
  simp_all
  unfold subnormalize
  unfold nToProp
  simp
  unfold gToProp
  simp
  unfold sToProp
  simp
  constructor
  rw [nStrip_equiv]
  rw [nStrip_equiv]
  simp
  cases' Classical.em (toProp k) with hk hnk
  simp_all
  simp_all
  exact hnk
  intro x a
  unfold normalizable.wToProp
  unfold normalizable.nToProp at l
  unfold normalizable.gToProp at l
  unfold normalizable.sToProp at l
  unfold normalizable.wToProp at l
  simp_all

theorem normal : ∀ n : normalizable α pred, toProp n <-> nToProp (normalize n) :=
  by
  intro n
  unfold normalize
  constructor
  unfold nToProp
  simp
  intro hn
  constructor
  unfold gToProp
  simp
  unfold sToProp
  simp
  unfold wToProp
  simp
  exact hn
  apply subnormal at n
  unfold nToProp at n
  simp at n
  exact n
  unfold nToProp
  simp
  intro hg _
  unfold gToProp at hg
  simp at hg
  unfold sToProp at hg
  simp at hg
  unfold wToProp at hg
  simp at hg
  exact hg

theorem s_nodup : ∀ s : List (Bool × normalizable α pred), ((∀ w : Bool × normalizable α pred,∀ x : Bool × normalizable α pred, w ∈ s ∧ x ∈ s ->
  w.snd == x.snd -> w.fst == x.fst) ∧ s.Nodup) <-> (s.map Prod.snd).Nodup :=
  by
  intro s
  constructor
  intro hs
  obtain ⟨ hcond,hnodup⟩ := hs
  induction' s with hd tl ht
  simp [List.Nodup]
  unfold List.Nodup
  simp only [ne_eq, List.map_cons, List.pairwise_cons, List.mem_map, Prod.exists, exists_eq_right]
  constructor
  simp only [List.mem_cons, beq_iff_eq, and_imp, Prod.forall] at hcond
  intro a
  intro ha1
  obtain ⟨ a1,ha1⟩ := ha1
  cases' Classical.em (a1 = hd.1) with ha1e ha1ne
  rw [List.Nodup] at hnodup
  simp only [ne_eq, List.pairwise_cons] at hnodup
  obtain ⟨ hhd, _⟩ := hnodup
  by_contra hhd2
  apply hhd (a1,a)
  exact ha1
  have hconda := hcond hd.1 hd.2 a1 a (by left;simp) (by right;exact ha1)
  have hcondaa := hconda hhd2
  have hhd : hd =(hd.1,hd.2) := by {
    simp
  }
  rw [hhd]
  rw [hhd2]
  rw [hcondaa]
  have hconda := hcond hd.1 hd.2 a1 a (by left;simp) (by right;exact ha1)
  by_contra ha2
  apply ha1ne
  symm
  apply hconda
  rw [ha2]
  apply ht
  intro a b hab h
  obtain ⟨ ha , hb⟩ := hab
  exact hcond a b (by constructor;right;exact ha;right;exact hb) h
  unfold List.Nodup at hnodup
  simp at hnodup
  obtain ⟨ _,hnodup⟩ := hnodup
  simp [List.Nodup]
  exact hnodup
  induction' s with hd tl ht
  simp
  intro hs
  constructor
  intro w x hwx
  obtain ⟨ hw,hx⟩ := hwx
  cases' hx with hhx hxt
  cases' hw with hhw hwt
  intro _
  simp
  simp only [List.map_cons, List.nodup_cons, List.mem_map, Prod.exists, exists_eq_right,
     not_or] at hs
  intro hwh2
  by_contra
  obtain ⟨ hs1,_⟩ := hs
  apply hs1
  use w.1
  simp at hwh2
  rw [← hwh2]
  simp
  assumption
  cases' hw with hhw hwt
  intro hxh2
  by_contra
  simp only [List.map_cons, List.nodup_cons, List.mem_map, Prod.exists, exists_eq_right,
     not_or] at hs
  obtain ⟨ hs1,_⟩ := hs
  apply hs1
  use x.1
  simp at hxh2
  rw [hxh2]
  simp
  assumption
  simp only [List.map_cons, List.nodup_cons, List.mem_map, Prod.exists, exists_eq_right,
     not_or] at hs
  obtain ⟨_,hs_right⟩ := hs
  unfold List.Nodup at hs_right
  simp at hs_right
  apply ht at hs_right
  obtain ⟨ hsl,_⟩ := hs_right
  have hslw := hsl w x
  apply hslw
  constructor
  assumption
  assumption
  simp
  simp only [List.map_cons, List.nodup_cons, List.mem_map, Prod.exists, exists_eq_right,
     not_or] at hs
  constructor
  obtain ⟨hs_left,hs_right⟩ := hs
  apply ht at hs_right
  by_contra hhd
  apply hs_left
  use hd.1
  obtain ⟨_,hs_right⟩ := hs
  apply ht at hs_right
  obtain ⟨_,hsr⟩ := hs_right
  exact hsr

def coherent (n : List (List (List (Bool × normalizable α pred)))) : Prop :=
  ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
  ∀ s : List (Bool × normalizable α pred), s ∈ g ->
  (s.map Prod.snd).Nodup

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
  rw [←  s_nodup]
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


theorem rule1 : ∀ n : List (List (List (Bool × normalizable α pred))),
                ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                ∀ s : List (Bool × normalizable α pred), s ∈ g ->
                ∀ v : Bool × normalizable α pred, ¬(v ∈ s) ->
                (∃ h : List (List (Bool × normalizable α pred)), h ∈ n ∧
                ∀ t : List (Bool × normalizable α pred), t ∈ h ->
                bcompatible t s -> v ∈ t) ->
                nToProp n -> sToProp s -> wToProp v :=
  by
  intro n g _ s _ v _ hh
  obtain ⟨ i, hh, hah⟩ := hh
  intro hn
  have hi : gToProp i := by {
    unfold nToProp at hn
    simp at hn
    apply hn at hh
    exact hh
  }
  intro hhs
  unfold gToProp at hi
  unfold sToProp at hi
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.forall_bool, Bool.decide_and,
    List.any_eq_true, Bool.and_eq_true] at hi
  by_contra hw
  have hni : ¬ (∃ x ∈ i, ∀ w ∈ x, wToProp w) := by {
    rw [not_exists]
    simp only [ Bool.forall_bool, not_and]
    intro x
    intro hx
    push_neg
    cases' Classical.em (bcompatible x s) with hvx hvnx
    use v
    constructor
    apply hah
    exact hx
    exact hvx
    exact hw
    unfold bcompatible at hvnx
    simp only [beq_iff_eq, List.all_eq_true, decide_eq_true_eq, Bool.forall_bool,
      implies_true, imp_false, true_and, and_true, not_and, not_forall, not_not, exists_prop,
      exists_eq_right'] at hvnx
    obtain ⟨ y,hy,z,hz,hyzl,hyzr⟩ := hvnx
    have hwy : wToProp z := by {
      unfold sToProp at hhs
      simp only [List.all_eq_true, decide_eq_true_eq, Bool.forall_bool] at hhs
      apply hhs
      exact hz
    }
    cases' Classical.em (sToProp x) with hyl hzr
    exfalso
    have hzl : wToProp y := by {
      unfold sToProp at hyl
      simp only [List.all_eq_true, decide_eq_true_eq, Bool.forall_bool] at hyl
      apply hyl
      exact hy
    }
    have hy1 : y.1 == ! z.1 := by {
      simp
      cases' Classical.em (y.1 = true) with hy hy
      cases' Classical.em (z.1 = true) with hz hz
      by_contra hzy
      simp at hzy
      apply hyzr
      exact hzy
      simp at hz
      rw [hz]
      simp
      rw [hy]
      cases' Classical.em (z.1 = true) with hz hz
      simp at hy
      rw [hz]
      rw [hy]
      simp
      rw [eq_comm]
      by_contra hyz
      simp at hyz
      apply hyzr
      rw [eq_comm]
      exact hyz
    }
    simp at hy1
    have hyp : y = (y.1,y.2) := by {
      simp
    }
    rw [hyp] at hzl
    rw [hy1] at hzl
    rw [hyzl] at hzl
    rw [w_neg] at hzl
    apply hzl
    exact hwy
    unfold sToProp at hzr
    simp only [List.all_eq_true, decide_eq_true_eq, Bool.forall_bool, not_and,
      not_forall, exists_prop] at hzr
    exact hzr
  }
  apply hni
  exact hi

theorem rule2 : ∀ n : List (List (List (Bool × normalizable α pred))),
                ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
                ∀ s : List (Bool × normalizable α pred),
                (∃ h : List (List (Bool × normalizable α pred)), h ∈ n ∧
                ∀ t : List (Bool × normalizable α pred), t ∈ h ->
                ¬(bcompatible s t)) ->
                nToProp n -> ¬(sToProp s) :=
  by
  intro n g _ s hi hn hns
  obtain ⟨ h,hh,hat⟩ := hi
  have hgh : gToProp h := by {
    unfold nToProp at hn
    simp at hn
    apply hn
    exact hh
  }
  unfold gToProp at hgh
  simp at hgh
  obtain ⟨ x,hx,hsx⟩ := hgh
  apply hat at hx
  apply compatibility at hx
  apply hx
  constructor
  exact hns
  exact hsx

theorem op1 : ∀ n : List (List (List (Bool × normalizable α pred))),
                    ∀ g h : List (List (Bool × normalizable α pred)), g ∈ n ∧ h ∈ n ->
                    nToProp n -> (gToProp g <-> gToProp (g.filter (fun x => h.any (fun y => bcompatible x y )))) :=
  by
  intro n g hi hg hn
  obtain ⟨ hg,hhi⟩ := hg
  unfold gToProp
  apply any_filter_imp
  intro l
  intro hns
  simp
  apply rule2
  exact hg
  simp at hns
  use hi
  constructor
  use hhi
  simp
  exact hns
  exact hn

theorem bcompatible_symm : ∀s t : List (Bool × normalizable α pred), bcompatible s t <-> bcompatible t s :=
  by
  intro s t
  unfold bcompatible
  simp only [beq_iff_eq, dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true]
  constructor
  intro hs x hx y hy hxy
  symm at hxy
  symm
  exact hs y hy x hx hxy
  intro hs x hx y hy hxy
  symm at hxy
  symm
  exact hs y hy x hx hxy

@[reducible]
def interl (l : List (List a)) [DecidableEq a] : List a :=
  match l with
  | [] => []
  | a :: [] => a
  | (a :: as) => List.inter a (interl as)

theorem interl_all (s : a -> Prop) : ∀ l : List (List a),
          l.any (fun x => x.all (fun y => s y)) -> ∀ b ∈ interl l, s b :=
  by
  intro l
  simp
  induction' l with hd t ht
  simp
  simp
  constructor
  intro hx
  unfold interl
  cases' Classical.em (t = []) with hht hnt
  rw [hht]
  simp
  exact hx
  simp
  apply List.forall_mem_inter_of_forall_left
  exact hx
  unfold interl
  cases' Classical.em (t = []) with hht hnt
  rw [hht]
  simp
  simp
  intro x hx hhx
  apply List.forall_mem_inter_of_forall_right
  apply ht
  exact hx
  exact hhx

theorem interl_all_filter (s : a -> Prop)(t : List a -> Prop) : (∀ x : List a, ¬ t x -> ¬(x.all fun y => s y))
     -> ∀ l : List (List a), (l.any (fun x => x.all (fun y => s y))
     -> ∀ b ∈ interl (l.filter (fun x => t x)), s b) :=
  by
  intro ha l hl
  simp at hl
  obtain ⟨ m, hm, hhm⟩ := hl
  induction' l with hd tl ht
  simp
  rw [List.filter_cons]
  cases' Classical.em (t hd) with htll htlr
  apply eq_true at htll
  rw [htll]
  simp
  cases' Classical.em (tl = []) with htl htr
  rw [htl]
  simp
  have hmd : m = hd := by
  {
    simp at hm
    cases' hm with hml hmr
    assumption
    exfalso
    rw [htl] at hmr
    apply List.not_mem_nil at hmr
    exact hmr
  }
  rw [← hmd]
  exact hhm
  cases' Classical.em (List.filter (fun x ↦ decide (t x)) tl = []) with htn htf
  have hdm : interl (hd :: List.filter (fun x ↦ decide (t x)) tl) = hd := by {
    rw [htn]
  }
  rw [hdm]
  simp at hm
  cases' hm with hm hm
  rw [← hm]
  exact hhm
  exfalso
  rw [List.filter_eq_nil_iff] at htn
  apply htn at hm
  apply ha
  simp at hm
  exact hm
  simp
  exact hhm
  unfold interl
  simp
  cases' Classical.em (m ∈ tl) with hmt hhd
  apply List.forall_mem_inter_of_forall_right
  apply ht
  exact hmt
  apply List.forall_mem_inter_of_forall_left
  have hmd : m = hd := by{
    simp at hm
    cases hm
    assumption
    exfalso
    apply hhd
    assumption
  }
  rw [← hmd]
  exact hhm
  have hmnt : m ≠ hd := by {
    intro hmt
    apply ha
    exact htlr
    simp
    rw [← hmt]
    exact hhm
  }
  apply eq_false at htlr
  rw [htlr]
  simp
  cases' Classical.em (tl = []) with htl htr
  rw [htl]
  simp
  simp at hm
  cases hm
  exfalso
  apply hmnt
  assumption
  apply ht
  assumption

theorem interl_all_nodup : ∀ l : List (List (Bool × normalizable α pred)), (∀ m ∈ l, (m.map Prod.snd).Nodup) -> ((interl l).map Prod.snd).Nodup :=
  by
  intro l
  induction' l with hd tl ih
  intro _
  dsimp
  simp
  intro h
  clear ih
  induction' tl with hd2 tl _
  unfold interl
  apply h
  simp
  unfold interl
  rw [← s_nodup]
  have hhd := h hd (by simp)
  rw [← s_nodup] at hhd
  constructor
  intro w x hxw hwx
  obtain ⟨ hw,hx⟩ := hxw
  apply List.inter_subset_left at hw
  apply List.inter_subset_left at hx
  apply hhd.1
  constructor
  exact hw
  exact hx
  exact hwx
  apply List.Nodup.inter
  exact hhd.2

theorem interl_all_bcompatible : ∀ l : List (Bool × normalizable α pred),∀ m : List (List (Bool × normalizable α pred)), (∀ n ∈ m, bcompatible l n) -> bcompatible l (interl m) :=
  by
  intro l m hm
  induction' m with hd tl ih
  unfold interl
  unfold bcompatible
  simp
  unfold interl
  cases' Classical.em (tl = []) with hp hn
  rw [hp]
  simp
  apply hm
  simp
  simp
  unfold bcompatible
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true]
  intro w hw x hx hwx
  apply List.mem_of_mem_inter_left at hx
  unfold bcompatible at hm
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hm
  apply hm hd
  simp
  exact hw
  exact hx
  exact hwx

theorem interl_bcompatible_12 : ∀ l : List ( Bool × normalizable α pred), ∀ m : List (List (Bool × normalizable α pred)), (∃ n ∈ m,bcompatible l n) -> bcompatible l (interl m) :=
  by
  intro l m hmn
  obtain ⟨ n, hn,hhn⟩ := hmn
  induction' m with hd tl ih
  unfold interl
  unfold bcompatible
  simp
  cases' hn with ht
  unfold interl
  cases' Classical.em (tl = []) with htl htr
  rw [htl]
  simp
  exact hhn
  simp
  unfold bcompatible
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true]
  intro w hw x hx hwx
  unfold bcompatible at hhn
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hhn
  apply hhn
  exact hw
  apply List.mem_of_mem_inter_left at hx
  exact hx
  exact hwx
  unfold bcompatible at ih
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at ih
  unfold interl
  cases' Classical.em (tl = []) with htl htr
  rw [htl]
  simp
  exfalso
  apply List.not_mem_nil n
  rw [← htl]
  assumption
  simp
  unfold bcompatible
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true]
  intro w hw x hx hwx
  apply ih
  assumption
  exact hw
  apply List.mem_of_mem_inter_right at hx
  exact hx
  exact hwx

theorem interl_bcompatible2 :  ∀ m n : List (List (Bool × normalizable α pred)),
         ((∃ o ∈ m, ∃ p ∈ n, bcompatible  o p ) -> bcompatible (interl m) (interl n)  ):=
  by
  intro m n hop
  induction' m with hd1 tl1 ih1
  obtain ⟨ o,ho,p,_,_⟩ := hop
  contradiction
  induction' n with hd2 tl2 _
  obtain ⟨o,_,p,hp,_⟩ := hop
  contradiction
  obtain ⟨o,ho,p,hp,hop⟩ := hop
  cases ho
  have hb : bcompatible hd1 (interl (hd2 :: tl2)) := by (
    apply interl_bcompatible_12
    use p
  )
  unfold bcompatible
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true]
  intro w hw x hx hwx
  unfold bcompatible at hb
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hb
  apply hb
  unfold interl at hw
  cases' Classical.em (tl1 = []) with htl htr
  rw [htl] at hw
  simp at hw
  exact hw
  simp at hw
  apply List.mem_of_mem_inter_left at hw
  exact hw
  exact hx
  exact hwx
  cases' hp
  have ha : bcompatible hd2 (interl (hd1 :: tl1)) := by {
    apply interl_bcompatible_12
    use o
    constructor
    right
    assumption
    rw [bcompatible_symm]
    exact hop
  }
  rw [bcompatible_symm]
  unfold bcompatible
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true]
  intro w hw x hx hwx
  unfold bcompatible at ha
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at ha
  apply ha
  unfold interl at hw
  cases' Classical.em (tl2 = []) with htl htr
  rw [htl] at hw
  simp at hw
  exact hw
  simp at hw
  apply List.mem_of_mem_inter_left at hw
  exact hw
  exact hx
  exact hwx
  unfold bcompatible
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true]
  intro w hw x hx hwx
  unfold bcompatible at ih1
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at ih1
  apply ih1
  use o
  constructor
  assumption
  use p
  constructor
  right
  assumption
  unfold bcompatible at hop
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hop
  exact hop
  unfold interl at hw
  cases' Classical.em (tl1 = []) with htl htr
  exfalso
  apply List.not_mem_nil o
  rw [← htl]
  assumption
  simp at hw
  apply List.mem_of_mem_inter_right at hw
  exact hw
  exact hx
  exact hwx

theorem forall_mem_or {b : a -> Prop}{c : a -> Prop}{e : a -> Prop}: (∀ f, (b f ∨ c f) -> e f) <-> (∀ f, b f -> e f) ∧ (∀ f, c f -> e f ) :=
  by
  constructor
  intro ha
  constructor
  intros a hha
  apply ha
  left
  exact hha
  intros a hha
  apply ha
  right
  exact hha
  intro ha
  intros a hha
  obtain ⟨ hal, har ⟩ := ha
  cases hha
  apply hal
  assumption
  apply har
  assumption

theorem interl_filter_filter (d : a -> Prop)(e : List a -> Prop):
        ∀ b : a,∀ c : List (List a),
        b ∈ interl ((c.filter (fun x: List a => e x)).map (fun x => x.filter (fun y : a => (d y) )))
        -> b ∈ interl (c.filter fun x => e x) :=
  by
  intro f
  intro l
  induction' l with hd t ht
  simp
  cases' Classical.em (e hd) with hdl hdr
  intro hi
  rw [List.filter_cons]
  simp
  apply eq_true at hdl
  rw [hdl]
  simp
  rw [List.filter_cons] at hi
  rw [hdl] at hi
  simp at hi
  cases' Classical.em (  (List.filter (fun x ↦ decide (e x)) t) = []) with hfe hff
  unfold interl
  rw [hfe]
  simp
  unfold interl at hi
  rw [hfe] at hi
  simp at hi
  exact hi.left
  unfold interl
  simp
  have hhi : f ∈
    (List.filter (fun y ↦ decide (d y)) hd).inter
    (interl (List.map (fun x ↦ List.filter
    (fun y ↦ decide (d y)) x) (List.filter
    (fun x ↦ decide (e x)) t))) := by{
    unfold interl at hi
    revert hi
    have hfm : List.map (fun x ↦ List.filter (fun y ↦ decide (d y)) x) (List.filter (fun x ↦ decide (e x)) t) ≠ [] := by {
      intro hg
      simp at hg
      apply hff
      simp
      exact hg
    }
    simp
  }
  apply List.mem_inter_of_mem_of_mem
  apply List.inter_subset_left at hhi
  simp at hhi
  exact hhi.left
  apply List.inter_subset_right at hhi
  apply ht
  exact hhi
  rw [List.filter_cons]
  apply eq_false at hdr
  rw [hdr]
  simp
  exact ht

theorem op2 : ∀ n : List (List (List (Bool × normalizable α pred))),
              ∀ g h : List (List (Bool × normalizable α pred)), h ∈ n
              -> g.all (fun x => h.any (fun y => bcompatible x y))
              -> nToProp n
              -> (gToProp g
                <-> gToProp (g.map (fun x =>
                x.append (interl ((h.filter
                (fun y => bcompatible x y)).map
              (fun y => y.filter (fun z => z ∉ x))))))) :=
  by
  intro n g hi hhi hg hn
  simp at hg
  simp
  unfold gToProp
  simp
  constructor
  intro hl
  obtain ⟨ t,ht,hht⟩ := hl
  use t
  constructor
  exact ht
  unfold sToProp
  rw [all_and]
  constructor
  unfold sToProp at hht
  simp only [List.all_eq_true, decide_eq_true_eq]
  simp only [List.all_eq_true, decide_eq_true_eq] at hht
  exact hht
  unfold nToProp at hn
  simp only [List.all_eq_true, decide_eq_true_eq] at hn
  have hgi : gToProp hi := by {
    apply hn at hi
    apply hi at hhi
    exact hhi
  }
  unfold gToProp at hgi
  unfold sToProp at hgi
  simp only [List.all_eq_true, decide_eq_true_eq]
  intros p ho
  apply interl_all_filter wToProp (fun y => bcompatible t y)
  intro l hlb hla
  have hlaf : sToProp l := by {
    unfold sToProp
    exact hla
  }
  apply compatibility at hlb
  apply hlb
  constructor
  exact hht
  exact hlaf
  simp only [List.all_eq_true, decide_eq_true_eq, Prod.forall
  ,  Bool.decide_and, List.any_eq_true, Bool.and_eq_true] at hgi
  simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq, Prod.forall]
  exact hgi
  apply interl_filter_filter (fun z => !(z ∈ t)) (fun x => bcompatible t x)
  simp
  convert ho
  intro hr
  unfold sToProp at hr
  unfold sToProp
  simp only [List.all_eq_true, decide_eq_true_eq]
  simp only [List.all_eq_true, List.mem_append, decide_eq_true_eq, ] at hr
  obtain ⟨ a, ha, hag⟩ := hr
  rw [forall_mem_or] at hag
  obtain ⟨ hagl,_⟩ := hag
  use a

theorem rule3 : ∀ n : List (List (List (Bool × normalizable α pred))), [] ∈ n -> ¬(nToProp n) :=
  by
  intro n hn
  unfold nToProp
  simp only [List.all_eq_true, decide_eq_true_eq, not_forall, exists_prop]
  use []
  unfold gToProp
  constructor
  exact hn
  simp

theorem mem_replace_or_mem : ∀ b c x : α,∀ l : List α, x ∈ l.replace b c -> x = c ∨ x ∈ l :=
  by
  intro b c x l h
  induction' l with hd t ht
  simp at h
  simp [List.replace] at h
  cases' Classical.em (b = hd) with hb hbn
  rw [hb] at h
  simp at h
  cases' h with hc ht
  left
  exact hc
  right
  right
  exact ht
  have hnb : (b == hd) = false := by
  {
    simp
    exact hbn
  }
  rw [hnb] at h
  simp at h
  cases' h with hl hr
  right
  simp
  left
  exact hl
  apply ht at hr
  cases' hr with hrl hrr
  left
  exact hrl
  right
  right
  exact hrr

theorem mem_replace_of_eq : ∀ a b : c,∀ l : List c, a ∈ l -> b ∈ l.replace a b :=
  by
  intro a b l ha
  induction' l with hd t ht
  contradiction
  simp [List.replace]
  cases' Classical.em (a = hd) with heq hne
  rw [heq]
  simp
  have hna : (a == hd) = false := by {
    simp
    exact hne
  }
  rw [hna ]
  simp
  right
  cases' ha with hahd hatl
  contradiction
  apply ht
  assumption

theorem mem_replace_of_mem_of_ne_r : ∀ a b x : α, ∀ l: List α, x ∈ l -> x ≠ a -> x ∈ l.replace a b :=
  by
  intro a b x l hx hne
  induction' l with hd t ht
  contradiction
  simp [List.replace]
  cases' Classical.em (a = hd) with heq hneq
  rw [heq]
  cases' hx with hxhd hxtl
  exfalso
  apply hne
  rw [heq]
  simp
  right
  assumption
  have hna : (a == hd) = false := by {
    simp
    exact hneq
  }
  rw [hna]
  simp
  cases' hx with hxhd hxtl
  left
  rfl
  right
  apply ht
  assumption

theorem mem_replace_of_mem_of_ne_l : ∀ a b x : α, ∀ l : List α, x ∈ l.replace a b -> x ≠ b -> x ∈ l :=
  by
  intro a b x l hx hnxb
  induction' l with hd tl ht
  unfold List.replace at hx
  contradiction
  unfold List.replace at hx
  cases' Classical.em (a = hd) with hah hnah
  rw [hah] at hx
  simp at hx
  cases hx
  contradiction
  simp
  right
  assumption
  have hanh : (a == hd) = false := by {
    simp
    exact hnah
  }
  rw [hanh ] at hx
  simp at hx
  cases' hx with hx hx
  simp
  left
  exact hx
  right
  apply ht
  exact hx

theorem rep1 : ∀ n : List (List (List (Bool × normalizable α pred))),
              ∀ g : List (List (Bool × normalizable α pred)), g ∈ n ->
              ∀ s t : List (Bool × normalizable α pred), s ∈ g ->
              (nToProp n -> (sToProp s <-> sToProp t) ) ->
              (nToProp n -> (gToProp g <-> gToProp (g.replace s t))) :=
  by
  intro n g hg s t hs hnst hn
  have hst := hnst hn
  constructor
  unfold gToProp
  simp only [List.any_eq_true, decide_eq_true_eq]
  intro hgg
  cases' g with hd tl ht
  contradiction
  unfold List.replace
  cases' Classical.em (s = hd) with hsh hsnh
  rw [hsh]
  simp
  rw [← hst]
  simp at hgg
  rw [← hsh] at hgg
  exact hgg
  have hnsh : (s == hd) = false := by {
    simp
    exact hsnh
  }
  rw [hnsh]
  simp
  simp at hgg
  cases' hgg with hgg hgg
  left
  exact hgg
  right
  obtain ⟨ a, hal, har⟩ := hgg
  cases' Classical.em (a = s) with has hans
  use t
  constructor
  simp at hs
  have hs : s ∈ tl := by {
    cases hs
    contradiction
    assumption
  }
  convert mem_replace_of_eq s t tl hs
  rw [← hst]
  rw [← has]
  exact har
  use a
  constructor
  convert mem_replace_of_mem_of_ne_r s t a tl hal hans
  exact har
  unfold gToProp
  simp only [List.any_eq_true, decide_eq_true_eq]
  intro hgr
  induction' g with hd tl _
  contradiction
  obtain ⟨ x,hx,hgs⟩ := hgr
  unfold List.replace at hx
  cases' Classical.em (s = hd) with hshd hsnh
  rw [hshd] at hx
  simp at hx
  cases' hx with hx hx
  use s
  constructor
  simp
  left
  exact hshd
  rw [hst]
  rw [← hx]
  exact hgs
  use x
  constructor
  right
  exact hx
  exact hgs
  have hnsh : (s == hd) = false := by {
    simp
    exact hsnh
  }
  rw [hnsh] at hx
  simp at hx
  cases' hx with hx hx
  use x
  constructor
  simp
  left
  assumption
  exact hgs
  cases' Classical.em (x = t) with hxs hxns
  use s
  constructor
  right
  have hs : s ∈ tl := by {
    cases hs
    contradiction
    assumption
  }
  exact hs
  rw [hst]
  rw [← hxs]
  exact hgs
  use x
  constructor
  right
  have himp : x ≠ t -> x ∈ tl := by {
    intro hb
    apply mem_replace_of_mem_of_ne_l s t x tl
    convert hx
    exact hb
  }
  apply himp
  rw [← ne_eq] at hxns
  exact hxns
  exact hgs

theorem rep2 : ∀ n : List (List (List (Bool × normalizable α pred))),
              ∀ g h : List (List (Bool × normalizable α pred)), g ∈ n ->
              (nToProp n -> (gToProp g <-> gToProp h)) -> (nToProp n -> (nToProp n <-> nToProp (n.replace g h))) :=
  by
  intro n g h hg hngh hn
  constructor
  intro hn
  unfold nToProp
  simp
  intro x hx
  unfold nToProp at hn
  simp at hn
  have hxx : x = h ∨ x ∈ n :=  by {
    apply mem_replace_or_mem g h x n
    convert hx
  }
  cases' (hxx) with hxh hxn
  rw [hxh]
  unfold nToProp at hngh
  simp at hngh
  have hgh := hngh hn
  rw [← hgh]
  apply hn
  exact hg
  apply hn
  exact hxn
  intro _
  exact hn

theorem all_length_list (c : List a -> Prop): (∀ l : List a, c l) <-> (∀ n : Nat,∀ l:List a , l.length = n -> c l) :=
  by
  constructor
  intro hl
  intro n
  intro l _
  apply hl
  intro hn
  intro l
  let n := l.length
  apply hn n
  simp

theorem nodup_filter : ∀ (l : List α)(p : α -> Bool),l.Nodup -> (l.filter p).Nodup :=
  by
  intro l p hnodup
  induction' l with hd tl ht
  simp
  rw [List.filter_cons]
  cases' p hd with hp hp
  simp
  apply ht
  simp at hnodup
  exact hnodup.2
  simp only [↓reduceIte, List.nodup_cons,  Bool.not_eq_true]
  constructor
  simp at hnodup
  intro hcontra
  apply List.mem_of_mem_filter at hcontra
  apply hnodup.1
  exact hcontra
  apply ht
  simp at hnodup
  exact hnodup.2

theorem or_and_not (a b : Prop): a ∨ (b ∧ ¬ a) <-> a ∨ b :=
  by
  constructor
  swap
  intro ab
  cases' Classical.em (a) with ha na
  left
  exact ha
  right
  cases' ab with ha hb
  contradiction
  constructor
  exact hb
  exact na
  intro abna
  cases' abna with ha bna
  left
  exact ha
  right
  exact bna.1

theorem filterunionmem (a : b) (l m : List b): (a ∈ l ++ (m.filter (fun x => x ∉ l))) <-> a ∈ l ∨ a ∈ m :=
  by
  simp
  rw [or_and_not]

theorem bcompatible_self : ∀ s : List (Bool × normalizable α pred), List.Nodup (List.map Prod.snd s) -> bcompatible s s :=
  by
  intro s hs
  unfold bcompatible
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true]
  rw [← s_nodup] at hs
  intro x hx y hy hxy
  simp only [beq_iff_eq, and_imp, implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hs
  apply hs.1
  exact hx
  exact hy
  exact hxy

theorem bcompatible_union : ∀ s t u : List (Bool × normalizable α pred), bcompatible s u -> bcompatible t u -> bcompatible (s ++ t.filter (fun x => x ∉ s)) u :=
  by
  intro s t u
  unfold bcompatible
  simp only [beq_iff_eq, dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true, decide_not, List.all_append, List.all_filter, Bool.decide_and,
    ite_not, Bool.if_true_left, Bool.and_eq_true, and_imp]
  intro hsu htu
  constructor
  exact hsu
  intro x hx _ y hy hxy
  apply htu
  exact hx
  exact hy
  exact hxy

theorem bcompatible_union_left : ∀ s t u : List (Bool × normalizable α pred), bcompatible (t ++ u.filter (fun x => x ∉ t)) s  -> bcompatible t s ∧ bcompatible u s :=
  by
  intro s t u
  unfold bcompatible
  simp only [beq_iff_eq, dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true, decide_not, List.all_append, List.all_filter, Bool.decide_and,
    ite_not, Bool.if_true_left, Bool.and_eq_true]
  intro hstu
  constructor
  exact hstu.1
  intro x hx y hy
  cases' Classical.em (x ∈ t) with hxp hxn
  apply hstu.1
  exact hxp
  exact hy
  apply hstu.2
  exact hx
  exact hxn
  exact hy

theorem bcompatible_union_equiv ( s t u : List (Bool × normalizable α pred)) : bcompatible (t ++ u.filter (fun x => x ∉ t)) s <-> bcompatible t s ∧ bcompatible u s :=
  by
  constructor
  apply bcompatible_union_left
  intro ha
  apply bcompatible_union
  exact ha.1
  exact ha.2

theorem bcompatible_union_nodup : ∀ a b : List (Bool × normalizable α pred), bcompatible a b -> (a.map Prod.snd).Nodup -> (b.map Prod.snd).Nodup -> ((a ++ b.filter (fun x => x ∉ a)).map Prod.snd).Nodup :=
  by
  intro a b hab ha hb
  rw [← s_nodup]
  constructor
  intro w x hxw hwx
  obtain ⟨ hw,hx⟩ := hxw
  simp at hw hx
  cases' hw with hwl hwr
  cases' hx with hxl hxr
  rw [← s_nodup] at ha
  apply ha.1
  constructor
  exact hwl
  exact hxl
  exact hwx
  unfold bcompatible at hab
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hab
  simp
  apply hab
  exact hwl
  exact hxr.1
  simp at hwx
  exact hwx
  cases' hx with hxl hxr
  simp
  symm
  unfold bcompatible at hab
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hab
  apply hab
  exact hxl
  exact hwr.1
  simp at hwx
  symm
  exact hwx
  rw [← s_nodup] at hb
  apply hb.1
  constructor
  exact hwr.1
  exact hxr.1
  exact hwx
  apply List.Nodup.append
  rw [← s_nodup] at ha
  exact ha.2
  rw [← s_nodup] at hb
  apply nodup_filter
  exact hb.2
  unfold List.Disjoint
  simp only [ List.mem_filter]
  intro x hx hhx
  simp at hhx
  apply hhx.2
  exact hx

theorem filter_disjoint : ∀ l m: List α,List.Disjoint l (m.filter (fun x => x ∉ l)) :=
  by
  intro l m
  unfold List.Disjoint
  intro x hx
  simp
  intro _
  exact hx

def wireset (n : List (List (List (Bool × normalizable α pred)))) : List (normalizable α pred) :=
  ((n.map
  (fun g => (g.map
  (fun s => s.map
  (fun w => w.snd))).flatten)).flatten).dedup

theorem compatible_fold1 :  ∀ (init1 : List  (Bool × normalizable α pred))
       (lst1 : List (List (Bool × normalizable α pred))), ∀ hd1 : List  (Bool × normalizable α pred),
       (∀ x ∈ hd1 :: lst1, bcompatible init1 x) ->
       (∀ a ∈ hd1 :: lst1, ∀ b ∈ hd1 :: lst1, bcompatible a b) -> bcompatible hd1 (lst1.foldr (fun a b => a ++ (b.filter (fun x => x ∉ a))) init1):=
  by
  intro init1 lst1
  induction' lst1 with hd' tl' ih2
  intro hd1 hinit2 _
  simp
  simp at hinit2
  rw [bcompatible_symm]
  exact hinit2
  intro hd1 hinit2 hab2
  simp only [ List.foldr_cons]
  rw [bcompatible_symm]
  apply bcompatible_union
  apply hab2
  simp
  simp
  rw [bcompatible_symm]
  apply ih2
  intro x hx
  apply hinit2
  cases' hx with hx hx
  simp
  right
  right
  assumption
  intro a ha b hb
  apply hab2
  cases' ha with ha ha
  simp
  right
  right
  assumption
  cases' hb with hb hb
  simp
  right
  right
  assumption

theorem nodup_fold2 : ∀ (init : List  (Bool × normalizable α pred))
       (lst : List (List (Bool × normalizable α pred))),
       (init.map Prod.snd).Nodup ->
       (∀ x ∈ lst, (x.map Prod.snd).Nodup) ->
       (∀ x ∈ lst, bcompatible init x) ->
       (∀ a ∈ lst, ∀ b ∈ lst, bcompatible a b) ->
       ((lst.foldr (fun a b => a ++ (b.filter (fun x => x ∉ a))) init).map Prod.snd).Nodup :=
  by
  intro init lst
  induction' lst with hd tl ih1
  intro hinit _ _ _
  simp [List.foldr]
  exact hinit
  intro hinit htail hcompat_init hab
  rw [← s_nodup]
  have hinit3 := hinit
  simp only [ List.foldr_cons]
  have htail1 : (∀ x ∈ tl, (List.map Prod.snd x).Nodup) := by {
    intro y hy
    apply htail
    right
    exact hy
  }
  have htail2 : (∀ x ∈ tl, bcompatible init x = true) := by {
    intro y hy
    apply hcompat_init
    right
    convert hy
  }
  have htail3 : (∀ a ∈ tl, ∀ b ∈ tl, bcompatible a b = true) := by {
    intro y hy z hz
    apply hab
    right
    exact hy
    right
    exact hz
  }
  have hi := ih1 hinit3 htail1 htail2 htail3
  rw [← s_nodup] at hi
  obtain ⟨hi1, hi2⟩ := hi
  constructor
  intro w x hwx hwx2
  obtain ⟨ hw, hx⟩ := hwx
  rw [List.mem_append] at hw
  rw [List.mem_append] at hx
  cases' hw with hwd hwt
  cases' hx with hxd hxt
  have hth := htail hd (by simp)
  rw [← s_nodup] at hth
  obtain ⟨hth1, _⟩ := hth
  apply hth1
  constructor
  exact hwd
  exact hxd
  exact hwx2
  have hcompat_tl := compatible_fold1 init tl hd hcompat_init hab
  unfold bcompatible at hcompat_tl
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat_tl
  apply List.mem_of_mem_filter at hxt
  simp
  apply hcompat_tl
  exact hwd
  exact hxt
  simp at hwx2
  exact hwx2
  cases' hx with hxd hxt
  have hcompat_tl := compatible_fold1 init tl hd hcompat_init hab
  unfold bcompatible at hcompat_tl
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat_tl
  apply List.mem_of_mem_filter at hwt
  simp
  symm
  apply hcompat_tl
  exact hxd
  exact hwt
  simp at hwx2
  symm
  exact hwx2
  apply hi1
  constructor
  apply List.mem_of_mem_filter at hwt
  exact hwt
  apply List.mem_of_mem_filter at hxt
  exact hxt
  exact hwx2
  rw [List.nodup_append]
  constructor
  have hhd2 := htail hd (by simp)
  rw [← s_nodup] at hhd2
  exact hhd2.2
  constructor
  apply nodup_filter
  exact hi2
  unfold List.Disjoint
  intro a ha
  simp
  intro _
  exact ha



theorem nin_filter (hd : a)(l1: List a) : hd ∉ l1 -> l1 = l1.filter (fun x : a => hd ≠ x) :=
  by
  intro hhd
  induction' l1 with hd1 tl ih
  simp
  rw [List.filter_cons]
  rw [if_pos]
  simp at hhd
  have i2 := ih hhd.2
  rw [i2]
  simp
  simp
  simp at hhd
  exact hhd.1

theorem dedup_filter_length : ∀ l : List a,∀ b ∈ l, l.dedup.length = (l.filter (fun x => b ≠ x)).dedup.length + 1 :=
  by
  intro l b hb
  induction' l with hd tl ih
  simp
  contradiction
  cases' Classical.em (hd ∈ tl) with hl hr
  rw [List.dedup_cons_of_mem hl]
  cases' Classical.em (b = hd) with hlb hbr
  rw [← hlb]
  simp
  simp only [decide_not] at ih
  apply ih
  rw [hlb]
  exact hl
  cases hb
  contradiction
  rw [List.filter_cons]
  simp
  rw [if_neg hbr]
  rw [List.dedup_cons_of_mem']
  simp only [decide_not] at ih
  apply ih
  assumption
  rw [List.mem_dedup]
  rw [List.mem_filter]
  constructor
  exact hl
  simp
  exact hbr
  rw [List.dedup_cons_of_not_mem hr]
  cases' Classical.em (b = hd) with hbl hbr
  simp
  rw [List.filter_cons]
  rw [if_neg]
  rw [← hbl] at hr
  have ht : tl = tl.filter (fun x => b ≠ x) := by {
    apply nin_filter
    exact hr
  }
  simp at ht
  nth_rewrite 1 [ht]
  rfl
  simp
  exact hbl
  cases hb
  contradiction
  rw [List.filter_cons]
  rw [if_pos]
  rw [List.dedup_cons_of_not_mem]
  simp
  simp only [decide_not] at ih
  apply ih
  assumption
  rw [List.mem_filter]
  simp
  contrapose
  intro _
  exact hr
  simp
  exact hbr

theorem dedup_length (l1 : List a) :∀ l2 : List a,  l1 ⊆ l2 -> l1.dedup.length ≤ l2.dedup.length :=
  by
  induction' l1 with hd tl ih
  simp
  simp
  intro l3 hh hhh
  cases' Classical.em (hd ∈ tl) with hl hr
  rw [List.dedup_cons_of_mem hl]
  apply ih
  exact hhh
  rw [List.dedup_cons_of_not_mem]
  simp
  have htl2 : tl ⊆ l3.filter (fun x => hd ≠ x) := by {
    intro x hx
    rw [List.mem_filter]
    constructor
    exact hhh hx
    simp
    by_contra hhd
    apply hr
    rw [hhd]
    exact hx
  }
  have h3 := ih (l3.filter (fun x => hd ≠ x)) htl2
  have h4 : l3.dedup.length = (l3.filter (fun x => hd ≠ x)).dedup.length + 1 := by {
    apply dedup_filter_length
    exact hh
  }
  rw [h4]
  simp only [ne_eq, Nat.add_le_add_iff_right,ge_iff_le]
  exact h3
  exact hr

theorem add_of_sub (a b c : Nat) : a = b + c -> a - c = b :=
  by
  intro a_1
  subst a_1
  simp_all only [Nat.add_sub_cancel]

@[simp]
theorem first_of (f : a -> b) (g : a -> c): (fun x => x.1) ∘ (fun x => (f x,g x)) = f :=
  by
  rfl

@[simp]
theorem second_of (f : a -> b) (g : a -> c): (fun x => x.2) ∘ (fun x => (f x, g x)) = g :=
  by
  rfl

theorem sum_map_add (l : List a)(f g: a -> Nat ) : (l.map f).sum + (l.map g).sum = (l.map (fun x => f x + g x)).sum :=
  by
  induction' l with hd tl ih
  simp
  simp
  rw [← ih]
  rw [← Nat.add_assoc]
  rw [← Nat.add_assoc]
  nth_rewrite 2 [Nat.add_comm]
  rw [← Nat.add_assoc]
  nth_rewrite 3 [Nat.add_comm]
  rfl

theorem sum_map_ite (l : List a) (f g: a -> Nat) (h : a -> Bool): (l.map (fun x => if h x then f x else g x)).sum = ((l.filter h).map f).sum + ((l.filter (fun x => !(h x))).map g).sum :=
  by
  induction' l with hd tl ih
  simp
  simp
  rw [ih]
  rw [List.filter_cons]
  rw [List.filter_cons]
  cases h hd
  simp
  rw [← Nat.add_assoc]
  rw [← Nat.add_assoc]
  nth_rewrite 2 [Nat.add_comm]
  rfl
  simp
  rw [← Nat.add_assoc]

@[simp]
theorem sum_map_zero (l : List a) : (l.map (fun x => 0) ).sum = 0 :=
  by
  induction' l with hd tl ih
  simp
  simp only [List.map_cons, List.sum_cons, Nat.zero_add]
  exact ih

theorem zip_map_fst (l : List a) (f : a -> b) (g : a -> c) : (List.zip (l.map f) (l.map g)).map (fun x => x.1) = l.map f :=
  by
  rw [← List.unzip_fst]
  rw [List.unzip_zip]
  simp

theorem zip_map_snd (l : List a)(f : a -> b) (g : a -> c) : (List.zip (l.map f) (l.map g)).map (fun x => x.2) = l.map g :=
  by
  rw [← List.unzip_snd]
  rw [List.unzip_zip]
  simp

@[aesop 90% unfold]
def order (wireset : List (normalizable α pred)) (n : List (List (List (Bool × {w : normalizable α pred // w ∈ wireset})))) : Nat :=
  (n.map (fun x => (x.map (fun y => (wireset.length * 2) - y.length)).sum)).sum

def compatibilize (wireset : List (normalizable α pred)) (n : List (List (List (Bool × {w : normalizable α pred // w ∈ wireset})))) (o : {o : Nat // o = order wireset n}): {n : List (List (List (Bool × {w : normalizable α pred // w ∈ wireset}))) × Nat // n.2 = order wireset n.1} :=
  let sp : List (List ((List (Bool × {w : normalizable α pred // w ∈ wireset}) × Nat))) :=
  n.map (fun x => x.map (fun y => (y,
  if (n.all (fun a => a.any
  (fun b => bcompatible (y.map (fun c => (c.1,c.2.1))) (b.map (fun c => (c.1,c.2.1))))))
  then 0 else (wireset.length * 2) - y.length)));
  let so : List ((List (List (Bool × {w : normalizable α pred // w ∈ wireset}))) × Nat) :=
  sp.map (fun x => ((x.filter (fun y :
  (List (Bool × {w : normalizable α pred // w ∈ wireset})) × Nat
  => (n.all (fun a => a.any
  (fun b => bcompatible (y.1.map (fun c => (c.1,c.2.1)))
  (b.map (fun c => (c.1,c.2.1)))))))).map (fun z => z.1),(x.map (fun z => z.2)).sum));
  let s := so.map (fun x => x.1)
  let o1 : {o : Nat // o = order wireset s} := ⟨ o - ((so.map (fun x => x.2)).sum) ,(by
  obtain ⟨ o,ho⟩ := o
  simp
  rw [ho]
  apply add_of_sub
  unfold order
  unfold s
  unfold so
  unfold sp

  simp only [List.map_map, Function.comp]
  rw [sum_map_add]
  simp only [List.map_map,Function.comp]
  rw [← List.filter_map]
  --rw [← List.zip_map']
  --rw [zip_map_fst]
  --rw [zip_map_snd]
  --rw [sum_map_ite]
  --rw [sum_map_ite]
  --simp [sum_map_zero,Nat.add_zero,List.filter_filter,Bool.and_self]
  --rw [← sum_map_ite]
  --
   sorry)⟩;
  if [] ∈ s then ⟨ (s,o1.1),(by sorry)⟩
  else compatibilize wireset s (o1)
  termination_by o.1
  decreasing_by
  simp_wf
  apply Nat.sub_lt
  obtain ⟨o,ho⟩ := o
  simp
  rw [ho]
  unfold order
  simp

  sorry
  sorry

def cleano (wireset : List (normalizable α pred)) (n : List (List (List (Bool × {w : normalizable α pred // w ∈ wireset}))))   (o :{o : Nat // o = order wireset n}) : List (List (List (Bool × normalizable α pred))) :=
  let sp : List (List ((List (Bool × {w : normalizable α pred // w ∈ wireset})) × Nat)) :=
  n.map (fun x => x.map (fun y => (y,
  if ( (y.map Prod.snd).Nodup ) then 0 else (wireset.length * 2) - y.length)));
  let so : List ((List (List (Bool × {w : normalizable α pred // w ∈ wireset}))) × Nat) :=
  sp.map (fun x : List ((List (Bool × {w : normalizable α pred // w ∈ wireset})) × Nat)
  => (((x.map Prod.fst).filter
  (fun y : List (Bool × {w : normalizable α pred // w ∈ wireset})
  => (y.map Prod.snd).Nodup )),(x.map Prod.snd).sum));
  let sc : List (List (List (Bool × {w : normalizable α pred // w ∈ wireset}))) :=
  so.map Prod.fst ;
  let o1 : {o : Nat // o = order wireset sc} :=
  ⟨ o - (so.map Prod.snd).sum,(by sorry)⟩ ;
  let sco := compatibilize wireset sc o1
  let s : List (List (List (Bool × {w : normalizable α pred // w ∈ wireset}))) := sco.1.1
  let o2 := sco.1.2
  if [] ∈ s then (s.map (fun x => x.map (fun y => y.map (fun z => (z.1,z.2.1))))) else
  let fp : List (List ((List (Bool × {w : normalizable α pred // w ∈ wireset}) ) × Nat)) :=
  s.map (fun x => x.map (fun y =>
  let sf : List ((List (Bool × {w : normalizable α pred // w ∈ wireset})) × Nat) :=
  (s.map (fun a => (a.filter (fun b => bcompatible (y.map (fun c => (c.1,c.2.1)))
  (b.map (fun c => (c.1,c.2.1))))).foldr
  (fun a b => a ∩ b) (List.product [false,true] wireset.attach))).foldr
  (fun a b => ((a.filter (fun c => b.all (fun d => c ∉ d.1)),
  (a.filter (fun c => b.all (fun d => c ∉ d.1))).length) :: b)) [(y,0)] ;
  (List.flatten (sf.map Prod.fst),(sf.map Prod.snd).sum)));
  let fo : List ((List (List (Bool × {w : normalizable α pred// w ∈ wireset}))) × Nat) := fp.map (fun x => (x.map Prod.fst,(x.map Prod.snd).sum))
  cleano wireset (fo.map Prod.fst) ⟨ o - (fo.map Prod.snd).sum,(by sorry)⟩
  termination_by o
  decreasing_by
  sorry

def clean (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  cleano (n.map (fun x => (x.map (fun y => y.map (Prod.snd))).flatten)).flatten.dedup
  (n.map (fun x => x.map (fun y => y.map (fun z => (z.1,⟨z.2,(by sorry)⟩ )))))
  ⟨order  (n.map (fun x => (x.map (fun y => y.map (Prod.snd))).flatten)).flatten.dedup
  (n.map (fun x => x.map (fun y => y.map (fun z => (z.1,⟨z.2,(by sorry)⟩ ))))),(by sorry)⟩


--the fuction addclauses does the equivalent of clause learning under the assumption that it only takes at most three commitments to get a contradiction
def addclausesi  (candidates : List (List {l : List (Bool × normalizable α pred)//l ≠ []})) (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  match candidates with
  | [] => n
  | a :: as => let f := if [] ∈ clean ([(a.map (fun x => x.1)).flatten.dedup] :: n) then [] else
  (
    --add one clause, whose entries are the negations of the indexes of those of the candidate
    --assume the index of a entry is its first element
    [a.map (fun x => [(!(List.head x.1 x.2).1,(List.head x.1 x.2).2)])]
  );
  addclausesi (as.filter (
    --filter by that for which in no clause g of clean f ++ n (order f ++ n),
    --at least one entry is incompatible with each entry of g
    fun x => (clean (f ++ n)).all (fun g => g.any (fun s => bcompatible (List.flatten (x.map (fun y => y.1))) s))
  )) (f ++ n)
  termination_by candidates.length
  decreasing_by
  sorry

def addclausesj (candidates : List (List {l : (List (Bool × normalizable α pred)) // l ≠ []})) (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  let f := addclausesi candidates n
  let c := candidates.filter (
    --same condition as addclausesi
    fun x => (clean n).all (fun g => g.any (fun s => bcompatible (x.map (fun y => y.1)).flatten s))
  );
  if c.length < candidates.length then addclausesj c f else f
  termination_by candidates.length

def addclauses (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  let m : List (List {l : (List (Bool × normalizable α pred))// l ≠ []}) :=
  n.map (fun x => let z := (x.filter (fun y => y ≠ [])).attach;
  z.map (fun y  =>⟨ y.1,(by
  simp_all only [ne_eq]
  obtain ⟨val, property⟩ := y
  simp_all only
  simp_all only [ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    not_false_eq_true] )⟩ ));
  addclausesj
  (((m.sublistsLen 3).map
    (fun x =>
      (x.foldr
        (fun y z =>
          (List.product y z).map
          (fun y =>
            (y.1 :: y.2)))
        [[]]))
  ).filter
  (fun x => (clean n).all
    (fun g => g.any
      (fun s => bcompatible
        (x.map
          (fun y => y.1)).flatten s
      )) ∧
    List.all₂
    (fun y z => bcompatible y.1 z.1) x x ))
  n

--full resolution algorithm. this algorithm is complete but requires exponential time.
--i will therefore not try to prove its completeness or termination

partial def resolutioni (n : List (List (List (Bool × normalizable α pred))))(l i: Nat) : (List (List (List (Bool × normalizable α pred)))) :=
  match i with
  |0 => take l (clean n)
  |a + 1 => if take l n = take l (clean n) ∨ [] ∈ clean n
  then n
  else (resolutioni l i (fun x => x ++ ((x.sublistsLen 2).attach.filter
  (fun y => ∃! s t, s ∈ y.1.get ⟨ 0,(by aesop)⟩ ∧
   t ∈ y.1.get ⟨ 1,(by aesop)⟩ ∧
   ! bcompatible s t)).map
   (fun y => let y1 := y.1.get ⟨ 0,(by aesop)⟩;
   let y2 := y.1.get ⟨ 1,(by aesop)⟩ ;
   y1.filter (y2.all (fun z => bcompatible y1 z)) ++
   y2.filter (y1.all (fun z => bcompatible y2 z)) ))
   (resolutioni l a (clean n))).pwfilter
   (fun x y => Multiset.ofList (x.map
   (fun z => Multiset.ofList z)) = Multiset.ofList
   (y.map (fun z => Multiset.ofList z)))

partial def resolution (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  let m := addcaluses n;
  let l := m.length;
  (List.range l).foldr ((fun o x => resolutioni l x (o ++ ((x.sublistsLen 2).attach.filter
  (fun y => ∃! s t, s ∈ y.1.get ⟨ 0,(by aesop)⟩ ∧
   t ∈ y.1.get ⟨ 1,(by aesop)⟩ ∧
   ! bcompatible s t)).map
   (fun y => let y1 := y.1.get ⟨ 0,(by aesop)⟩;
   let y2 := y.1.get ⟨ 1,(by aesop)⟩ ;
   y1.filter (y2.all (fun z => bcompatible y1 z)) ++
   y2.filter (y1.all (fun z => bcompatible y2 z)) ))
   (resolutioni l a (clean n))).pwfilter
   (fun x y => Multiset.ofList (x.map
   (fun z => Multiset.ofList z)) = Multiset.ofList
   (y.map (fun z => Multiset.ofList z)))) m

theorem clean_equiv : ∀ n : List (List (List (Bool × normalizable α pred))), nToProp n <-> nToProp ( (clean n (order n))) :=
  by
  sorry

theorem clean_precondition : ∀ n : List (List (List (Bool × normalizable α pred))),
          [] ∈ ( (clean n )) ∨ ¬ (∃ g: List (List (Bool × normalizable α pred)), g ∈ (clean n ) ∧
            ∃ s : List (Bool × normalizable α pred), s ∈ g ∧
            ∃ h : List (List (Bool × normalizable α pred)),h ∈ (clean n ) ∧
            ((∃ w : Bool × normalizable α pred , w ∉ s ∧
            ∀ t ∈ h, bcompatible s t -> w ∈ t))) :=
  by
  sorry

theorem clean_subset : ∀ n : List (List (List (Bool × normalizable α pred))),[] ∉  (clean n )
           -> ∀ g ∈ List.zip n ((clean n )) , ∀ s ∈ g.2, ∃ t ∈ g.1, List.Subset t s :=
  by
  sorry

theorem seq_equiv : ∀ n : List (List (List (Bool × normalizable α pred))), ∀ g ∈ n,∀ s ∈ g,
            ∀ t : List (Bool × normalizable α pred),
            (List.Subset s t ∧ (t.map Prod.snd).Nodup ∧ (sToProp t -> nToProp n))
            <-> (∃ seq : List (List (Bool × normalizable α pred)),
            (seq.length = n.length) ∧
            (∀ u ∈ List.zip n seq, u.2 ∈ u.1) ∧
            ([] ∉ (clean (seq.map (fun x => [x])) ))
            ∧ (s ∈ seq) ∧ (∀ u ∈ seq, List.Subset u t)) :=
  by
  sorry

theorem seq_next : ∀ n : List (List (List (Bool × normalizable α pred))),
    ∀ seq : List (List (Bool × normalizable α pred)), seq.length = n.length -> (∀ u ∈ List.zip n seq, u.2 ∈ u.1) ->
    ∀ m : Fin seq.length,
     clean (((List.take (m.val + 1) seq).map (fun x => [x]))
     ++ List.drop (m.val + 1) n)
    = ((List.take (m.val + 1) seq).map (fun x => [x])) ++
       (clean ((List.drop (m.val + 1)
      ( (clean (((List.take m.val seq).map (fun x => [x]))
      ++ List.drop m.val n)))).map
      (fun x => x.filter (fun y => bcompatible (seq.get m) y)))) :=
  by
  sorry

theorem subseq_not : ∀ n : List (List (List (Bool × normalizable α pred))),
           ∀ seq : List (List (Bool × normalizable α pred)), seq.length = n.length -> (∀ u ∈ List.zip n seq, u.2 ∈ u.1) ->
           ([] ∈ clean (seq.map (fun x => [x])) ) ->
           [] ∈ clean n  ∨
           (∃ m : Fin seq.length,
           [] ∉ clean (((seq.take m.val).map (fun x => [x])) ++ n.drop m.val ) ∧
           [] ∈ clean (((seq.take (m.val + 1)).map (fun x => [x])) ++ n.drop (m.val + 1) )) :=
  by
  sorry

theorem c3 : ∀ n : List (List (List (Bool × normalizable α pred))),
             coherent n ->
            ¬ (∃ g: List (List (Bool × normalizable α pred)), g ∈ n ∧
            ∃ s : List (Bool × normalizable α pred), s ∈ g ∧
            ∃ h : List (List (Bool × normalizable α pred)),h ∈ n ∧
            ((∃ w : Bool × normalizable α pred , w ∉ s ∧
            ∀ t ∈ h, bcompatible s t -> w ∈ t) ∨ ¬(∃ t ∈ h, bcompatible s t ))) ->
            (∀ g ∈ n, ∀ s ∈ g, ∃ no : normalizable α pred, (true,no) ∈ s ∧ ∀ t ∈ g, t ≠ s -> (false, no) ∈ t ) ->
            (∀ g ∈ n, ∀ s ∈ g, ∃ t, List.Subset s t ∧ (t.map Prod.snd).Nodup ∧ (sToProp t -> nToProp n)) :=
  by
  --do induction over the length of n three times
  rw [ all_length_list (fun n =>  (coherent n ->
            ¬ (∃ g: List (List (Bool × normalizable α pred)), g ∈ n ∧
            ∃ s : List (Bool × normalizable α pred), s ∈ g ∧
            ∃ h : List (List (Bool × normalizable α pred)),h ∈ n ∧
            ((∃ w : Bool × normalizable α pred , w ∉ s ∧
            ∀ t ∈ h, bcompatible s t -> w ∈ t) ∨ ¬(∃ t ∈ h, bcompatible s t ))) ->
            (∀ g ∈ n, ∀ s ∈ g, ∃ no : normalizable α pred, (true,no) ∈ s ∧ ∀ t ∈ g, t ≠ s -> (false, no) ∈ t ) ->
            (∀ g ∈ n, ∀ s ∈ g, ∃ t, List.Subset s t ∧ (t.map Prod.snd).Nodup ∧ (sToProp t -> nToProp n))) ) ]
  intro m
  induction' m with m ih
  --at 0, the universal is vacuous
  intro n hn hccoh hneg hex g hg
  simp at hn
  rw [hn] at hg
  contradiction
  --at 1, just use the entries of g
  clear ih
  induction' m with m' ih
  intro n hn
  simp at hn
  intro hcoh hneg hex g hg
  cases' n with g tl
  contradiction
  simp at hn
  rw [hn] at hg
  have hhg := hg
  simp at hg
  rw [hg]
  intro s hs
  use s
  constructor
  exact List.Subset.refl s
  constructor
  apply hcoh
  rw [hn]
  simp
  rfl
  exact hs
  rw [hn]
  unfold nToProp
  simp
  unfold gToProp
  intro hhs
  simp
  use s
  --at 2, take the union of each entry and that of h that is bcompatible
  clear ih
  induction' m' with m'' ih
  intro n hn
  simp at hn
  intro hcoh hneg hex
  push_neg at hneg
  cases' n with g1 n1
  contradiction
  cases' n1 with g2 n2
  simp at hn
  simp at hn
  rw [hn]
  rw [hn] at hneg
  intro g hg
  have hhg : g = g1 ∨ g = g2 := by {
    simp at hg
    exact hg
  }
  cases' hhg with hg1 hg2
  intro s hs
  have hhs : s ∈ g1 := by {
    rw [hg1] at hs
    exact hs
  }
  have hcompat := hneg g hg s hs g2 (by simp)
  obtain ⟨ _,t,ht,hcompat⟩ := hcompat
  use (s ++ (t.filter (fun x => x ∉ s)))
  constructor
  intro x hx
  simp
  left
  exact hx
  constructor
  rw [←  s_nodup]
  rw [hn] at hcoh
  unfold coherent at hcoh
  have hcohs := hcoh g hg s hs
  have hcoht := hcoh g2 (by simp) t ht
  rw [← s_nodup] at hcohs
  rw [← s_nodup] at hcoht
  constructor
  simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq, and_imp]
  intro w x hw hx hsnd
  unfold bcompatible at hcompat
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    Bool.forall_bool, or_true,  Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat
  cases' hw with hw hw
  cases' hx with hx hx
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcohs
  apply hcohs.1
  exact hw
  exact hx
  exact hsnd
  apply hcompat
  exact hw
  exact hx.1
  exact hsnd
  cases' hx with hx hx
  symm
  apply hcompat
  exact hx
  exact hw.1
  rw [hsnd]
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcoht
  apply hcoht.1
  exact hw.1
  exact hx.1
  exact hsnd
  apply List.Nodup.append
  exact hcohs.2
  apply nodup_filter
  exact hcoht.2
  intro x hx hxt
  simp at hxt
  apply hxt.2
  exact hx
  intro hst
  unfold nToProp
  simp
  constructor
  unfold gToProp
  simp
  use s
  constructor
  exact hhs
  unfold sToProp at hst
  simp only [decide_not, List.all_append, List.all_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, decide_implies, dite_eq_ite, ite_not,
    Bool.if_true_left, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true] at hst
  unfold sToProp
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact hst.1
  unfold gToProp
  simp
  use t
  constructor
  exact ht
  unfold sToProp
  simp only [List.all_eq_true, decide_eq_true_eq]
  unfold sToProp at hst
  simp only [decide_not, List.all_append, List.all_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq,  dite_eq_ite, ite_not,
    Bool.if_true_left, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true] at hst
  intro x hx
  cases' Classical.em (x ∈ s) with hxs hnxs
  apply hst.1
  exact hxs
  apply hst.2
  exact hx
  exact hnxs
  intro s hs
  have hhs : s ∈ g2 := by {
    rw [hg2] at hs
    exact hs
  }
  have hcompat := hneg g hg s hs g1 (by simp)
  obtain ⟨ _,t,ht,hcompat⟩ := hcompat
  use (s ++ (t.filter (fun x => x ∉ s)))
  constructor
  intro x hx
  simp
  left
  exact hx
  constructor
  rw [←  s_nodup]
  rw [hn] at hcoh
  unfold coherent at hcoh
  have hcohs := hcoh g hg s hs
  have hcoht := hcoh g1 (by simp) t ht
  rw [← s_nodup] at hcohs
  rw [← s_nodup] at hcoht
  constructor
  simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq, and_imp]
  intro w x hw hx hsnd
  unfold bcompatible at hcompat
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    Bool.forall_bool, or_true,  Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat
  cases' hw with hw hw
  cases' hx with hx hx
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcohs
  apply hcohs.1
  exact hw
  exact hx
  exact hsnd
  apply hcompat
  exact hw
  exact hx.1
  exact hsnd
  cases' hx with hx hx
  symm
  apply hcompat
  exact hx
  exact hw.1
  rw [hsnd]
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcoht
  apply hcoht.1
  exact hw.1
  exact hx.1
  exact hsnd
  apply List.Nodup.append
  exact hcohs.2
  apply nodup_filter
  exact hcoht.2
  intro x hx hxt
  simp at hxt
  apply hxt.2
  exact hx
  intro hst
  unfold nToProp
  simp
  rw [and_comm]
  constructor
  unfold gToProp
  simp
  use s
  constructor
  exact hhs
  unfold sToProp at hst
  simp only [decide_not, List.all_append, List.all_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, decide_implies, dite_eq_ite, ite_not,
    Bool.if_true_left, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true] at hst
  unfold sToProp
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact hst.1
  unfold gToProp
  simp
  use t
  constructor
  exact ht
  unfold sToProp
  simp only [List.all_eq_true, decide_eq_true_eq]
  unfold sToProp at hst
  simp only [decide_not, List.all_append, List.all_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq,  dite_eq_ite, ite_not,
    Bool.if_true_left, Bool.and_eq_true, List.all_eq_true,
    Bool.or_eq_true] at hst
  intro x hx
  cases' Classical.em (x ∈ s) with hxs hnxs
  apply hst.1
  exact hxs
  apply hst.2
  exact hx
  exact hnxs
  clear ih
  induction' m'' with m''' ih
  intro n hn
  --at 3,
    -- show that if an entry s ∈ g is compatible with t ∈ h, the element of t assured by hex, with its fst false, is not in s, this is an equivalence.
    -- then for that (true, w) from s, (false, w) would not be in t, ergo (applying hneg) there is a entry u in a third compatible with t also without (false, w),
    -- and u would also be compatible with s
  cases' n with g1 n1
  contradiction
  cases' n1 with g2 n2
  simp at hn
  cases' n2 with g3 n3
  simp at hn
  simp [List.length] at hn
  rw [hn]
  intro hcoh hneg hex g hg s hs
  simp at hg
  push_neg at hneg
  cases' hg with hg1 hg
  unfold coherent at hcoh
  have hcohs := hcoh g (by rw [hg1];simp) s hs
  rw [← s_nodup] at hcohs
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcohs
  rw [hg1] at hs
  have hex_t := hex g1 (by simp) s hs
  obtain ⟨ w,hw_true,hw_false⟩ := hex_t
  have h_compat_equiv : ∀ h ∈ [g1, g2, g3], ∀ t ∈ h, bcompatible s t <->  (false,w) ∉ t := by {
    intro h hh t ht
    constructor
    intro hcomp
    intro hcontra
    unfold bcompatible at hcomp
    simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hcomp
    have hcontra' := hcomp (true,w) hw_true (false,w) hcontra (by simp)
    contradiction
    contrapose!
    intro hb
    have h_compatible_entries : ∀ u ∈ g, bcompatible u t -> (false,w) ∈ u := by {
      intro u hu hcomp_u
      cases' Classical.em (u = s) with heqs hneqs
      rw [heqs] at hcomp_u
      contradiction
      rw [hg1] at hu
      exact hw_false u hu hneqs
    }
    by_contra hnt
    have hnegt := (hneg h hh t ht g (by rw [hg1];simp)).1 (false,w) hnt
    obtain ⟨ u,hu,hcompatu,huf⟩ := hnegt
    rw [bcompatible_symm] at hcompatu
    have hcontra := h_compatible_entries u hu hcompatu
    contradiction
  }
  have ht := (hneg g1 (by simp) s hs g2 (by simp)).2
  obtain ⟨ t,ht,hht⟩ := ht
  let t2 := s ++ (t.filter (fun x => x ∉ s))
  have h_not_in_t := (h_compat_equiv g2 (by simp) t ht).1 hht
  have h_compat3 := (hneg g2 (by simp) t ht g3 (by simp)).1 (false, w) h_not_in_t
  obtain ⟨ t3,ht3, hcompat3, h_not_in_t3⟩ := h_compat3
  have hcompat13 := (h_compat_equiv g3 (by simp) t3 ht3).2 h_not_in_t3
  use t2 ++ (t3.filter (fun x => x ∉ t2))
  have ht2e :  t2 = s ++ (t.filter (fun x => x ∉ s)) := by {
    dsimp
  }
  constructor
  intro x hx
  rw [ht2e]
  simp
  left
  exact hx
  constructor
  rw [ht2e]
  rw [← s_nodup]
  simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, not_or, not_and, Decidable.not_not, Bool.decide_and,
    dite_eq_ite, Bool.if_true_right, List.append_assoc, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq, and_imp,  implies_true,
    Bool.false_eq_true, imp_false, true_and, Bool.true_eq_false, and_true]
  have hcoht := hcoh g2 (by simp) t ht
  rw [← s_nodup] at hcoht
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcoht
  have hcoht3 := hcoh g3 (by simp) t3 ht3
  rw [← s_nodup] at hcoht3
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcoht3
  constructor
  intro w x hw hx hwx
  cases' hw with hw1 hw2
  cases' hx with hx1 hx2
  apply hcohs.1
  exact hw1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  unfold bcompatible at hht
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hht
  apply hht
  exact hw1
  exact hx2.1
  exact hwx
  unfold bcompatible at hcompat13
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat13
  apply hcompat13
  exact hw1
  exact hx3.1
  exact hwx
  cases' hw2 with hw2 hw3
  cases' hx with hx1 hx2
  rw [bcompatible_symm] at hht
  unfold bcompatible at hht
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hht
  apply hht
  exact hw2.1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  apply hcoht.1
  exact hw2.1
  exact hx2.1
  exact hwx
  unfold bcompatible at hcompat3
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat3
  apply hcompat3
  exact hw2.1
  exact hx3.1
  exact hwx
  cases' hx with hx1 hx2
  rw [bcompatible_symm] at hcompat13
  unfold bcompatible at hcompat13
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat13
  apply hcompat13
  exact hw3.1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  rw [bcompatible_symm] at hcompat3
  unfold bcompatible at hcompat3
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat3
  apply hcompat3
  exact hw3.1
  exact hx2.1
  exact hwx
  apply hcoht3.1
  exact hw3.1
  exact hx3.1
  exact hwx
  simp
  rw [List.nodup_append]
  constructor
  exact hcohs.2
  simp
  constructor
  rw [List.nodup_append]
  constructor
  apply nodup_filter
  exact hcoht.2
  constructor
  apply nodup_filter
  exact hcoht3.2
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, imp_false, not_and, not_or, Decidable.not_not, and_imp]
  intro x hx hhx hhhx hhhhx
  constructor
  exact hx
  exact hhx
  constructor
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, imp_false, not_and,
    Decidable.not_not]
  intro x hx hhx
  exact hx
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.or_eq_true, decide_eq_true_eq, imp_false, not_and, Decidable.not_not]
  intro x hx hhx hhhx hhhhx
  cases hhhhx
  contradiction
  contradiction
  rw [ht2e]
  unfold sToProp
  simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, not_or, not_and, Decidable.not_not, Bool.decide_and,
    dite_eq_ite, Bool.if_true_right, List.append_assoc, List.all_append, List.all_filter,
    decide_eq_true_eq, ite_not, Bool.if_true_left, Bool.and_eq_true, Bool.or_eq_true, and_imp,
    Bool.decide_or, Bool.not_or, Bool.not_not, List.all_eq_true]
  intro hx hy hz
  unfold nToProp
  simp
  unfold gToProp
  simp
  unfold sToProp
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  use s
  constructor
  use t
  constructor
  exact ht
  intro x hhx
  cases' Classical.em (x ∈ s) with hhhx hnx
  apply hx
  exact hhhx
  apply hy
  exact hhx
  exact hnx
  use t3
  constructor
  exact ht3
  intro x hhx
  cases' Classical.em (x ∈ s ∨ x ∈ t) with hst hnst
  cases' Classical.em (x ∈ s) with his hnis
  apply hx
  exact his
  cases' hst with his hit
  contradiction
  apply hy
  exact hit
  exact hnis
  simp at hnst
  apply hz
  exact hhx
  exact hnst.1
  intro hxt
  exfalso
  apply hnst.2
  exact hxt
  --case g2
  cases' hg with hg2 hg3
  unfold coherent at hcoh
  have hcohs := hcoh g (by rw [hg2];simp) s hs
  rw [← s_nodup] at hcohs
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcohs
  rw [hg2] at hs
  have hex_t := hex g2 (by simp) s hs
  obtain ⟨ w,hw_true,hw_false⟩ := hex_t
  have h_compat_equiv : ∀ h ∈ [g1, g2, g3], ∀ t ∈ h, bcompatible s t <->  (false,w) ∉ t := by {
    intro h hh t ht
    constructor
    intro hcomp
    intro hcontra
    unfold bcompatible at hcomp
    simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hcomp
    have hcontra' := hcomp (true,w) hw_true (false,w) hcontra (by simp)
    contradiction
    contrapose!
    intro hb
    have h_compatible_entries : ∀ u ∈ g, bcompatible u t -> (false,w) ∈ u := by {
      intro u hu hcomp_u
      cases' Classical.em (u = s) with heqs hneqs
      rw [heqs] at hcomp_u
      contradiction
      rw [hg2] at hu
      exact hw_false u hu hneqs
    }
    by_contra hnt
    have hnegt := (hneg h hh t ht g (by rw [hg2];simp)).1 (false,w) hnt
    obtain ⟨ u,hu,hcompatu,huf⟩ := hnegt
    rw [bcompatible_symm] at hcompatu
    have hcontra := h_compatible_entries u hu hcompatu
    contradiction
  }
  have ht := (hneg g2 (by simp) s hs g1 (by simp)).2
  obtain ⟨ t,ht,hht⟩ := ht
  let t2 := s ++ (t.filter (fun x => x ∉ s))
  have h_not_in_t := (h_compat_equiv g1 (by simp) t ht).1 hht
  have h_compat3 := (hneg g1 (by simp) t ht g3 (by simp)).1 (false, w) h_not_in_t
  obtain ⟨ t3,ht3, hcompat3, h_not_in_t3⟩ := h_compat3
  have hcompat13 := (h_compat_equiv g3 (by simp) t3 ht3).2 h_not_in_t3
  use t2 ++ (t3.filter (fun x => x ∉ t2))
  have ht2e :  t2 = s ++ (t.filter (fun x => x ∉ s)) := by {
    dsimp
  }
  constructor
  intro x hx
  rw [ht2e]
  simp
  left
  exact hx
  constructor
  rw [ht2e]
  rw [← s_nodup]
  simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, not_or, not_and, Decidable.not_not, Bool.decide_and,
    dite_eq_ite, Bool.if_true_right, List.append_assoc, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq, and_imp,  implies_true,
    Bool.false_eq_true, imp_false, true_and, Bool.true_eq_false, and_true]
  have hcoht := hcoh g1 (by simp) t ht
  rw [← s_nodup] at hcoht
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcoht
  have hcoht3 := hcoh g3 (by simp) t3 ht3
  rw [← s_nodup] at hcoht3
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcoht3
  constructor
  intro w x hw hx hwx
  cases' hw with hw1 hw2
  cases' hx with hx1 hx2
  apply hcohs.1
  exact hw1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  unfold bcompatible at hht
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hht
  apply hht
  exact hw1
  exact hx2.1
  exact hwx
  unfold bcompatible at hcompat13
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat13
  apply hcompat13
  exact hw1
  exact hx3.1
  exact hwx
  cases' hw2 with hw2 hw3
  cases' hx with hx1 hx2
  rw [bcompatible_symm] at hht
  unfold bcompatible at hht
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hht
  apply hht
  exact hw2.1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  apply hcoht.1
  exact hw2.1
  exact hx2.1
  exact hwx
  unfold bcompatible at hcompat3
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat3
  apply hcompat3
  exact hw2.1
  exact hx3.1
  exact hwx
  cases' hx with hx1 hx2
  rw [bcompatible_symm] at hcompat13
  unfold bcompatible at hcompat13
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat13
  apply hcompat13
  exact hw3.1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  rw [bcompatible_symm] at hcompat3
  unfold bcompatible at hcompat3
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat3
  apply hcompat3
  exact hw3.1
  exact hx2.1
  exact hwx
  apply hcoht3.1
  exact hw3.1
  exact hx3.1
  exact hwx
  simp
  rw [List.nodup_append]
  constructor
  exact hcohs.2
  simp
  constructor
  rw [List.nodup_append]
  constructor
  apply nodup_filter
  exact hcoht.2
  constructor
  apply nodup_filter
  exact hcoht3.2
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, imp_false, not_and, not_or, Decidable.not_not, and_imp]
  intro x hx hhx hhhx hhhhx
  constructor
  exact hx
  exact hhx
  constructor
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, imp_false, not_and,
    Decidable.not_not]
  intro x hx hhx
  exact hx
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.or_eq_true, decide_eq_true_eq, imp_false, not_and, Decidable.not_not]
  intro x hx hhx hhhx hhhhx
  cases hhhhx
  contradiction
  contradiction
  rw [ht2e]
  unfold sToProp
  simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, not_or, not_and, Decidable.not_not, Bool.decide_and,
    dite_eq_ite, Bool.if_true_right, List.append_assoc, List.all_append, List.all_filter,
    decide_eq_true_eq, ite_not, Bool.if_true_left, Bool.and_eq_true, Bool.or_eq_true, and_imp,
    Bool.decide_or, Bool.not_or, Bool.not_not, List.all_eq_true]
  intro hx hy hz
  unfold nToProp
  simp
  unfold gToProp
  simp
  unfold sToProp
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  swap
  constructor
  use s
  swap
  use t
  constructor
  exact ht
  intro x hhx
  cases' Classical.em (x ∈ s) with hhhx hnx
  apply hx
  exact hhhx
  apply hy
  exact hhx
  exact hnx
  use t3
  constructor
  exact ht3
  intro x hhx
  cases' Classical.em (x ∈ s ∨ x ∈ t) with hst hnst
  cases' Classical.em (x ∈ s) with his hnis
  apply hx
  exact his
  cases' hst with his hit
  contradiction
  apply hy
  exact hit
  exact hnis
  simp at hnst
  apply hz
  exact hhx
  exact hnst.1
  intro hxt
  exfalso
  apply hnst.2
  exact hxt
  --case g3
  unfold coherent at hcoh
  have hcohs := hcoh g (by rw [hg3];simp) s hs
  rw [← s_nodup] at hcohs
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcohs
  rw [hg3] at hs
  have hex_t := hex g3 (by simp) s hs
  obtain ⟨ w,hw_true,hw_false⟩ := hex_t
  have h_compat_equiv : ∀ h ∈ [g1, g2, g3], ∀ t ∈ h, bcompatible s t <->  (false,w) ∉ t := by {
    intro h hh t ht
    constructor
    intro hcomp
    intro hcontra
    unfold bcompatible at hcomp
    simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hcomp
    have hcontra' := hcomp (true,w) hw_true (false,w) hcontra (by simp)
    contradiction
    contrapose!
    intro hb
    have h_compatible_entries : ∀ u ∈ g, bcompatible u t -> (false,w) ∈ u := by {
      intro u hu hcomp_u
      cases' Classical.em (u = s) with heqs hneqs
      rw [heqs] at hcomp_u
      contradiction
      rw [hg3] at hu
      exact hw_false u hu hneqs
    }
    by_contra hnt
    have hnegt := (hneg h hh t ht g (by rw [hg3];simp)).1 (false,w) hnt
    obtain ⟨ u,hu,hcompatu,huf⟩ := hnegt
    rw [bcompatible_symm] at hcompatu
    have hcontra := h_compatible_entries u hu hcompatu
    contradiction
  }
  have ht := (hneg g3 (by simp) s hs g2 (by simp)).2
  obtain ⟨ t,ht,hht⟩ := ht
  let t2 := s ++ (t.filter (fun x => x ∉ s))
  have h_not_in_t := (h_compat_equiv g2 (by simp) t ht).1 hht
  have h_compat3 := (hneg g2 (by simp) t ht g1 (by simp)).1 (false, w) h_not_in_t
  obtain ⟨ t3,ht3, hcompat3, h_not_in_t3⟩ := h_compat3
  have hcompat13 := (h_compat_equiv g1 (by simp) t3 ht3).2 h_not_in_t3
  use t2 ++ (t3.filter (fun x => x ∉ t2))
  have ht2e :  t2 = s ++ (t.filter (fun x => x ∉ s)) := by {
    dsimp
  }
  constructor
  intro x hx
  rw [ht2e]
  simp
  left
  exact hx
  constructor
  rw [ht2e]
  rw [← s_nodup]
  simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, not_or, not_and, Decidable.not_not, Bool.decide_and,
    dite_eq_ite, Bool.if_true_right, List.append_assoc, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq, and_imp,  implies_true,
    Bool.false_eq_true, imp_false, true_and, Bool.true_eq_false, and_true]
  have hcoht := hcoh g2 (by simp) t ht
  rw [← s_nodup] at hcoht
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcoht
  have hcoht3 := hcoh g1 (by simp) t3 ht3
  rw [← s_nodup] at hcoht3
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcoht3
  constructor
  intro w x hw hx hwx
  cases' hw with hw1 hw2
  cases' hx with hx1 hx2
  apply hcohs.1
  exact hw1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  unfold bcompatible at hht
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hht
  apply hht
  exact hw1
  exact hx2.1
  exact hwx
  unfold bcompatible at hcompat13
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat13
  apply hcompat13
  exact hw1
  exact hx3.1
  exact hwx
  cases' hw2 with hw2 hw3
  cases' hx with hx1 hx2
  rw [bcompatible_symm] at hht
  unfold bcompatible at hht
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hht
  apply hht
  exact hw2.1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  apply hcoht.1
  exact hw2.1
  exact hx2.1
  exact hwx
  unfold bcompatible at hcompat3
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat3
  apply hcompat3
  exact hw2.1
  exact hx3.1
  exact hwx
  cases' hx with hx1 hx2
  rw [bcompatible_symm] at hcompat13
  unfold bcompatible at hcompat13
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat13
  apply hcompat13
  exact hw3.1
  exact hx1
  exact hwx
  cases' hx2 with hx2 hx3
  rw [bcompatible_symm] at hcompat3
  unfold bcompatible at hcompat3
  simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
     or_true, implies_true, Bool.false_eq_true, or_false, true_and,
    Bool.true_eq_false, and_true] at hcompat3
  apply hcompat3
  exact hw3.1
  exact hx2.1
  exact hwx
  apply hcoht3.1
  exact hw3.1
  exact hx3.1
  exact hwx
  simp
  rw [List.nodup_append]
  constructor
  exact hcohs.2
  simp
  constructor
  rw [List.nodup_append]
  constructor
  apply nodup_filter
  exact hcoht.2
  constructor
  apply nodup_filter
  exact hcoht3.2
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, imp_false, not_and, not_or, Decidable.not_not, and_imp]
  intro x hx hhx hhhx hhhhx
  constructor
  exact hx
  exact hhx
  constructor
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not, imp_false, not_and,
    Decidable.not_not]
  intro x hx hhx
  exact hx
  unfold List.Disjoint
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.or_eq_true, decide_eq_true_eq, imp_false, not_and, Decidable.not_not]
  intro x hx hhx hhhx hhhhx
  cases hhhhx
  contradiction
  contradiction
  rw [ht2e]
  unfold sToProp
  simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, not_or, not_and, Decidable.not_not, Bool.decide_and,
    dite_eq_ite, Bool.if_true_right, List.append_assoc, List.all_append, List.all_filter,
    decide_eq_true_eq, ite_not, Bool.if_true_left, Bool.and_eq_true, Bool.or_eq_true, and_imp,
    Bool.decide_or, Bool.not_or, Bool.not_not, List.all_eq_true]
  intro hx hy hz
  unfold nToProp
  simp
  unfold gToProp
  simp
  unfold sToProp
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  swap
  constructor
  swap
  use s
  use t
  constructor
  exact ht
  intro x hhx
  cases' Classical.em (x ∈ s) with hhhx hnx
  apply hx
  exact hhhx
  apply hy
  exact hhx
  exact hnx
  use t3
  constructor
  exact ht3
  intro x hhx
  cases' Classical.em (x ∈ s ∨ x ∈ t) with hst hnst
  cases' Classical.em (x ∈ s) with his hnis
  apply hx
  exact his
  cases' hst with his hit
  contradiction
  apply hy
  exact hit
  exact hnis
  simp at hnst
  apply hz
  exact hhx
  exact hnst.1
  intro hxt
  exfalso
  apply hnst.2
  exact hxt
  --at m + 3,
  --show that in gates a b and c, if s ∈ a ∪ t ∈ b is not compatible with any u ∈ c,
  -- index s is false in t.this is similar to what we did in case 3
  --let n4 be n1 with the every t compatible with s, unioned with s and one round of the algorithm applied (and spell it out)
  --show it satisfies the preconditions,
  --and that the candidate solutions solve n
  intro n hn hcoh hneg hex
  cases' n with g1 n1
  contradiction
  intro g hg s hs
  push_neg at hneg
  have hs1 : ∃ s1 ∈ g1, bcompatible s s1 := by {
    have hss := hneg g hg s hs g1 (by simp)
    obtain ⟨ hss1,hss2⟩ := hss
    exact hss2
  }
  obtain ⟨ s1,hs11,hss1⟩ := hs1
  have hex_s1 := hex g1 (by simp) s1 hs11
  obtain ⟨ index_s1,hindex_s1_true,hindex_s1_false⟩ := hex_s1
  have h_compat_equiv : ∀ h ∈ (g1 :: n1), ∀ t ∈ h, bcompatible s1 t <-> (false, index_s1) ∉ t := by {
    intro h hh t ht
    constructor
    intro hcomp hcontra
    unfold bcompatible at hcomp
    simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hcomp
    have hcontran := hcomp (true, index_s1) hindex_s1_true (false, index_s1) hcontra (by simp)
    contradiction
    contrapose!
    intro hb
    have hcompatible_entries : ∀ w ∈ g1, bcompatible w t -> (false, index_s1) ∈ w := by {
      intro w hw hcomp_w
      cases' Classical.em (w = s1) with heqs hneqs
      rw [heqs] at hcomp_w
      contradiction
      exact hindex_s1_false w hw hneqs
    }
    by_contra hnt
    have hnegt := (hneg h hh t ht g1 (by simp)).1 (false, index_s1) hnt
    obtain ⟨ w, hw, hcompatu, hwf⟩ := hnegt
    rw [bcompatible_symm] at hcompatu
    have hcontra := hcompatible_entries w hw hcompatu
    contradiction
  }
  have h_compat3n : ∀ b ∈ (g1 :: n1), ∀ c ∈ (g1 :: n1), ∀ u ∈ b, bcompatible s1 u ->
     ∃ t ∈ c, bcompatible s1 t ∧ bcompatible u t := by {
    intro b hb c hc t ht hcompat
    have h_not_in_t := (h_compat_equiv b hb t ht).1 hcompat
    have h_compat3 := (hneg b hb t ht c hc).1 (false, index_s1) h_not_in_t
    obtain ⟨t3,ht3,hcompat3,h_not_in_t3⟩ := h_compat3
    have hcompat13 := (h_compat_equiv c hc t3 ht3).2 h_not_in_t3
    use t3
  }
  have h_false_index : ∀ b ∈ (g1 :: n1),∀ c ∈ (g1 :: n1), ∀ u ∈ b,
    bcompatible s1 u -> (∀ v ∈ c, ¬ bcompatible (s1 ++ u.filter (fun x => x ∉ s1)) v) ->
    (false, index_s1) ∈ u := by {
    intro b hb c hc t ht hcompat hnot_comp
    by_contra hnf
    have h_not_in_t := (h_compat_equiv b hb t ht).1 hcompat
    have h_compat3 := (hneg b hb t ht c hc).1 (false, index_s1) h_not_in_t
    obtain ⟨t3,ht3,hcompat3,h_not_in_t3⟩ := h_compat3
    have hcompat13 := (h_compat_equiv c hc t3 ht3).2 h_not_in_t3
    apply hnot_comp t3 ht3
    apply bcompatible_union
    exact hcompat13
    exact hcompat3
  }
  let n4_pre := (n1.map (fun x => (x.filter (fun y => bcompatible s1 y)).map (fun y => s1 ++ y.filter (fun z => z ∉ s1))))
  have hn4_pre : n4_pre = (n1.map (fun x => (x.filter (fun y => bcompatible s1 y)).map (fun y => s1 ++ y.filter (fun z => z ∉ s1)))) := by {
    dsimp
  }
  let n4 := (n4_pre.map (fun t =>
  (t.filter (fun w => n4_pre.all (fun u => u.any (fun v => bcompatible v w)))))).map (fun t => t.map
  (fun r => ((n4_pre.map
  (fun p => (p.filter (fun v => bcompatible v r)))).map
  (fun w => interl (w.filter (fun v => bcompatible v r)))).foldr
  (fun u v => u ++ v.filter (fun x => x ∉ u)) r))
  have hn4 : n4 = (n4_pre.map (fun t =>
  (t.filter (fun w => n4_pre.all (fun u => u.any (fun v => bcompatible v w)))))).map (fun t => t.map
  (fun r => ((n4_pre.map
  (fun p => (p.filter (fun v => bcompatible v r)))).map
  (fun w => interl (w.filter (fun v => bcompatible v r)))).foldr
  (fun u v => u ++ v.filter (fun x => x ∉ u)) r)) := by {
    dsimp
  }
  have hfe : n4_pre.map (fun t => t.filter (fun w => n4_pre.all (fun u => u.any (fun v => bcompatible v w)))) = n4_pre := by {
    rw [hn4_pre]
    simp only [ List.all_map, List.map_map, List.map_inj_left, Function.comp_apply,
      List.filter_eq_self, List.mem_map, List.mem_filter, List.all_eq_true, List.any_map,
      List.any_filter, List.any_eq_true, Bool.and_eq_true, forall_exists_index, and_imp]
    intro g hg s t ht hst hsu h hh
    have hcompats := h_compat3n g (by right; exact hg) h (by right; exact hh) t ht hst
    obtain ⟨ u,hu, hcompats1,hcompats2⟩ := hcompats
    use u
    constructor
    exact hu
    constructor
    exact hcompats1
    rw [← hsu]
    rw [bcompatible_symm] at hst
    have hc1 := bcompatible_union s1 t s1 (bcompatible_self s1 (hcoh g1 (by simp) s1 hs11)) hst
    rw [bcompatible_symm] at hc1
    have hcompats := bcompatible_union s1 t u  hcompats1 hcompats2
    rw [bcompatible_symm] at hcompats
    exact bcompatible_union s1 u (s1 ++ List.filter (fun x ↦ decide (x ∉ s1)) t) hc1 hcompats
  }
  have h_n4_coherent : coherent n4 := by {
    unfold coherent
    intro g hg s hs
    rw [hn4] at hg
    rw [hfe] at hg
    rw [hn4_pre] at hg
    simp only [List.mem_map] at hg
    obtain ⟨ x,hx,rfl⟩ := hg
    simp only [List.mem_map] at hs
    obtain ⟨ y,hy,hhy⟩ := hs
    rw [← hhy]
    apply nodup_fold2
    obtain ⟨ xo,hxo,hhxo⟩ := hx
    rw [← hhxo] at hy
    simp only [List.mem_map] at hy
    obtain ⟨yo,hyo,hhyo⟩ := hy
    rw [List.mem_filter] at hyo
    obtain ⟨ hy_orig, hcompat_y⟩ := hyo
    have hcoh_s1 := hcoh g1 (by simp) s1 hs11
    have hcoh_y := hcoh xo (by right;exact hxo) yo hy_orig
    rw [← s_nodup] at hcoh_s1 hcoh_y
    rw [← hhyo]
    rw [← s_nodup]
    constructor
    simp only [decide_not, List.mem_append, List.mem_filter, Bool.not_eq_true',
      decide_eq_false_iff_not, beq_iff_eq, and_imp]
    simp only [beq_iff_eq, and_imp,  Bool.forall_bool, implies_true, Bool.false_eq_true,
      imp_false, true_and, Bool.true_eq_false, and_true] at hcoh_s1
    intro w v hw hv hwv
    cases' hw with hws hwy
    cases' hv with hvs hvy
    apply hcoh_s1.1
    exact hws
    exact hvs
    exact hwv
    unfold bcompatible at hcompat_y
    simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hcompat_y
    apply hcompat_y
    exact hws
    exact hvy.1
    exact hwv
    cases' hv with hvs hvy
    unfold bcompatible at hcompat_y
    simp only [beq_iff_eq,  dite_eq_ite, Bool.if_true_right, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
       or_true, implies_true, Bool.false_eq_true, or_false, true_and,
      Bool.true_eq_false, and_true] at hcompat_y
    symm
    apply hcompat_y
    exact hvs
    exact hwy.1
    symm
    exact hwv
    simp only [beq_iff_eq, and_imp] at hcoh_y
    apply hcoh_y.1
    exact hwy.1
    exact hvy.1
    exact hwv
    rw [List.nodup_append]
    constructor
    exact hcoh_s1.2
    constructor
    apply nodup_filter
    exact hcoh_y.2
    unfold List.Disjoint
    intro x hx hx_filter
    simp at hx_filter
    exact hx_filter.2 hx
    intro x' hx'
    simp only [ List.map_map, List.mem_map, Function.comp_apply, List.filter_filter,
      and_self, Bool.decide_eq_true] at hx'
    obtain ⟨ xo,hxo,hhxo⟩ := hx'
    rw [← hhxo]
    apply interl_all_nodup
    simp only [ List.mem_filter, List.mem_map, and_imp, forall_exists_index]
    intro m x hx hsx hs1x hmy
    rw [← hs1x]
    rw [← hs1x] at hmy
    rw [bcompatible_union_equiv] at hmy
    apply bcompatible_union_nodup
    exact hsx
    exact hcoh g1 (by simp) s1 hs11
    exact hcoh xo (by right; exact hxo) x hx
    intro x' hx'
    simp only [List.map_map] at hx'
    rw [List.mem_map] at hx'
    obtain ⟨ xo,hxo,hhxo⟩ := hx'
    rw [← hhxo]
    apply interl_all_bcompatible
    simp
    intro a b hb hsb hsub hayb
    rw [bcompatible_symm]
    exact hayb
    intro x' hx' y' hy'
    simp only [List.map_map] at hx'
    rw [List.mem_map] at hx'
    obtain ⟨ xo,hxo,hhxo⟩ := hx'
    rw [← hhxo]
    simp only [List.map_map] at hy'
    rw [List.mem_map] at hy'
    obtain ⟨ yo,hyo,hhyo⟩ := hy'
    rw [← hhyo]

  }
  have hnegn4 : ¬(∃ g ∈ n4, ∃ s ∈ g, ∃ h ∈ n4,
      (∃ w ∉ s, ∀ t ∈ h, bcompatible s t -> w ∈ t) ∨
      ¬ (∃ t ∈ h, bcompatible s t)) := by {
    push_neg
    rw [hn4]
    rw [hfe]
    rw [hn4_pre]
    intro g hg s hs h hh
    rw [List.mem_map] at hh
    obtain ⟨ ho, hho,hhe⟩ := hh
    rw [List.mem_map] at hg
    obtain ⟨ go,hgo,hge⟩ := hg
    rw [← hge] at hs
    rw [List.mem_map] at hs
    obtain ⟨so,hso,hse⟩ := hs


  }
  have hexn4 : ∀ g ∈ n4,∀ s ∈ g, ∃ no, (true, no) ∈ s ∧
              ∀ t ∈ g, t ≠ s -> (false, no) ∈ t := by {
    sorry
  }
  have hnn4 : List.length n4 = m''' + 1 + 1 + 1 := by {
    sorry
  }
  have houtn4 := ih n4 hnn4 h_n4_coherent hnegn4 hexn4
  sorry





theorem leneqclean :  ∀ n : List (List (List (Bool × normalizable α pred))), (clean n ).length = n.length :=
  by
  intro n
  unfold clean
  simp
  have hm : List.length (makeCoherent n) = List.length n := by {
    unfold makeCoherent
    simp
  }
  exact hm
  intro n
  unfold clean
  simp
  cases' Classical.em (order (makeCoherent n) ≤
         order
    (if [] ∈ makeCoherent n then makeCoherent n
            else
              List.map
                ((fun t ↦
                    List.map
                      (fun r ↦
                        List.foldr (fun u v ↦ u.union v) r
                          (List.map
                            ((fun w ↦
                                List.filter (fun x ↦ !decide (x ∈ r))
                                  (interl (List.filter (fun v ↦ bcompatible v r) w))) ∘
                              fun p ↦ List.filter (fun v ↦ bcompatible v r) p)
                            (List.filter (fun u ↦ !decide (u = t)) (makeCoherent n))))
                      t) ∘
                  fun t ↦ List.filter (fun w ↦ (makeCoherent n).all fun u ↦ u.any fun v ↦ bcompatible v w) t)
                (makeCoherent n))) with hord hnord
  rw [if_pos]
  have hm : List.length (makeCoherent n) = List.length n := by {
    unfold makeCoherent
    simp
  }
  apply ho at n
  exact hm
  convert hord
  rw [if_neg]
  rw [ho]
  cases' Classical.em ([] ∈ makeCoherent n) with hmc hnmc
  rw [if_pos]
  have hm : List.length (makeCoherent n) = List.length n := by {
    unfold makeCoherent
    simp
  }
  exact hm
  exact hmc
  rw [if_neg]
  simp
  have hm : List.length (makeCoherent n) = List.length n := by {
    unfold makeCoherent
    simp
  }
  exact hm
  exact hnmc
  exact hnord

def solutions (o : normalizable α pred) : List (List (List (Bool × normalizable α pred))) :=
  clean (makeCoherent (normalizel o)) (order (normalizel o))

def satisfiable? (o : normalizable α pred)  : Bool :=
  [] ∉ solutions o

def lsatisfiable? (n : List (List (List (Bool × normalizable α pred)))) : Bool :=
  [] ∉ clean n (order n)

 def chose (n : List (List (List (Bool × normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  match n with
  | [] => []
  | [[]] => []
  | ([] :: _) => []
  | (b :: _) :: as => let s := clean ([b] :: as) (order ([b] :: as)); if [] ∉ s then ([b] :: chose s.tail)  else []
  termination_by List.length n
  decreasing_by
  have hl : List.length (clean ([b] :: as) (order ([b] :: as))) = List.length ([b] :: as) :=
  by
  {apply leneqclean}
  simp_wf
  rw [hl]
  simp


def getS (o : List (List (List (Bool × normalizable α pred)))) : List (Bool × normalizable α pred) :=
  match o with
  | [] => []
  | [] :: _ => []
  | (b :: _) :: bs => (b.append (getS bs)).dedup

 def solveWhole (o : normalizable α pred) : List (Bool × normalizable α pred) :=
  getS (chose (solutions o))

 def lsolvewhole (n : List (List (List (Bool × normalizable α pred)))) : List (Bool × normalizable α pred) :=
  getS (chose (clean n (order n)))

--theorem solveSound : ∀ n : normalizable α pred, satisfiable? n == false -> ¬ toProp n :=
--  by
--  sorry

--theorem lsolvesound : ∀ n : List (List (List (Bool × normalizable α pred))), lsatisfiable? n == false -> ¬(nToProp n) :=
--  by
--  sorry

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

--theorem solveComplete : ∀ n : normalizable α pred, satisfiable? n == true ->
--                        ∃ s : List (Bool × normalizable α pred), List.Subset (s.map snd) (atoms n) ∧ (s ≠ []) ∧
--                        sToProp s -> toProp n :=
--  by
--  intro n
--  intro
--  use (solveAtoms n)
  --take it from here
--  sorry

--same thing here
--theorem lsolvecomplete : ∀ n : List (List (List (Bool × normalizable α pred))), lsatisfiable? n == true ->
--                     ∃ s : List (Bool × normalizable α pred),
--                     (∀ w: Bool × normalizable α pred, w ∈ s -> isAtom w.snd)  ∧ (s ≠ []) ∧
--                     sToProp s -> nToProp n :=
--  by
--  sorry

 def nextSolution (s : List (Bool × normalizable α pred)) (n : List (List (List (Bool × normalizable α pred))))
                   : (List (Bool × normalizable α pred)  ×    List (List (List (Bool × normalizable α pred)))) :=
  let m := (s.map (fun x => [(!x.fst,x.snd)])) :: n;
  ((lsolveatoms (m)),m)
