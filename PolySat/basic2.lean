import Init.Data.List
import Init.PropLemmas
import Mathlib.Algebra.BigOperators.Group.List
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
import Batteries.Data.List.Lemmas
import Batteries.Data.List.Basic
import Aesop
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

--@[simp]
@[reducible]
def nStrip (n : normalizable α pred) : Bool × normalizable α pred :=
  match n with
  | Not i =>  (false,i)
  | i => (true,i)

def booleanize (n : List (List (List (normalizable α pred)))) : List (List (List (Bool × normalizable α pred))) :=
  n.map (fun x => x.map (fun y => y.map (fun z => nStrip z)))

def normalizel (n : normalizable α pred) : List (List (List (Bool × normalizable α pred))) :=
  booleanize (normalize n)

@[aesop 50% unfold]
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

--@[simp]
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
  --aesop?
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

theorem subnormal : ∀ n : normalizable α pred, fToProp (subnormalize n) :=
  by
  intro n
  induction' n with a b c d e f g i j k l
  unfold subnormalize
  unfold fToProp
  simp
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
  simp at hnodup
  obtain ⟨ hhd, _⟩ := hnodup
  by_contra hhd2
  apply hhd
  have hhdp : hd = (hd.1,hd.2) := by {
    simp
  }
  rw [hhdp]
  rw [← ha1e]
  rw [hhd2]
  exact ha1
  have hconda := hcond hd.1 hd.2 a1 a (by left;simp) (by right;exact ha1)
  by_contra ha2
  apply hconda at ha2
  apply ha1ne
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

def bcompatible (s : List (Bool × normalizable α pred)) (t : List (Bool × normalizable α pred)) : Bool :=
  s.all (fun x => t.all (fun y =>  x.snd == y.snd -> x.fst == y.fst))

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
  rw [List.filter_eq_nil] at htn
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


theorem c3 : ∀ n : List (List (List (Bool × normalizable α pred))),
             (coherent n ->
            ¬ (∃ g: List (List (Bool × normalizable α pred)), g ∈ n ∧
            ∃ s : List (Bool × normalizable α pred), s ∈ g ∧
            ∃ h : List (List (Bool × normalizable α pred)),h ∈ n ∧
            ((∃ w : Bool × normalizable α pred , w ∉ s ∧
            ∀ t ∈ h, bcompatible s t -> w ∈ t) ∨ ¬(∃ t ∈ h, bcompatible s t ))) ->
            (∀ g ∈ n, ∀ s ∈ g, ∃ t, List.Subset s t ∧ (t.map Prod.snd).Nodup ∧ (sToProp t -> nToProp n))) :=
  by
  --do induction over the length of n three times
  rw [ all_length_list (fun n => (coherent n ->
            ¬ (∃ g: List (List (Bool × normalizable α pred)), g ∈ n ∧
            ∃ s : List (Bool × normalizable α pred), s ∈ g ∧
            ∃ h : List (List (Bool × normalizable α pred)),h ∈ n ∧
            ((∃ w : Bool × normalizable α pred , w ∉ s ∧
            ∀ t ∈ h, bcompatible s t -> w ∈ t) ∨ ¬(∃ t ∈ h, bcompatible s t ))) ->
            (∀ g ∈ n, ∀ s ∈ g, ∃ t, List.Subset s t ∧ (t.map Prod.snd).Nodup ∧ (sToProp t -> nToProp n))) ) ]
  intro m
  induction' m with m ih
  --at 0, the universal is vacuous
  intro n hn hccoh hneg g hg
  simp at hn
  rw [hn] at hg
  contradiction
  --at 1, just use the entries of g
  clear ih
  induction' m with m' ih
  intro n hn
  simp at hn
  intro hcoh hneg g hg
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
  intro hcoh hneg
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
  intro n hn
  induction' m'' with m''' ih
  cases' n with g1 n1
  contradiction
  cases' n1 with g2 n2
  simp at hn
  cases' n2 with g3 n3
  simp at hn
  simp [List.length] at hn
  rw [hn]
  intro hcoh hneg g hg s hs
  simp at hg
  push_neg at hneg
    --at 3, have that (∀ g h,(∀ s ∈ g, ∃ t ∈ h, bcompatible s t) ∧ (∀ t ∈ h, ∃ s ∈ g, bcompatible s t)) ->
  -- ∀s, (s ∈ g ∨ s ∈ h) -> ∃ t ∈ cross g h, List.Subset s t
  --the full solution set is (A cross c) cross (B cross C),
  --where cross a b = ((Cross a b).filter (fun x => bcompatible x.1 x.2)).map (fun x => (x.1 ++ x.2).dedup),
  --n = [A , B , C]
  cases' hg with hg1 hg
  unfold coherent at hcoh
  have hcohs := hcoh g (by rw [hg1];simp) s hs
  rw [← s_nodup] at hcohs
  simp only [beq_iff_eq, and_imp,  implies_true, Bool.false_eq_true,
    imp_false, true_and, Bool.true_eq_false, and_true] at hcohs
  rw [hg1] at hs

  let cross12 := g1.bind (fun s1 => (g2.filter (fun s2 => bcompatible s1 s2)).map (fun s2 => s1 ++ s2.filter (fun x => x ∉ s1)))
  have hcross12 : cross12 = g1.bind (fun s1 => (g2.filter (fun s2 => bcompatible s1 s2)).map (fun s2 => s1 ++ s2.filter (fun x => x ∉ s1))) := by {
    dsimp
  }
  let cross13 := g1.bind (fun s1 => (g3.filter (fun s2 => bcompatible s1 s2)).map (fun s2 => s1 ++ s2.filter (fun x => x ∉ s1)))
  have hcross13 : cross13 = g1.bind (fun s1 => (g3.filter (fun s2 => bcompatible s1 s2)).map (fun s2 => s1 ++ s2.filter (fun x => x ∉ s1))) := by {
    dsimp
  }
  --to prove that there is a t3 from cross13 compatible with each element t2 of cross12,
  --do proof by contradiction,
  --show that there would have to be elements w1, w2 of t2 and t3 from s ∈ g1, whatever t3 is, not in the subsets s2 ∈ g2 and s3 ∈ g3, which violate compatibility
  -- this contradicts the ∀ w ∉ s,∃ t ∈ h, bcompatible s t ∧ w ∉ t part of hneg
  have h_cross12 : ∃ t2 ∈ cross12, s.Subset t2 := by {
    have hcompat := (hneg g1 (by simp) s hs g2 (by simp)).2
    obtain ⟨ t2,ht2,hcomp2⟩ := hcompat
    use s++ t2.filter (fun x => x ∉ s)
    constructor
    rw [hcross12]
    simp
    use s
    constructor
    exact hs
    use t2
    intro x hx
    simp
    left
    exact hx
  }
  have hcompat : ∀ t2 ∈ cross12 ,∃ t3 ∈ cross13, bcompatible t2 t3 := by {
    intro t2 ht2
    by_contra hh
    push_neg at hh
    obtain ⟨ s1,hs1,ht2'⟩ := List.mem_bind.mp ht2
    obtain ⟨ t2', ht2',ht2eq⟩ := List.mem_map.mp ht2'
    have h_vio : ∀t3 ∈ cross13, ∃ t3t ∈ g3, t3t.Subset t3 ∧  ∃ s3 ∈ g1, s3.Subset t3 ∧ ∃ w1 ∈ s1,∃ w2 ∈ s3, w1 ∉ t2' ∧ w2 ∉ t3t ∧ w1.2 = w2.2 ∧ w1.1 ≠ w2.1 := by
    {

    }
  }
  sorry



  --at m + 3, do proof by contradiction
  --with n = (A :: B :: C :: tl)
  --  ¬ nToProp n -> (¬nToProp (B :: C :: tl)) ∨ (¬nToProp (A :: C :: tl)) ∨ (¬ nToProp (A :: B :: tl))
  -- then there is a pair g h violating the precondition, in a list of length m + 2
  --since every pair g h in n is in one of the lists, and vice versa, g h is in n
  sorry

def wireset (n : List (List (List (Bool × normalizable α pred)))) : List (normalizable α pred) :=
  ((n.map
  (fun g => (g.map
  (fun s => s.map
  (fun w => w.snd))).join)).join).dedup

def order (n : List (List (List (Bool × normalizable α pred))))  : Nat :=
  let count : Nat := Nat.succ (wireset n).length;
  (n.map
  (fun g => (g.map
  (fun s => count - (List.length s))).sum)).sum

def clean (r : List (List (List (Bool × normalizable α pred)))) (n : Nat) : List (List (List (Bool × normalizable α pred))) :=
  let s := makeCoherent r;
  match n with
  | 0 => s
  | Nat.succ a => let f := (if [] ∈ s then s else
    s.map
  (fun t : List (List (Bool × normalizable α pred)) =>
    (t.filter
      (fun w => s.all
        (fun u => u.any
          (fun v => bcompatible v w)))).map
    (fun r : List (Bool × normalizable α pred) =>
      (((s.filter
            (fun u => !(u = t))).map
          (fun p : List (List (Bool × (normalizable α pred))) =>
            (p.filter
              (fun v : List (Bool × (normalizable α pred)) => bcompatible v r)))).map
        (fun w : List (List (Bool × normalizable α pred)) =>
          ((interl (w.filter
                (fun v : List (Bool × normalizable α  pred) => bcompatible v r))).filter
            (fun x : Bool × normalizable α pred => ¬(x ∈ r))))).foldl
      (fun u v : List (Bool × normalizable α pred) => u.union v) r)));
  if  order f >= order s then s else clean f a
  termination_by n
  decreasing_by
  simp_wf

theorem leneqclean : ∀ o : Nat, ∀ n : List (List (List (Bool × normalizable α pred))), (clean n o).length = n.length :=
  by
  intro o
  induction' o with o ho
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
        (fun t ↦
          List.map
            (fun r ↦
              List.foldl (fun u v ↦ u.union v) r
                (List.map
                  ((fun w ↦ List.filter (fun x ↦ !decide (x ∈ r)) (interl (List.filter (fun v ↦ bcompatible v r) w))) ∘
                    fun p ↦ List.filter (fun v ↦ bcompatible v r) p)
                  (List.filter (fun u ↦ !decide (u = t)) (makeCoherent n))))
            (List.filter (fun w ↦ (makeCoherent n).all fun u ↦ u.any fun v ↦ bcompatible v w) t))
        (makeCoherent n))) with hord hnord
  rw [if_pos]
  have hm : List.length (makeCoherent n) = List.length n := by {
    unfold makeCoherent
    simp
  }
  apply ho at n
  exact hm
  exact hord
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
