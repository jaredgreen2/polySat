import Init.Prelude
import Init.Coe
import Mathlib.Data.List.Basic

variable {α : Type}
inductive IList α
  where
  | single : α -> IList α
  | cons : α -> (IList α) -> (IList α)
deriving DecidableEq

def IList.fold  (l : IList α)  (f : α -> b -> b)  (g : α -> b) : b :=
  match l with
  | single a => g a
  | cons a as => f a (fold as f g)

def IList.map  (f : α -> b) : IList α -> IList b
  | single a => single (f a)
  | cons a as => cons (f a) (map f as)

def IList.toList : IList α -> {l : List α // l ≠ []}
  | single a => ⟨ [a], by simp⟩
  | cons a as => ⟨ (a :: (IList.toList as)),by simp⟩

def IList.ofList (l: {l : List α // l ≠ []}) : IList α :=
  match l with
  | ⟨ [x], _ ⟩ => .single x
  | ⟨ x :: xs@(y :: ys),h⟩ => .cons x ( IList.ofList ⟨ xs, fun h => by aesop ⟩ )

instance : Coe (IList α) {l : List α // l ≠ []} where
  coe l := IList.toList l

instance : Coe {l : List α // l ≠ []} (IList α) where
  coe l := IList.ofList l
