import PolySat.NP.constraints
import PolySat.basic2
import Init.Data.List
import Std.Data.List
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Join
open Classical

variable (n : Nat)

Type Sudoku n :=  Vec (Vec (fin (n ^ 2 + 1)) (n ^ 2)) (n ^2)

variable (s: Sudoku n)

Type SudokuInstance n := List ((fin (n ^ 2) × fin (n ^ 2)) × fin (n ^ 2 + 1))

def SudokuPred n (a : (fin n^2 × fin n^2)× fin n^2 + 1 ):= ((s.get a.fst.fst).get (a.fst.snd)) = a.snd

def cellConstraints n : List (List (List (Bool × normalizable ((fin (n ^ 2) × fin (n ^ 2)) × fin (n ^ 2 + 1)) SudokuPred))) :=
  ((List.range (n^2 - 1)).map
  (fun x => ((List.range (n^2 - 1)).map
  (fun y => oneConstraint (((List.range (n^2 - 1)).map
  (fun x => x + 1)).map
  (fun z => vAtom ((x,y),z))))).Join)).Join

def rowConstraints n : List (List (List (Bool × normalizable ((fin (n ^ 2) × fin (n ^ 2)) × fin (n ^ 2 + 1)) SudokuPred))) :=
  ((List.range (n^2 - 1)).map
  (fun x => (((List.range (n^2 - 1)).map
  (fun x => x + 1)).map
  (fun y => oneConstraint (((List.range (n^2 - 1)).map
  (fun z => vAtom ((x,z),y)))))).Join)).Join

def columnConstraints n : List (List (List (Bool × normalizable ((fin (n ^ 2) × fin (n ^ 2)) × fin (n ^ 2 + 1)) SudokuPred))) :=
  ((List.range (n^2 - 1)).map
  (fun x => (((List.range (n^2 - 1)).map
  (fun x => x + 1)).map
  (fun y => oneConstraint (((List.range (n^2 - 1)).map
  (fun z => vAtom ((z, x), y)))))).Join)).Join

def blockConstraints n: List (List (List (Bool × normalizable ((fin (n ^ 2) × fin (n ^ 2)) × fin (n ^ 2 + 1)) SudokuPred))) :=
  ((List.range (n^2 - 1).map (fun z => z + 1)).map
  (fun z => ((List.product (List.range n) (List.range n)).map
  (fun x => oneConstraint ((List.product (List.range n) (List.range n)).map
  (fun y => vAtom ((x.fst * n + y.fst, x.snd * n + y.snd), z))))).Join)).Join

def SudokuConstraints n (i : SudokuInstance n) : List (List (List (Bool × normalizable ((fin (n ^ 2) × fin (n ^ 2)) × fin (n ^ 2 + 1)) SudokuPred))) :=
  [(i.map (fun x => [[atom x]])), cellConstraints n, rowConstraints n, blockConstraints n].Join

partial def solution n (i : SudokuInstance n) : Sudoku n :=
  if lsatisfiable? (sudokuConstrints n i)
  then (List.range (n^2 - 1)).map
    (fun x => (List.range (n^2 - 1)).map
    (fun y => ((lsolveatoms (SudokuConstraints i)).find
    (fun z => z.fst = (x,y))).snd))
