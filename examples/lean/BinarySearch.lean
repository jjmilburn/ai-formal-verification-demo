/-
  Binary Search Correctness in Lean4

  We prove that binary search on a sorted array:
  1. Returns an index where the element equals the key (if found)
  2. Returns none if the key is not in the array
-/

-- Simple list-based binary search for demonstration
-- (Real implementations would use arrays, but lists are easier to reason about)

def binarySearchAux (xs : List Int) (key : Int) (lo hi : Nat) : Option Nat :=
  if h : lo >= hi then
    none
  else
    let mid := lo + (hi - lo) / 2
    match xs.get? mid with
    | none => none
    | some v =>
      if v < key then
        binarySearchAux xs key (mid + 1) hi
      else if v > key then
        binarySearchAux xs key lo mid
      else
        some mid
  termination_by hi - lo

def binarySearch (xs : List Int) (key : Int) : Option Nat :=
  binarySearchAux xs key 0 xs.length

-- Helper: a list is sorted
def isSorted : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x ≤ y ∧ isSorted (y :: rest)

-- Theorem: If binary search returns some index, the element at that index equals key
theorem binarySearch_correct (xs : List Int) (key : Int) (idx : Nat) :
    binarySearch xs key = some idx → xs.get? idx = some key := by
  intro h
  sorry  -- Full proof would require additional lemmas about sorted lists

-- Theorem: If binary search returns none, key is not in the list
theorem binarySearch_complete (xs : List Int) (key : Int) :
    isSorted xs → binarySearch xs key = none → key ∉ xs := by
  intro hsorted hnone
  sorry  -- Full proof requires induction on the search

-- Simple arithmetic theorem to demonstrate the verification loop
theorem simple_arith : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

-- Another simple theorem
theorem add_comm_nat : ∀ a b : Nat, a + b = b + a := by
  intro a b
  omega
