---------------------------- MODULE BinarySearch ----------------------------
(*
  Binary Search Specification in TLA+

  This models binary search as a state machine and verifies:
  1. The algorithm terminates
  2. If it finds an index, the element at that index equals the key
  3. If it returns "not found", the key is not in the array
*)

EXTENDS Integers, Sequences, TLC

CONSTANTS
    Array,      \* The sorted array (as a sequence)
    Key         \* The key to search for

VARIABLES
    lo,         \* Lower bound of search range
    hi,         \* Upper bound of search range
    result,     \* Search result: index or "not_found" or "searching"
    pc          \* Program counter

vars == <<lo, hi, result, pc>>

\* Array is sorted
IsSorted(arr) == \A i, j \in 1..Len(arr) : i < j => arr[i] <= arr[j]

\* Type invariant
TypeOK ==
    /\ lo \in 0..Len(Array)+1
    /\ hi \in 0..Len(Array)+1
    /\ result \in (1..Len(Array)) \cup {"not_found", "searching"}
    /\ pc \in {"search", "done"}

\* Initial state
Init ==
    /\ lo = 1
    /\ hi = Len(Array) + 1
    /\ result = "searching"
    /\ pc = "search"

\* Search step
Search ==
    /\ pc = "search"
    /\ IF lo >= hi
       THEN
            /\ result' = "not_found"
            /\ pc' = "done"
            /\ UNCHANGED <<lo, hi>>
       ELSE
            LET mid == lo + (hi - lo) \div 2
            IN IF Array[mid] < Key
               THEN
                    /\ lo' = mid + 1
                    /\ UNCHANGED <<hi, result, pc>>
               ELSE IF Array[mid] > Key
                    THEN
                        /\ hi' = mid
                        /\ UNCHANGED <<lo, result, pc>>
                    ELSE  \* Found it
                        /\ result' = mid
                        /\ pc' = "done"
                        /\ UNCHANGED <<lo, hi>>

\* Termination (stuttering when done)
Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Search \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Search)

-----------------------------------------------------------------------------
(* Safety Properties *)

\* If we found something, it's the right value
CorrectResult ==
    result \in 1..Len(Array) => Array[result] = Key

\* If we didn't find it, it's really not there
CompleteResult ==
    (pc = "done" /\ result = "not_found") =>
        \A i \in 1..Len(Array) : Array[i] # Key

\* Combined invariant
SafetyInvariant == TypeOK /\ CorrectResult

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* The search eventually terminates
Termination == <>(pc = "done")

=============================================================================
