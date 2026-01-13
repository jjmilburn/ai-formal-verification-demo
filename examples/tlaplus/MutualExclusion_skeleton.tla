--------------------------- MODULE MutualExclusion_skeleton ---------------------------
(*
  Mutual Exclusion - SKELETON with natural language spec

  PROBLEM DESCRIPTION (for LLM):

  "Two processes need to share a critical section. Requirements:
   1. SAFETY: Both processes must never be in the critical section simultaneously
   2. LIVENESS: If a process wants to enter, it eventually gets in (no starvation)

   Each process should:
   - Set a flag indicating it wants to enter
   - Wait until it's safe to enter
   - Enter the critical section
   - Clear its flag when exiting"

  TODO: This skeleton is missing something - when both processes want to enter,
  how do we decide who goes first? The model checker will find the bug.
*)

EXTENDS Integers

VARIABLES
    flag,       \* flag[i] = TRUE means process i wants to enter CS
    \* TODO: What else might we need to break symmetry?
    pc          \* program counter for each process

vars == <<flag, pc>>

Procs == {0, 1}

Init ==
    /\ flag = [p \in Procs |-> FALSE]
    /\ pc = [p \in Procs |-> "idle"]

\* Process p wants to enter critical section - set flag
SetFlag(p) ==
    /\ pc[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "waiting"]

\* Process p tries to enter - but how to handle both wanting in?
TryEnter(p) ==
    /\ pc[p] = "waiting"
    /\ ~flag[1-p]               \* TODO: This causes deadlock when both set flags!
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED flag

\* Process p exits critical section
Exit(p) ==
    /\ pc[p] = "cs"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Next == \E p \in Procs : SetFlag(p) \/ TryEnter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties to verify *)

\* Safety: Both processes never in critical section together
MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

\* Liveness: If a process wants in, it eventually gets in
NoStarvation == \A p \in Procs : (pc[p] = "waiting") ~> (pc[p] = "cs")

=============================================================================
