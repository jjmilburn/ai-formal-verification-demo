--------------------------- MODULE MutualExclusion ---------------------------
(*
  Peterson's Mutual Exclusion Algorithm

  Classic example of formal verification.
  Two processes share a critical section - we verify they never both enter.

  This is the example from Murat Demirbas's "Genefication" blog post,
  demonstrating the LLM + TLC feedback loop.
*)

EXTENDS Integers, TLC

VARIABLES
    flag,       \* flag[i] = TRUE means process i wants to enter CS
    turn,       \* whose turn it is (tiebreaker)
    pc          \* program counter for each process: "idle", "waiting", "cs"

vars == <<flag, turn, pc>>

Procs == {0, 1}

TypeOK ==
    /\ flag \in [Procs -> BOOLEAN]
    /\ turn \in Procs
    /\ pc \in [Procs -> {"idle", "set_flag", "set_turn", "waiting", "cs", "exit"}]

Init ==
    /\ flag = [p \in Procs |-> FALSE]
    /\ turn = 0
    /\ pc = [p \in Procs |-> "idle"]

\* Process p wants to enter critical section
SetFlag(p) ==
    /\ pc[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "set_flag"]
    /\ UNCHANGED turn

\* Process p sets turn to other process (being polite)
SetTurn(p) ==
    /\ pc[p] = "set_flag"
    /\ turn' = 1 - p
    /\ pc' = [pc EXCEPT ![p] = "set_turn"]
    /\ UNCHANGED flag

\* Process p waits until it can enter
Wait(p) ==
    /\ pc[p] = "set_turn"
    /\ \/ ~flag[1-p]           \* Other process doesn't want in
       \/ turn = p             \* It's my turn
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<flag, turn>>

\* Process p is in critical section, then exits
Exit(p) ==
    /\ pc[p] = "cs"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED turn

\* All process actions
Process(p) == SetFlag(p) \/ SetTurn(p) \/ Wait(p) \/ Exit(p)

Next == \E p \in Procs : Process(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: Mutual Exclusion *)

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")

(* Liveness: No starvation - if a process wants in, it eventually gets in *)
NoStarvation == \A p \in Procs : (pc[p] = "set_flag") ~> (pc[p] = "cs")

=============================================================================
