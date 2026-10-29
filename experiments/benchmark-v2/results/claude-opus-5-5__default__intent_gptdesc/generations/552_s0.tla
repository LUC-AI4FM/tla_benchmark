------------------------- MODULE OneBitScannerMutex -------------------------
(***************************************************************************)
(* Mutual exclusion for N identical processes using a single shared        *)
(* boolean flag per process and a bounded shared integer token "turn"      *)
(* (the scanner index, ranging over 0..N-1).                               *)
(*                                                                         *)
(* Each process repeatedly cycles through:                                 *)
(*   ncs  : noncritical section (may stay there forever)                   *)
(*   set  : raise own flag  (flag[i] := TRUE)                              *)
(*   scan : look at the process designated by the scanner index:           *)
(*            - if turn = i               -> enter critical section        *)
(*            - if flag[turn] = FALSE     -> advance scanner index         *)
(*            - otherwise                 -> wait (blocked)                *)
(*   cs   : critical section                                               *)
(*   exit : clear own flag and pass the scanner index to the next process  *)
(*                                                                         *)
(* A process only enters the CS when the scanner index designates it.      *)
(* While a process is in the CS its flag is TRUE and the index points to   *)
(* it, so no other process may advance the index.  This gives mutual       *)
(* exclusion.  The index only moves forward cyclically.  It moves past     *)
(* idle processes (flag FALSE) and past processes that complete their CS.  *)
(* As a result, every waiting process is eventually designated.  Once it   *)
(* is designated, the index cannot move until that process has entered     *)
(* and left the CS.  This gives starvation freedom under weak fairness.    *)
(*                                                                         *)
(* Modeling note: a "scan" step reads flag[turn] and conditionally         *)
(* advances turn in one atomic step (a test-and-advance on the token).     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

Next1(k) == (k + 1) % N           \* cyclic successor of a scanner index

VARIABLES
    flag,   \* flag[i] : the single shared bit owned by process i
    turn,   \* shared bounded scanner index / token, in 0..N-1
    pc      \* control location of each process

vars == << flag, turn, pc >>

Locations == {"ncs", "set", "scan", "cs", "exit"}

TypeOK ==
    /\ flag \in [Procs -> BOOLEAN]
    /\ turn \in Procs
    /\ pc   \in [Procs -> Locations]

Init ==
    /\ flag = [i \in Procs |-> FALSE]
    /\ turn = 0
    /\ pc   = [i \in Procs |-> "ncs"]

---------------------------------------------------------------------------
(* Process actions *)

\* Leave noncritical section and start trying (no fairness: may never happen)
NCS(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "set"]
    /\ UNCHANGED << flag, turn >>

\* Announce interest by raising own flag
SetFlag(i) ==
    /\ pc[i] = "set"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ pc'   = [pc EXCEPT ![i] = "scan"]
    /\ UNCHANGED turn

\* Scanner index designates someone else whose flag is down: advance it
Advance(i) ==
    /\ pc[i] = "scan"
    /\ turn # i
    /\ ~flag[turn]
    /\ turn' = Next1(turn)
    /\ UNCHANGED << flag, pc >>

\* Scanner index designates me: enter the critical section
Enter(i) ==
    /\ pc[i] = "scan"
    /\ turn = i
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << flag, turn >>

\* Finish critical section
LeaveCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED << flag, turn >>

\* Exit protocol: clear own flag and pass the scanner index onward
Exit(i) ==
    /\ pc[i] = "exit"
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ turn' = Next1(i)
    /\ pc'   = [pc EXCEPT ![i] = "ncs"]

\* All protocol (non-NCS) steps of process i
Protocol(i) ==
    \/ SetFlag(i)
    \/ Advance(i)
    \/ Enter(i)
    \/ LeaveCS(i)
    \/ Exit(i)

Proc(i) == NCS(i) \/ Protocol(i)

Next == \E i \in Procs : Proc(i)

\* Weak fairness on every process's entry/exit protocol actions.
\* There is no fairness on NCS, so a process may stay noncritical forever.
Fairness == \A i \in Procs : WF_vars(Protocol(i))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Equivalent cardinality formulation
AtMostOneInCS == Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

\* Auxiliary inductive invariants
FlagInv ==
    \A i \in Procs : flag[i] <=> (pc[i] \in {"scan", "cs", "exit"})

TokenInv ==
    \A i \in Procs : (pc[i] \in {"cs", "exit"}) => (turn = i)

Inv == TypeOK /\ FlagInv /\ TokenInv /\ MutualExclusion /\ AtMostOneInCS

---------------------------------------------------------------------------
(* Liveness properties *)

Trying(i) == pc[i] \in {"set", "scan"}

\* No starvation: every process that tries eventually enters the CS
StarvationFreedom ==
    \A i \in Procs : Trying(i) ~> (pc[i] = "cs")

\* Deadlock freedom: if someone is trying, someone eventually enters
DeadlockFreedom ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

\* A process in the CS eventually returns to the noncritical section
ExitProgress ==
    \A i \in Procs : (pc[i] = "cs") ~> (pc[i] = "ncs")

\* A process that tries infinitely often enters the CS infinitely often
RepeatedEntry ==
    \A i \in Procs : ([]<>Trying(i)) => ([]<>(pc[i] = "cs"))

---------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => StarvationFreedom /\ DeadlockFreedom /\ ExitProgress
=============================================================================