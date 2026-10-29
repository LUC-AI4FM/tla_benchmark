------------------------------ MODULE FastMutex ------------------------------
(***************************************************************************)
(* Lamport's fast mutual-exclusion algorithm for N asynchronous processes. *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   b[i]  : announcement flag of process i                                *)
(*   x, y  : two shared coordination variables (0 means "none")            *)
(* Per-process local state:                                                *)
(*   pc[i] : program counter                                               *)
(*   j[i]  : loop index used when probing the others' announcements        *)
(*                                                                         *)
(* Each step reads or writes at most one shared variable.                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS N, M

ASSUME N \in Nat \ {0}

Procs == 1 .. N

VARIABLES x, y, b, j, pc

vars == << x, y, b, j, pc >>

Labels == { "ncs", "start", "l1", "l2", "l3", "l4", "l5",
            "l6", "l7", "l8", "cs", "l9", "l10" }

TypeOK ==
    /\ x \in 0 .. N
    /\ y \in 0 .. N
    /\ b \in [Procs -> BOOLEAN]
    /\ j \in [Procs -> 1 .. (N + 1)]
    /\ pc \in [Procs -> Labels]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ j = [i \in Procs |-> 1]
    /\ pc = [i \in Procs |-> "ncs"]

Goto(i, l) == pc' = [pc EXCEPT ![i] = l]

\* Noncritical section: the process starts a new attempt.
NCS(i) ==
    /\ pc[i] = "ncs"
    /\ Goto(i, "start")
    /\ UNCHANGED << x, y, b, j >>

\* Announce intent.
Start(i) ==
    /\ pc[i] = "start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ Goto(i, "l1")
    /\ UNCHANGED << x, y, j >>

L1(i) ==
    /\ pc[i] = "l1"
    /\ x' = i
    /\ Goto(i, "l2")
    /\ UNCHANGED << y, b, j >>

\* Contention detected on y: withdraw announcement and back off.
L2(i) ==
    /\ pc[i] = "l2"
    /\ IF y # 0
         THEN /\ b' = [b EXCEPT ![i] = FALSE]
              /\ Goto(i, "l3")
         ELSE /\ Goto(i, "l4")
              /\ UNCHANGED b
    /\ UNCHANGED << x, y, j >>

\* Backoff: wait until y = 0, then retry.
L3(i) ==
    /\ pc[i] = "l3"
    /\ y = 0
    /\ Goto(i, "start")
    /\ UNCHANGED << x, y, b, j >>

L4(i) ==
    /\ pc[i] = "l4"
    /\ y' = i
    /\ Goto(i, "l5")
    /\ UNCHANGED << x, b, j >>

\* Fast path if x is still i; otherwise slow path probing others.
L5(i) ==
    /\ pc[i] = "l5"
    /\ IF x # i
         THEN /\ b' = [b EXCEPT ![i] = FALSE]
              /\ j' = [j EXCEPT ![i] = 1]
              /\ Goto(i, "l6")
         ELSE /\ Goto(i, "cs")
              /\ UNCHANGED << b, j >>
    /\ UNCHANGED << x, y >>

\* for k := 1 to N do await ~b[k]
L6(i) ==
    /\ pc[i] = "l6"
    /\ IF j[i] <= N
         THEN /\ ~ b[j[i]]
              /\ j' = [j EXCEPT ![i] = j[i] + 1]
              /\ Goto(i, "l6")
         ELSE /\ Goto(i, "l7")
              /\ UNCHANGED j
    /\ UNCHANGED << x, y, b >>

L7(i) ==
    /\ pc[i] = "l7"
    /\ IF y # i
         THEN Goto(i, "l8")
         ELSE Goto(i, "cs")
    /\ UNCHANGED << x, y, b, j >>

\* Abort: wait until y = 0, then retry.
L8(i) ==
    /\ pc[i] = "l8"
    /\ y = 0
    /\ Goto(i, "start")
    /\ UNCHANGED << x, y, b, j >>

CS(i) ==
    /\ pc[i] = "cs"
    /\ Goto(i, "l9")
    /\ UNCHANGED << x, y, b, j >>

\* Release.
L9(i) ==
    /\ pc[i] = "l9"
    /\ y' = 0
    /\ Goto(i, "l10")
    /\ UNCHANGED << x, b, j >>

L10(i) ==
    /\ pc[i] = "l10"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ Goto(i, "ncs")
    /\ UNCHANGED << x, y, j >>

Proc(i) ==
    \/ NCS(i) \/ Start(i) \/ L1(i) \/ L2(i) \/ L3(i) \/ L4(i)
    \/ L5(i) \/ L6(i) \/ L7(i) \/ L8(i) \/ CS(i) \/ L9(i) \/ L10(i)

Next == \E i \in Procs : Proc(i)

Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~ (pc[p] = "cs" /\ pc[q] = "cs")

Invariant == TypeOK /\ MutualExclusion

Trying(i) == pc[i] \notin { "ncs", "cs", "l9", "l10" }

\* Deadlock freedom: whenever some process is trying, eventually some
\* process enters the critical section; hence entries happen infinitely often.
DeadlockFreedom ==
    (\E i \in Procs : Trying(i)) ~> (\E k \in Procs : pc[k] = "cs")

Liveness ==
    /\ DeadlockFreedom
    /\ []<>(\E k \in Procs : pc[k] = "cs")
=============================================================================