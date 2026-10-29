------------------------- MODULE FastMutualExclusion -------------------------
(***************************************************************************)
(* A parameterized fast mutual-exclusion algorithm for N processes        *)
(* (in the style of Lamport's "fast" algorithm).                          *)
(*                                                                         *)
(* Fast path: a process announces intent (b[i] := TRUE), writes x := i,   *)
(* checks that y = 0 (no one in the fast doorway), writes y := i, and if  *)
(* x is still i it enters the critical section without waiting for anyone.*)
(*                                                                         *)
(* Backup path: if contention is detected (x # i after writing y), the    *)
(* process withdraws its flag, waits until every process's flag has been  *)
(* cleared (scanning b[1..N]), and then enters if it still owns y.        *)
(* Otherwise it waits for y = 0 and restarts from the beginning.          *)
(*                                                                         *)
(* Atomicity assumptions: each individual read or write of a shared       *)
(* variable (x, y, b[j]) is atomic, and each labeled process step below   *)
(* is a single atomic action performing at most one shared access.        *)
(* Processes are symmetric; process identities 1..N are used only to      *)
(* name the processes and as values of x and y (0 means "no process").    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES
    x,      \* shared: last process to enter the fast doorway
    y,      \* shared: global indicator; 0 iff no process holds the fast doorway
    b,      \* shared: per-process intent flags
    pc,     \* local: program counter of each process
    j       \* local: loop index for the backup scan of the flags

vars == << x, y, b, pc, j >>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
           "l6", "l7", "l8", "cs", "l9", "l10"}

TypeOK ==
    /\ x \in Procs \cup {0}
    /\ y \in Procs \cup {0}
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> Labels]
    /\ j \in [Procs -> 1..(N+1)]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ j = [i \in Procs |-> 1]

\* Leave the noncritical section and start an attempt
Ncs(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Announce intent
Start(i) ==
    /\ pc[i] = "start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "l1"]
    /\ UNCHANGED << x, y, j >>

\* Enter the fast doorway
L1(i) ==
    /\ pc[i] = "l1"
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "l2"]
    /\ UNCHANGED << y, b, j >>

\* Read the global indicator; if someone holds the doorway, withdraw
L2(i) ==
    /\ pc[i] = "l2"
    /\ IF y # 0
          THEN /\ b' = [b EXCEPT ![i] = FALSE]
               /\ pc' = [pc EXCEPT ![i] = "l3"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "l4"]
               /\ UNCHANGED b
    /\ UNCHANGED << x, y, j >>

\* Wait until the doorway is free, then restart
L3(i) ==
    /\ pc[i] = "l3"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Claim the doorway
L4(i) ==
    /\ pc[i] = "l4"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "l5"]
    /\ UNCHANGED << x, b, j >>

\* Check for contention: fast entry if x = i, else switch to backup protocol
L5(i) ==
    /\ pc[i] = "l5"
    /\ IF x # i
          THEN /\ b' = [b EXCEPT ![i] = FALSE]
               /\ j' = [j EXCEPT ![i] = 1]
               /\ pc' = [pc EXCEPT ![i] = "l6"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
               /\ UNCHANGED << b, j >>
    /\ UNCHANGED << x, y >>

\* Backup protocol: wait for every process's flag to be cleared, one at a time
L6(i) ==
    /\ pc[i] = "l6"
    /\ IF j[i] <= N
          THEN /\ ~b[j[i]]
               /\ j' = [j EXCEPT ![i] = j[i] + 1]
               /\ UNCHANGED pc
          ELSE /\ pc' = [pc EXCEPT ![i] = "l7"]
               /\ UNCHANGED j
    /\ UNCHANGED << x, y, b >>

\* Backup protocol: enter if still owning the doorway, otherwise lose
L7(i) ==
    /\ pc[i] = "l7"
    /\ IF y # i
          THEN pc' = [pc EXCEPT ![i] = "l8"]
          ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

\* Lost the race: wait for the doorway to be free, then restart
L8(i) ==
    /\ pc[i] = "l8"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Critical section
CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "l9"]
    /\ UNCHANGED << x, y, b, j >>

\* Exit: release the doorway
L9(i) ==
    /\ pc[i] = "l9"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![i] = "l10"]
    /\ UNCHANGED << x, b, j >>

\* Exit: clear intent flag and return to the noncritical section
L10(i) ==
    /\ pc[i] = "l10"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << x, y, j >>

Proc(i) ==
    \/ Ncs(i) \/ Start(i) \/ L1(i) \/ L2(i) \/ L3(i) \/ L4(i) \/ L5(i)
    \/ L6(i)  \/ L7(i)    \/ L8(i) \/ CS(i) \/ L9(i) \/ L10(i)

Next == \E i \in Procs : Proc(i)

\* Weak fairness on every process's steps: processes keep trying forever
Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
    \A i, k \in Procs : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

\* No deadlock: some process can always take a step
NoDeadlock == ENABLED Next

-----------------------------------------------------------------------------
(* Liveness *)

Trying(i) == pc[i] \in {"start", "l1", "l2", "l3", "l4", "l5", "l6", "l7", "l8"}

\* Deadlock freedom: if some process is trying, some process eventually enters
DeadlockFreedom ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

\* A process that lost the fast race (or was blocked at the doorway)
\* eventually reattempts from the start, or the system makes progress
\* through some process entering the critical section.
LostRaceResolution ==
    \A i \in Procs :
        (pc[i] \in {"l3", "l8"}) ~>
            (pc[i] = "start" \/ \E k \in Procs : pc[k] = "cs")

\* The system enters the critical section infinitely often
InfinitelyOftenCS == []<>(\E i \in Procs : pc[i] = "cs")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion /\ NoDeadlock)
THEOREM Spec => DeadlockFreedom /\ LostRaceResolution /\ InfinitelyOftenCS
=============================================================================