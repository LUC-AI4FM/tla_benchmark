------------------------------ MODULE FastMutex ------------------------------
(***************************************************************************)
(* A model of Lamport's Fast Mutual Exclusion algorithm for N processes.   *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   x, y : coordination variables, values in 0..N (0 means "free").      *)
(*   b[i] : process i's announcement flag ("I am trying").                *)
(* Local state:                                                            *)
(*   pc[i] : the control location of process i.                          *)
(*   j[i]  : loop index used while probing the announcements of others.   *)
(*                                                                         *)
(* Every step reads or writes at most one shared variable, so the model    *)
(* assumes no atomic multi-process or multi-variable updates. Processes    *)
(* interleave arbitrarily. Busy-wait loops are modelled as guarded         *)
(* ("await") actions.                                                      *)
(*                                                                         *)
(* Control locations:                                                      *)
(*   ncs   : noncritical section; may stay there forever                   *)
(*   start : b[i] := TRUE                    (announce intent)             *)
(*   l1    : x := i                                                        *)
(*   l2    : if y # 0 goto l3 else goto l4   (contention probe)            *)
(*   l3    : b[i] := FALSE                   (abort: retract announcement) *)
(*   l3a   : await y = 0; goto start         (back off and retry)          *)
(*   l4    : y := i                                                        *)
(*   l5    : if x # i goto l6 else goto cs   (fast path)                   *)
(*   l6    : b[i] := FALSE; j := 1           (slow path)                   *)
(*   l7    : for j in 1..N: await ~b[j]      (probe all announcements)     *)
(*   l8    : if y # i goto l9 else goto cs                                 *)
(*   l9    : await y = 0; goto start         (abort and retry)             *)
(*   cs    : critical section                                              *)
(*   l10   : y := 0                          (release)                     *)
(*   l11   : b[i] := FALSE; goto ncs         (release)                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 1..N

VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

Labels == {"ncs", "start", "l1", "l2", "l3", "l3a", "l4", "l5", "l6",
           "l7", "l8", "l9", "cs", "l10", "l11"}

\* Locations in which a process is attempting to enter the critical section
Trying == {"start", "l1", "l2", "l3", "l3a", "l4", "l5", "l6",
           "l7", "l8", "l9"}

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [Procs -> BOOLEAN]
  /\ pc \in [Procs -> Labels]
  /\ j \in [Procs -> 1..(N+1)]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Procs |-> FALSE]
  /\ pc = [i \in Procs |-> "ncs"]
  /\ j = [i \in Procs |-> 1]

Goto(i, lbl) == pc' = [pc EXCEPT ![i] = lbl]

\* Noncritical section: nondeterministically decide to try to enter.
NCS(i) ==
  /\ pc[i] = "ncs"
  /\ Goto(i, "start")
  /\ UNCHANGED << x, y, b, j >>

\* Nonblocking attempt: announce intent.
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

\* Probe y: contention detected if y # 0.
L2(i) ==
  /\ pc[i] = "l2"
  /\ IF y # 0 THEN Goto(i, "l3") ELSE Goto(i, "l4")
  /\ UNCHANGED << x, y, b, j >>

\* Abort: retract the announcement.
L3(i) ==
  /\ pc[i] = "l3"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ Goto(i, "l3a")
  /\ UNCHANGED << x, y, j >>

\* Backoff: wait until y = 0, then retry.
L3a(i) ==
  /\ pc[i] = "l3a"
  /\ y = 0
  /\ Goto(i, "start")
  /\ UNCHANGED << x, y, b, j >>

L4(i) ==
  /\ pc[i] = "l4"
  /\ y' = i
  /\ Goto(i, "l5")
  /\ UNCHANGED << x, b, j >>

\* Fast path check.
L5(i) ==
  /\ pc[i] = "l5"
  /\ IF x # i THEN Goto(i, "l6") ELSE Goto(i, "cs")
  /\ UNCHANGED << x, y, b, j >>

\* Slow path: retract announcement, initialise probe index.
L6(i) ==
  /\ pc[i] = "l6"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ Goto(i, "l7")
  /\ UNCHANGED << x, y >>

\* Probe the announcements of all processes, one at a time (busy-wait).
L7(i) ==
  /\ pc[i] = "l7"
  /\ IF j[i] <= N
       THEN /\ ~b[j[i]]
            /\ j' = [j EXCEPT ![i] = j[i] + 1]
            /\ UNCHANGED pc
       ELSE /\ Goto(i, "l8")
            /\ UNCHANGED j
  /\ UNCHANGED << x, y, b >>

L8(i) ==
  /\ pc[i] = "l8"
  /\ IF y # i THEN Goto(i, "l9") ELSE Goto(i, "cs")
  /\ UNCHANGED << x, y, b, j >>

\* Lost the race: wait until y = 0, then retry.
L9(i) ==
  /\ pc[i] = "l9"
  /\ y = 0
  /\ Goto(i, "start")
  /\ UNCHANGED << x, y, b, j >>

\* Critical section.
CS(i) ==
  /\ pc[i] = "cs"
  /\ Goto(i, "l10")
  /\ UNCHANGED << x, y, b, j >>

\* Explicit release.
L10(i) ==
  /\ pc[i] = "l10"
  /\ y' = 0
  /\ Goto(i, "l11")
  /\ UNCHANGED << x, b, j >>

L11(i) ==
  /\ pc[i] = "l11"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ Goto(i, "ncs")
  /\ UNCHANGED << x, y, j >>

\* All steps of process i other than leaving the noncritical section.
\* (A process is allowed to remain in its noncritical section forever.)
Protocol(i) ==
  \/ Start(i) \/ L1(i) \/ L2(i) \/ L3(i) \/ L3a(i) \/ L4(i) \/ L5(i)
  \/ L6(i) \/ L7(i) \/ L8(i) \/ L9(i) \/ CS(i) \/ L10(i) \/ L11(i)

Proc(i) == NCS(i) \/ Protocol(i)

Next == \E i \in Procs : Proc(i)

\* Weak fairness for every protocol action of every process.
Fairness == \A i \in Procs : WF_vars(Protocol(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)

MutualExclusion ==
  \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

\* Deadlock freedom: whenever some process is trying, eventually some
\* process enters the critical section.
DeadlockFree ==
  (\E i \in Procs : pc[i] \in Trying) ~> (\E i \in Procs : pc[i] = "cs")

\* Global eventual entry: if processes keep attempting to enter, then
\* infinitely often some process is in the critical section.
GlobalProgress ==
  ([]<>(\E i \in Procs : pc[i] \in Trying))
     => []<>(\E i \in Procs : pc[i] = "cs")

\* Conditional starvation freedom: a trying process eventually enters,
\* provided the other processes do not indefinitely interfere (i.e. they
\* eventually stay in their noncritical sections). This holds under the
\* weak fairness assumption above.
StarvationFreeIfUncontended ==
  \A i \in Procs :
     (<>[](\A k \in Procs \ {i} : pc[k] = "ncs"))
        => ((pc[i] \in Trying) ~> (pc[i] = "cs"))

\* Unconditional starvation freedom. NOTE: Lamport's fast mutex is only
\* deadlock-free; this stronger property is NOT expected to hold and is
\* included so a model checker can exhibit a starvation counterexample.
StarvationFree ==
  \A i \in Procs : (pc[i] \in Trying) ~> (pc[i] = "cs")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree /\ GlobalProgress /\ StarvationFreeIfUncontended
=============================================================================