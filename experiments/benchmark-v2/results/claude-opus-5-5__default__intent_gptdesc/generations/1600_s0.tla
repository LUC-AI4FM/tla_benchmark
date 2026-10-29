------------------------------ MODULE FastMutex ------------------------------
(***************************************************************************)
(* Fast-path mutual exclusion for N identical processes, in the style of   *)
(* Lamport's fast mutual exclusion algorithm.                              *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   b[i] : process i's advertised intent flag                             *)
(*   x    : fast-path gate (last process to announce itself)               *)
(*   y    : the "owner" indicator (0 means no owner)                       *)
(*                                                                         *)
(* Per-process code (pc labels):                                           *)
(*   ncs : noncritical section                                             *)
(*   l1  : b[i] := TRUE                    (express intent)                *)
(*   l2  : x := i                                                          *)
(*   l3  : IF y # 0 THEN b[i] := FALSE; goto l4 ELSE goto l5               *)
(*   l4  : await y = 0; goto l1            (back off, then retry)          *)
(*   l5  : y := i                          (claim ownership)               *)
(*   l6  : IF x # i THEN b[i] := FALSE; goto l7 (contention detected)      *)
(*         ELSE goto cs                    (fast path succeeded)           *)
(*   l7  : for j := 1 to N: await ~b[j]    (slow path: wait for window)    *)
(*   l8  : IF y # i THEN goto l9 ELSE goto cs                              *)
(*   l9  : await y = 0; goto l1            (back off, then retry)          *)
(*   cs  : critical section                                                *)
(*   e1  : y := 0                          (release ownership)             *)
(*   e2  : b[i] := FALSE; goto ncs         (clear intent)                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 1

Procs == 1..N

Labels == {"ncs", "l1", "l2", "l3", "l4", "l5", "l6",
           "l7", "l8", "l9", "cs", "e1", "e2"}

VARIABLES
    pc,   \* pc[i]  : control location of process i
    b,    \* b[i]   : intent flag of process i
    x,    \* fast-path gate
    y,    \* owner indicator (0 = none)
    j     \* j[i]   : loop index for slow-path scan of process i

vars == <<pc, b, x, y, j>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Procs -> Labels]
    /\ b  \in [Procs -> BOOLEAN]
    /\ x  \in 0..N
    /\ y  \in 0..N
    /\ j  \in [Procs -> 1..(N+1)]

Init ==
    /\ pc = [i \in Procs |-> "ncs"]
    /\ b  = [i \in Procs |-> FALSE]
    /\ x  = 0
    /\ y  = 0
    /\ j  = [i \in Procs |-> 1]

-----------------------------------------------------------------------------
(* Process actions *)

NCS(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "l1"]
    /\ UNCHANGED <<b, x, y, j>>

L1(i) ==   \* express intent
    /\ pc[i] = "l1"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "l2"]
    /\ UNCHANGED <<x, y, j>>

L2(i) ==   \* announce on fast gate
    /\ pc[i] = "l2"
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "l3"]
    /\ UNCHANGED <<b, y, j>>

L3(i) ==   \* check for an existing owner
    /\ pc[i] = "l3"
    /\ IF y # 0
          THEN /\ b'  = [b EXCEPT ![i] = FALSE]
               /\ pc' = [pc EXCEPT ![i] = "l4"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "l5"]
               /\ b'  = b
    /\ UNCHANGED <<x, y, j>>

L4(i) ==   \* back off until owner releases, then retry
    /\ pc[i] = "l4"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "l1"]
    /\ UNCHANGED <<b, x, y, j>>

L5(i) ==   \* claim ownership
    /\ pc[i] = "l5"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "l6"]
    /\ UNCHANGED <<b, x, j>>

L6(i) ==   \* fast-path test
    /\ pc[i] = "l6"
    /\ IF x # i
          THEN /\ b'  = [b EXCEPT ![i] = FALSE]
               /\ j'  = [j EXCEPT ![i] = 1]
               /\ pc' = [pc EXCEPT ![i] = "l7"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
               /\ UNCHANGED <<b, j>>
    /\ UNCHANGED <<x, y>>

L7(i) ==   \* slow path: wait until each other process is not interested
    /\ pc[i] = "l7"
    /\ IF j[i] <= N
          THEN /\ ~b[j[i]]
               /\ j'  = [j EXCEPT ![i] = j[i] + 1]
               /\ pc' = pc
          ELSE /\ pc' = [pc EXCEPT ![i] = "l8"]
               /\ j'  = j
    /\ UNCHANGED <<b, x, y>>

L8(i) ==   \* still owner?
    /\ pc[i] = "l8"
    /\ IF y # i
          THEN pc' = [pc EXCEPT ![i] = "l9"]
          ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<b, x, y, j>>

L9(i) ==   \* lost: back off until owner releases, then retry
    /\ pc[i] = "l9"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "l1"]
    /\ UNCHANGED <<b, x, y, j>>

CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "e1"]
    /\ UNCHANGED <<b, x, y, j>>

E1(i) ==   \* release ownership indicator
    /\ pc[i] = "e1"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![i] = "e2"]
    /\ UNCHANGED <<b, x, j>>

E2(i) ==   \* clear advertised intent
    /\ pc[i] = "e2"
    /\ b'  = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y, j>>

Proc(i) ==
    \/ NCS(i) \/ L1(i) \/ L2(i) \/ L3(i) \/ L4(i) \/ L5(i) \/ L6(i)
    \/ L7(i)  \/ L8(i) \/ L9(i) \/ CS(i) \/ E1(i) \/ E2(i)

Next == \E i \in Procs : Proc(i)

(* Weak fairness for every process: no process halts forever while it has *)
(* an enabled step (processes keep cycling and attempting entry).          *)
Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

InCS(i) == pc[i] = "cs"

\* No process is aborted in this model, so every process counts as
\* "non-aborted"; at most one may be in the critical section.
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(InCS(p) /\ InCS(q))

\* Proper cleanup (state form): a process in its noncritical section
\* advertises no intent and holds no ownership marker.
CleanupInvariant ==
    \A i \in Procs : pc[i] = "ncs" => (~b[i] /\ y # i)

\* Proper cleanup (action form): completing the exit protocol leaves the
\* intent flag cleared and the ownership indicator not held by the process.
CleanupOnExit ==
    [][\A i \in Procs :
         (pc[i] = "e2" /\ pc'[i] = "ncs") => (~b'[i] /\ y' # i)]_vars

\* The release step actually resets the owner indicator.
ReleaseResetsOwner ==
    [][\A i \in Procs :
         (pc[i] = "e1" /\ pc'[i] = "e2") => (y' = 0)]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

Trying(i) == pc[i] \in {"l1", "l2", "l3", "l4", "l5", "l6", "l7", "l8", "l9"}

\* Global progress / no permanent starvation of the system:
\* from any reachable state, some process eventually enters the CS.
GlobalProgress == []<>(\E i \in Procs : InCS(i))

\* Deadlock freedom: if some process is trying, some process eventually
\* enters the critical section.
DeadlockFreedom ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))

\* Progress under contention detection: a process that failed the fast
\* attempt (is on the slow path) completes it, either entering the CS or
\* backing off to retry, or else the system as a whole makes progress.
SlowPathProgress ==
    \A i \in Procs :
        (pc[i] \in {"l7", "l8", "l9"})
            ~> (pc[i] \in {"cs", "l1"} \/ \E k \in Procs : InCS(k))

\* A process that backed off after detecting contention gets to retry,
\* or someone enters the critical section.
BackoffProgress ==
    \A i \in Procs :
        (pc[i] = "l4") ~> (pc[i] = "l1" \/ \E k \in Procs : InCS(k))

\* A process in the critical section always leaves and finishes cleanup.
ExitCompletes ==
    \A i \in Procs : InCS(i) ~> (pc[i] = "ncs")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion /\ CleanupInvariant)
THEOREM Spec => CleanupOnExit /\ ReleaseResetsOwner
THEOREM Spec => GlobalProgress /\ DeadlockFreedom /\ SlowPathProgress
                /\ BackoffProgress /\ ExitCompletes
=============================================================================