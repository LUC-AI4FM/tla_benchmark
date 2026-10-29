------------------------------ MODULE FastMutex ------------------------------
(***************************************************************************)
(* Lamport's Fast Mutual Exclusion algorithm for N processes.              *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   x  : register holding the id of the last process to announce itself   *)
(*   y  : register; 0 means "free", otherwise the id of a contender         *)
(*   b  : array of per-process boolean flags                               *)
(*                                                                         *)
(* Process code (for process i):                                           *)
(*   ncs:   noncritical section                                            *)
(*   start: b[i] := TRUE                                                   *)
(*   l1:    x := i                                                         *)
(*   l2:    if y # 0 then { l3: b[i] := FALSE;                             *)
(*                          l4: await y = 0; goto start }                  *)
(*   l5:    y := i                                                         *)
(*   l6:    if x # i then { l7: b[i] := FALSE;                             *)
(*                          l8: await \A j : ~b[j];                        *)
(*                          l9: if y # i then { l10: await y = 0;          *)
(*                                              goto start } }             *)
(*   cs:    critical section                                               *)
(*   l11:   y := 0                                                         *)
(*   l12:   b[i] := FALSE; goto ncs                                        *)
(*                                                                         *)
(* Model check with a small concrete value, e.g. N = 3.                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5", "l6", "l7",
           "l8", "l9", "l10", "cs", "l11", "l12"}

TypeOK ==
    /\ x \in Procs \cup {0}
    /\ y \in Procs \cup {0}
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> Labels]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]

Ncs(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b>>

Start(i) ==
    /\ pc[i] = "start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "l1"]
    /\ UNCHANGED <<x, y>>

L1(i) ==
    /\ pc[i] = "l1"
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "l2"]
    /\ UNCHANGED <<y, b>>

L2(i) ==
    /\ pc[i] = "l2"
    /\ IF y # 0
          THEN pc' = [pc EXCEPT ![i] = "l3"]
          ELSE pc' = [pc EXCEPT ![i] = "l5"]
    /\ UNCHANGED <<x, y, b>>

L3(i) ==
    /\ pc[i] = "l3"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "l4"]
    /\ UNCHANGED <<x, y>>

L4(i) ==
    /\ pc[i] = "l4"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b>>

L5(i) ==
    /\ pc[i] = "l5"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "l6"]
    /\ UNCHANGED <<x, b>>

L6(i) ==
    /\ pc[i] = "l6"
    /\ IF x # i
          THEN pc' = [pc EXCEPT ![i] = "l7"]
          ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b>>

L7(i) ==
    /\ pc[i] = "l7"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "l8"]
    /\ UNCHANGED <<x, y>>

L8(i) ==
    /\ pc[i] = "l8"
    /\ \A j \in Procs : ~b[j]
    /\ pc' = [pc EXCEPT ![i] = "l9"]
    /\ UNCHANGED <<x, y, b>>

L9(i) ==
    /\ pc[i] = "l9"
    /\ IF y # i
          THEN pc' = [pc EXCEPT ![i] = "l10"]
          ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b>>

L10(i) ==
    /\ pc[i] = "l10"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b>>

CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "l11"]
    /\ UNCHANGED <<x, y, b>>

L11(i) ==
    /\ pc[i] = "l11"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![i] = "l12"]
    /\ UNCHANGED <<x, b>>

L12(i) ==
    /\ pc[i] = "l12"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y>>

Proc(i) ==
    \/ Ncs(i) \/ Start(i) \/ L1(i) \/ L2(i) \/ L3(i) \/ L4(i)
    \/ L5(i) \/ L6(i) \/ L7(i) \/ L8(i) \/ L9(i) \/ L10(i)
    \/ CS(i) \/ L11(i) \/ L12(i)

Next == \E i \in Procs : Proc(i)

Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety: mutual exclusion.                                               *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Liveness: some process enters the critical section infinitely often.    *)
(***************************************************************************)
DeadlockFreedom ==
    (\E i \in Procs : pc[i] \notin {"ncs", "cs", "l11", "l12"})
        ~> (\E i \in Procs : pc[i] = "cs")

InfinitelyOftenCS == []<>(\E i \in Procs : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => InfinitelyOftenCS
=============================================================================