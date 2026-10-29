---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

(***************************************************************************)
(* Fast-path mutual exclusion with a backup waiting protocol, after        *)
(* Lamport's fast mutual exclusion algorithm.                              *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   x : the last process to enter the fast doorway.                       *)
(*   y : the global indicator. It is 0 when no process holds the doorway.  *)
(*   b : the per-process intent flags.                                     *)
(*                                                                         *)
(* Local state:                                                            *)
(*   j  : the loop index for the backup scan.                              *)
(*   pc : the program counter.                                             *)
(*                                                                         *)
(* Atomicity: each labelled step performs at most one read or one write    *)
(* of a shared variable, and that access is atomic. Each process step is   *)
(* atomic.                                                                 *)
(***************************************************************************)

Procs == 1..N

VARIABLES x, y, b, j, pc

vars == <<x, y, b, j, pc>>

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Procs -> BOOLEAN]
    /\ j \in [Procs -> 1..(N+1)]
    /\ pc \in [Procs -> {"ncs","start","l1","l2","l3","l4","l5","l6",
                         "l7","l8","l9","l10","cs","l11","l12"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ j = [i \in Procs |-> 1]
    /\ pc = [i \in Procs |-> "ncs"]

ncs(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b, j>>

start(i) ==
    /\ pc[i] = "start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "l1"]
    /\ UNCHANGED <<x, y, j>>

l1(i) ==
    /\ pc[i] = "l1"
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "l2"]
    /\ UNCHANGED <<y, b, j>>

l2(i) ==
    /\ pc[i] = "l2"
    /\ IF y # 0
          THEN pc' = [pc EXCEPT ![i] = "l3"]
          ELSE pc' = [pc EXCEPT ![i] = "l5"]
    /\ UNCHANGED <<x, y, b, j>>

l3(i) ==
    /\ pc[i] = "l3"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "l4"]
    /\ UNCHANGED <<x, y, j>>

l4(i) ==
    /\ pc[i] = "l4"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b, j>>

l5(i) ==
    /\ pc[i] = "l5"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "l6"]
    /\ UNCHANGED <<x, b, j>>

l6(i) ==
    /\ pc[i] = "l6"
    /\ IF x # i
          THEN pc' = [pc EXCEPT ![i] = "l7"]
          ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b, j>>

l7(i) ==
    /\ pc[i] = "l7"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ j' = [j EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "l8"]
    /\ UNCHANGED <<x, y>>

l8(i) ==
    /\ pc[i] = "l8"
    /\ IF j[i] <= N
          THEN /\ ~b[j[i]]
               /\ j' = [j EXCEPT ![i] = j[i] + 1]
               /\ pc' = [pc EXCEPT ![i] = "l8"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "l9"]
               /\ UNCHANGED j
    /\ UNCHANGED <<x, y, b>>

l9(i) ==
    /\ pc[i] = "l9"
    /\ IF y # i
          THEN pc' = [pc EXCEPT ![i] = "l10"]
          ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b, j>>

l10(i) ==
    /\ pc[i] = "l10"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b, j>>

cs(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "l11"]
    /\ UNCHANGED <<x, y, b, j>>

l11(i) ==
    /\ pc[i] = "l11"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![i] = "l12"]
    /\ UNCHANGED <<x, b, j>>

l12(i) ==
    /\ pc[i] = "l12"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y, j>>

Proc(i) ==
    \/ ncs(i) \/ start(i) \/ l1(i) \/ l2(i) \/ l3(i) \/ l4(i)
    \/ l5(i) \/ l6(i) \/ l7(i) \/ l8(i) \/ l9(i) \/ l10(i)
    \/ cs(i) \/ l11(i) \/ l12(i)

Next == \E i \in Procs : Proc(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Procs : WF_vars(Proc(i))

(* Safety: mutual exclusion. *)
MutualExclusion ==
    \A i, k \in Procs : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Invariant == TypeOK /\ MutualExclusion

(* Liveness: deadlock freedom. If some process is trying, then some       *)
(* process eventually enters the critical section.                        *)
Trying == {"start","l1","l2","l3","l4","l5","l6","l7","l8","l9","l10"}

Liveness ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E i \in Procs : pc[i] = "cs")

====