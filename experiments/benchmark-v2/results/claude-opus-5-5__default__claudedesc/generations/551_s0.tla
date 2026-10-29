---------------------------- MODULE MC_Session9onebit ----------------------------
(***************************************************************************)
(* Model-checking configuration for the one-bit mutual exclusion          *)
(* algorithm. Self-contained: the process behaviour of Session9onebit is  *)
(* inlined so the module parses with SANY on its own.                     *)
(*                                                                         *)
(* Intended model values: N <- 3, Procs <- {0, 1, 2}                       *)
(*                                                                         *)
(* Properties checked:                                                     *)
(*   INVARIANT MutualExclusion                                             *)
(*   PROPERTY  DeadAndLivelockFree                                         *)
(*   PROPERTY  NoStarveProc0                                               *)
(*   \* PROPERTY NoStarveProc1   \* algorithm does not satisfy this        *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS N, Procs

ASSUME /\ N \in Nat \ {0}
       /\ Procs = 0 .. (N - 1)

VARIABLES x, pc, j

vars == << x, pc, j >>

Labels    == {"ncs", "e1", "e2", "e3", "e4", "cs", "exit"}
TryLabels == {"e1", "e2", "e3", "e4"}

TypeOK ==
    /\ x  \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> Labels]
    /\ j  \in [Procs -> 0 .. N]

Init ==
    /\ x  = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ j  = [i \in Procs |-> 0]

(* Leave the non-critical section and start trying *)
NCS(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "e1"]
    /\ UNCHANGED << x, j >>

(* Raise own flag and start scanning lower-numbered processes *)
E1(i) ==
    /\ pc[i] = "e1"
    /\ x'  = [x  EXCEPT ![i] = TRUE]
    /\ j'  = [j  EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "e2"]

(* for k < i: if x[k] then back off *)
E2(i) ==
    /\ pc[i] = "e2"
    /\ IF j[i] < i
         THEN IF x[j[i]]
                THEN /\ x'  = [x  EXCEPT ![i] = FALSE]
                     /\ pc' = [pc EXCEPT ![i] = "e3"]
                     /\ UNCHANGED j
                ELSE /\ j' = [j EXCEPT ![i] = j[i] + 1]
                     /\ UNCHANGED << x, pc >>
         ELSE /\ j'  = [j  EXCEPT ![i] = i + 1]
              /\ pc' = [pc EXCEPT ![i] = "e4"]
              /\ UNCHANGED x

(* After backing off: await ~x[k], then restart *)
E3(i) ==
    /\ pc[i] = "e3"
    /\ ~x[j[i]]
    /\ pc' = [pc EXCEPT ![i] = "e1"]
    /\ UNCHANGED << x, j >>

(* for k > i: await ~x[k] *)
E4(i) ==
    /\ pc[i] = "e4"
    /\ IF j[i] < N
         THEN /\ ~x[j[i]]
              /\ j' = [j EXCEPT ![i] = j[i] + 1]
              /\ UNCHANGED << x, pc >>
         ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
              /\ UNCHANGED << x, j >>

CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED << x, j >>

Exit(i) ==
    /\ pc[i] = "exit"
    /\ x'  = [x  EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED j

(* Steps a process is obliged to take (it may stay in ncs forever) *)
Proc(i) == E1(i) \/ E2(i) \/ E3(i) \/ E4(i) \/ CS(i) \/ Exit(i)

Next == \E i \in Procs : NCS(i) \/ Proc(i)

Fairness == \A i \in Procs : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

MutualExclusion ==
    \A i, k \in Procs : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

DeadAndLivelockFree ==
    (\E i \in Procs : pc[i] \in TryLabels) ~> (\E i \in Procs : pc[i] = "cs")

NoStarveProc0 == (pc[0] \in TryLabels) ~> (pc[0] = "cs")

NoStarveProc1 == (pc[1] \in TryLabels) ~> (pc[1] = "cs")

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadAndLivelockFree
THEOREM Spec => NoStarveProc0
\* NoStarveProc1 is NOT checked: the one-bit algorithm does not satisfy it.
=============================================================================