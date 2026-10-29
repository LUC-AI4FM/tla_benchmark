------------------------------ MODULE MCSession9peterson ------------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style (filter) mutual exclusion   *)
(* algorithm. The algorithm from Session9peterson is inlined here so that  *)
(* the module is self-contained and parses with SANY. The wrapper gives    *)
(* concrete values for the number of processes and the process range, and *)
(* states two properties: mutual exclusion and starvation freedom.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(* Concrete constant value for model checking (use N <- MC_N in the config) *)
MC_N == 3

(* Process identifier range *)
P == 1..N

VARIABLES pc, level, last, l

vars == << pc, level, last, l >>

Locations == {"ncs", "enter", "wait", "cs"}

TypeOK ==
    /\ pc    \in [P -> Locations]
    /\ level \in [P -> 0..(N-1)]
    /\ last  \in [1..(N-1) -> P]
    /\ l     \in [P -> 1..N]

Init ==
    /\ pc    = [p \in P |-> "ncs"]
    /\ level = [p \in P |-> 0]
    /\ last  = [i \in 1..(N-1) |-> 1]
    /\ l     = [p \in P |-> 1]

(* Process leaves the non-critical section and wants to enter *)
Request(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ l'  = [l EXCEPT ![p] = 1]
    /\ UNCHANGED << level, last >>

(* Process announces its level and yields to others at that level, *)
(* or, having passed all levels, enters the critical section.       *)
Enter(p) ==
    /\ pc[p] = "enter"
    /\ IF l[p] < N
         THEN /\ level' = [level EXCEPT ![p] = l[p]]
              /\ last'  = [last EXCEPT ![l[p]] = p]
              /\ pc'    = [pc EXCEPT ![p] = "wait"]
         ELSE /\ pc'    = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED << level, last >>
    /\ UNCHANGED l

(* Process waits until no other process is at its level or higher, *)
(* or until another process has become the last at its level.      *)
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ \A q \in P \ {p} : level[q] < l[p]
       \/ last[l[p]] # p
    /\ l'  = [l EXCEPT ![p] = l[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED << level, last >>

(* Process leaves the critical section *)
Exit(p) ==
    /\ pc[p] = "cs"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ pc'    = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED << last, l >>

Proc(p) == Request(p) \/ Enter(p) \/ Wait(p) \/ Exit(p)

Next == \E p \in P : Proc(p)

(* No fairness on Request: processes may stay in "ncs" forever. *)
Fairness ==
    \A p \in P : SF_vars(Enter(p) \/ Wait(p) \/ Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

(* No two distinct processes are simultaneously in the critical section *)
MutualExclusion ==
    \A p, q \in P : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Any process at location "enter" eventually reaches location "cs" *)
StarvationFreedom ==
    \A p \in P : (pc[p] = "enter") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=========================================================================================