---------------------------- MODULE MCSession9peterson ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style mutual exclusion algorithm. *)
(* The original wrapper EXTENDS Session9peterson. To keep this module      *)
(* self-contained and parseable on its own, the algorithm is restated      *)
(* here. It is the classic two-process Peterson algorithm with the         *)
(* control locations "ncs", "enter", "wait", "cs" and "exit".              *)
(***************************************************************************)
EXTENDS Naturals, TLC

(***************************************************************************)
(* Concrete constants for model checking                                   *)
(***************************************************************************)
N == 2            \* number of processes
P == 1 .. N       \* process identifiers

Other(p) == CHOOSE q \in P : q # p

VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

TypeOK ==
    /\ flag \in [P -> BOOLEAN]
    /\ turn \in P
    /\ pc   \in [P -> {"ncs", "enter", "wait", "cs", "exit"}]

Init ==
    /\ flag = [p \in P |-> FALSE]
    /\ turn \in P
    /\ pc   = [p \in P |-> "ncs"]

(* Leave the non-critical section (may never happen) *)
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED << flag, turn >>

(* Announce interest and give priority to the other process *)
Enter(p) ==
    /\ pc[p] = "enter"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ turn' = Other(p)
    /\ pc'   = [pc EXCEPT ![p] = "wait"]

(* Wait until the other is not interested or it is our turn *)
Wait(p) ==
    /\ pc[p] = "wait"
    /\ (~flag[Other(p)] \/ turn = p)
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED << flag, turn >>

(* Critical section *)
CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED << flag, turn >>

(* Exit protocol *)
Exit(p) ==
    /\ pc[p] = "exit"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ pc'   = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED turn

(* Steps of process p that must eventually be taken when enabled *)
Proc(p) == Enter(p) \/ Wait(p) \/ CS(p) \/ Exit(p)

Next == \E p \in P : NCS(p) \/ Proc(p)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in P : WF_vars(Proc(p))

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

(* No two distinct processes are simultaneously in the critical section *)
MutualExclusion ==
    \A p, q \in P : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Every process at location "enter" eventually reaches location "cs" *)
StarvationFreedom ==
    \A p \in P : (pc[p] = "enter") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=============================================================================