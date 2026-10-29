---------------------------- MODULE MCSession8peterson ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style (filter) mutual exclusion   *)
(* protocol. The original wrapper EXTENDS Session8peterson; the protocol    *)
(* is included inline here so the module is self-contained for SANY.       *)
(*                                                                         *)
(* Alternative candidates considered in the original file:                 *)
(*   \* EXTENDS Session8dekker                                             *)
(*   \* EXTENDS Session8naive                                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

(***************************************************************************)
(* Concrete constants supplied by the wrapper                              *)
(***************************************************************************)
ConstN == 3

ProcSet == 0..(ConstN - 1)

Levels == 1..(ConstN - 1)

NoProc == -1

(***************************************************************************)
(* State variables of the imported Peterson-style model                    *)
(*   Procs[i] : the level process i currently occupies (0 = not trying)    *)
(*   last[l]  : the last process to enter level l (the "victim")           *)
(*   cur[i]   : the level process i is currently attempting                *)
(*   pc[i]    : the control location of process i                          *)
(***************************************************************************)
VARIABLES Procs, last, cur, pc

vars == << Procs, last, cur, pc >>

Labels == {"ncs", "setlevel", "setlast", "wait", "cs"}

TypeOK ==
    /\ Procs \in [ProcSet -> 0..(ConstN - 1)]
    /\ last  \in [Levels -> ProcSet \cup {NoProc}]
    /\ cur   \in [ProcSet -> 0..(ConstN - 1)]
    /\ pc    \in [ProcSet -> Labels]

Init ==
    /\ Procs = [i \in ProcSet |-> 0]
    /\ last  = [l \in Levels  |-> NoProc]
    /\ cur   = [i \in ProcSet |-> 0]
    /\ pc    = [i \in ProcSet |-> "ncs"]

(***************************************************************************)
(* Process actions                                                         *)
(***************************************************************************)
Try(i) ==
    /\ pc[i] = "ncs"
    /\ cur' = [cur EXCEPT ![i] = 1]
    /\ pc'  = [pc  EXCEPT ![i] = "setlevel"]
    /\ UNCHANGED << Procs, last >>

SetLevel(i) ==
    /\ pc[i] = "setlevel"
    /\ Procs' = [Procs EXCEPT ![i] = cur[i]]
    /\ pc'    = [pc    EXCEPT ![i] = "setlast"]
    /\ UNCHANGED << last, cur >>

SetLast(i) ==
    /\ pc[i] = "setlast"
    /\ last' = [last EXCEPT ![cur[i]] = i]
    /\ pc'   = [pc   EXCEPT ![i] = "wait"]
    /\ UNCHANGED << Procs, cur >>

Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ \A k \in ProcSet \ {i} : Procs[k] < cur[i]
       \/ last[cur[i]] # i
    /\ IF cur[i] = ConstN - 1
          THEN /\ pc'  = [pc EXCEPT ![i] = "cs"]
               /\ UNCHANGED cur
          ELSE /\ cur' = [cur EXCEPT ![i] = cur[i] + 1]
               /\ pc'  = [pc  EXCEPT ![i] = "setlevel"]
    /\ UNCHANGED << Procs, last >>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ Procs' = [Procs EXCEPT ![i] = 0]
    /\ cur'   = [cur   EXCEPT ![i] = 0]
    /\ pc'    = [pc    EXCEPT ![i] = "ncs"]
    /\ UNCHANGED last

Protocol(i) ==
    \/ SetLevel(i)
    \/ SetLast(i)
    \/ Wait(i)
    \/ Exit(i)

Proc(i) == Try(i) \/ Protocol(i)

Next == \E i \in ProcSet : Proc(i)

Fairness == \A i \in ProcSet : WF_vars(Protocol(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety assertion added by the wrapper                                   *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in ProcSet :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Equivalent formulation over the imported level array Procs *)
AtMostOneInCS ==
    Cardinality({i \in ProcSet : pc[i] = "cs" /\ Procs[i] = ConstN - 1}) <= 1

(***************************************************************************)
(* Liveness: every process that starts trying eventually enters the CS     *)
(***************************************************************************)
StarvationFreedom ==
    \A i \in ProcSet : (pc[i] = "setlevel") ~> (pc[i] = "cs")

DeadlockFreedom ==
    (\E i \in ProcSet : pc[i] \in {"setlevel", "setlast", "wait"})
        ~> (\E i \in ProcSet : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ AtMostOneInCS)
THEOREM Spec => StarvationFreedom /\ DeadlockFreedom
==================================================================================