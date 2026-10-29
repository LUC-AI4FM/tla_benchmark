---------------------------- MODULE MCSession8peterson ----------------------------
(***************************************************************************)
(* Model-checking configuration for Peterson's mutual exclusion algorithm, *)
(* generalized to N processes (the "filter" algorithm).                    *)
(*                                                                         *)
(* The model is instantiated with three processes, numbered 0 through 2:   *)
(*     N     <- 3                                                          *)
(*     Procs <- {0, 1, 2}                                                  *)
(*                                                                         *)
(* The algorithm is defined in this module so that it is self-contained.   *)
(* In the teaching series it would come from the Session8peterson module,  *)
(* and other variants could be substituted for comparison, for example:    *)
(*     \* EXTENDS Session8onebit                                           *)
(*     \* EXTENDS Session8alternative                                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ASSUME /\ N \in Nat
       /\ N >= 1
       /\ Procs = 0 .. (N - 1)

(* Configuration values used for model checking: N = 3, Procs = {0,1,2}    *)
MC_N     == 3
MC_Procs == {0, 1, 2}

Levels == 1 .. (N - 1)

VARIABLES
    pc,     \* pc[p] : control state of process p
    level,  \* level[p] : the level process p currently occupies (0 = none)
    last,   \* last[l] : the last process that entered level l
    lv      \* lv[p] : the level process p is currently trying to enter

vars == << pc, level, last, lv >>

PCs == {"ncs", "setlevel", "setlast", "wait", "cs", "exit"}

TypeOK ==
    /\ pc    \in [Procs -> PCs]
    /\ level \in [Procs -> 0 .. (N - 1)]
    /\ last  \in [Levels -> Procs]
    /\ lv    \in [Procs -> 0 .. (N - 1)]

Init ==
    /\ pc    = [p \in Procs |-> "ncs"]
    /\ level = [p \in Procs |-> 0]
    /\ last  = [l \in Levels |-> 0]
    /\ lv    = [p \in Procs |-> 0]

(* Leave the non-critical section and start competing *)
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ IF N = 1
         THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED lv
         ELSE /\ lv' = [lv EXCEPT ![p] = 1]
              /\ pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ UNCHANGED << level, last >>

(* level[p] := lv[p] *)
SetLevel(p) ==
    /\ pc[p] = "setlevel"
    /\ level' = [level EXCEPT ![p] = lv[p]]
    /\ pc' = [pc EXCEPT ![p] = "setlast"]
    /\ UNCHANGED << last, lv >>

(* last[lv[p]] := p *)
SetLast(p) ==
    /\ pc[p] = "setlast"
    /\ last' = [last EXCEPT ![lv[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED << level, lv >>

(* await (\A k # p : level[k] < lv[p]) \/ last[lv[p]] # p *)
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ \A k \in Procs \ {p} : level[k] < lv[p]
       \/ last[lv[p]] # p
    /\ IF lv[p] < N - 1
         THEN /\ lv' = [lv EXCEPT ![p] = lv[p] + 1]
              /\ pc' = [pc EXCEPT ![p] = "setlevel"]
         ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED lv
    /\ UNCHANGED << level, last >>

(* Critical section *)
CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED << level, last, lv >>

(* Exit protocol: level[p] := 0 *)
Exit(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ lv' = [lv EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED last

(* Steps a process is obliged to eventually take (it may stay in ncs) *)
Progress(p) ==
    \/ SetLevel(p)
    \/ SetLast(p)
    \/ Wait(p)
    \/ CS(p)
    \/ Exit(p)

Proc(p) == NCS(p) \/ Progress(p)

Next == \E p \in Procs : Proc(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Procs : WF_vars(Progress(p))

-----------------------------------------------------------------------------
(* Safety: no two distinct processes are in the critical section at once *)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness: every process that starts competing eventually enters cs *)
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "setlevel") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================