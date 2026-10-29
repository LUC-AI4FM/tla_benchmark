---------------------------- MODULE Session8petersonMC ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style (filter) mutual exclusion   *)
(* protocol. The original wrapper EXTENDS Session8peterson; that protocol  *)
(* is inlined here so the module is self-contained and parses with SANY.   *)
(* It fixes the process count to 3, uses the process index range           *)
(* 0..(ConstN-1), and states mutual exclusion over Procs and pc.           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

\* Concrete process count used for model checking
ConstN == 3

\* Process index range
ConstProcSet == 0..(ConstN - 1)

\* Filter levels (0 means "not competing")
Levels == 0..(ConstN - 1)
ActiveLevels == 1..(ConstN - 1)

VARIABLES
    Procs,   \* Procs[p] : current level of process p
    last,    \* last[l]  : the last process to enter level l (the "victim")
    pc       \* pc[p]    : program counter of process p

vars == <<Procs, last, pc>>

PCs == {"ncs", "wait", "cs"}

TypeOK ==
    /\ Procs \in [ConstProcSet -> Levels]
    /\ last  \in [ActiveLevels -> ConstProcSet]
    /\ pc    \in [ConstProcSet -> PCs]

Init ==
    /\ Procs = [p \in ConstProcSet |-> 0]
    /\ last  = [l \in ActiveLevels |-> 0]
    /\ pc    = [p \in ConstProcSet |-> "ncs"]

\* Leave the non-critical section: enter level 1 and become its victim
Request(p) ==
    /\ pc[p] = "ncs"
    /\ Procs' = [Procs EXCEPT ![p] = 1]
    /\ last'  = [last EXCEPT ![1] = p]
    /\ pc'    = [pc EXCEPT ![p] = "wait"]

\* Wait condition at the current level
CanAdvance(p) ==
    LET l == Procs[p] IN
        \/ \A k \in ConstProcSet \ {p} : Procs[k] < l
        \/ last[l] # p

\* Advance one level, or enter the critical section from the top level
Advance(p) ==
    /\ pc[p] = "wait"
    /\ CanAdvance(p)
    /\ IF Procs[p] = ConstN - 1
         THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
              /\ UNCHANGED <<Procs, last>>
         ELSE /\ Procs' = [Procs EXCEPT ![p] = Procs[p] + 1]
              /\ last'  = [last EXCEPT ![Procs[p] + 1] = p]
              /\ UNCHANGED pc

\* Leave the critical section
Exit(p) ==
    /\ pc[p] = "cs"
    /\ Procs' = [Procs EXCEPT ![p] = 0]
    /\ pc'    = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED last

Proc(p) == Request(p) \/ Advance(p) \/ Exit(p)

Next == \E p \in ConstProcSet : Proc(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in ConstProcSet : WF_vars(Advance(p) \/ Exit(p))

(***************************************************************************)
(* Safety: no two distinct processes are in the critical section at once.  *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in ConstProcSet :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================