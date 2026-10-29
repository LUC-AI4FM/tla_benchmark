---------------------------- MODULE Session8MC ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style (filter) mutual exclusion   *)
(* protocol. The original wrapper EXTENDS Session8peterson. To keep this   *)
(* module self-contained and parseable by SANY, the Peterson filter        *)
(* protocol over the state variables Procs and pc is inlined here.         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS ConstN

ASSUME ConstN \in Nat /\ ConstN >= 1

(* Concrete process count and process index range used for checking *)
N == 3

ProcSet == 0..(N - 1)

Levels == 1..(N - 1)

VARIABLES
    Procs,   \* set of participating process identifiers
    pc,      \* program counter of each process
    level,   \* current level of each process in the filter lock
    last,    \* last process to enter each level
    lv       \* local loop counter of each process

vars == <<Procs, pc, level, last, lv>>

PCs == {"ncs", "setlevel", "wait", "cs", "exit"}

TypeOK ==
    /\ Procs = ProcSet
    /\ pc \in [ProcSet -> PCs]
    /\ level \in [ProcSet -> 0..(N - 1)]
    /\ last \in [Levels -> ProcSet]
    /\ lv \in [ProcSet -> 0..N]

Init ==
    /\ Procs = ProcSet
    /\ pc = [i \in ProcSet |-> "ncs"]
    /\ level = [i \in ProcSet |-> 0]
    /\ last = [l \in Levels |-> 0]
    /\ lv = [i \in ProcSet |-> 0]

(* Leave non-critical section and start climbing the filter levels *)
NCS(i) ==
    /\ pc[i] = "ncs"
    /\ lv' = [lv EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "setlevel"]
    /\ UNCHANGED <<Procs, level, last>>

(* Announce entry to level lv[i], or enter the critical section *)
SetLevel(i) ==
    /\ pc[i] = "setlevel"
    /\ IF lv[i] < N
          THEN /\ level' = [level EXCEPT ![i] = lv[i]]
               /\ last' = [last EXCEPT ![lv[i]] = i]
               /\ pc' = [pc EXCEPT ![i] = "wait"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
               /\ UNCHANGED <<level, last>>
    /\ UNCHANGED <<Procs, lv>>

(* Wait until no other process is at an equal or higher level, *)
(* or some other process has become the last at this level.     *)
Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ last[lv[i]] # i
       \/ \A k \in Procs \ {i} : level[k] < lv[i]
    /\ lv' = [lv EXCEPT ![i] = lv[i] + 1]
    /\ pc' = [pc EXCEPT ![i] = "setlevel"]
    /\ UNCHANGED <<Procs, level, last>>

(* Execute the critical section *)
CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<Procs, level, last, lv>>

(* Release the lock *)
Exit(i) ==
    /\ pc[i] = "exit"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<Procs, last, lv>>

Proc(i) ==
    \/ NCS(i)
    \/ SetLevel(i)
    \/ Wait(i)
    \/ CS(i)
    \/ Exit(i)

Next == \E i \in ProcSet : Proc(i)

Spec == Init /\ [][Next]_vars /\ \A i \in ProcSet : WF_vars(Proc(i))

(***************************************************************************)
(* Safety assertion checked by this wrapper: mutual exclusion.            *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)

=============================================================================