---------------------------- MODULE MCSession8peterson ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style (filter) mutual exclusion   *)
(* protocol. The original wrapper imports Session8peterson; the protocol   *)
(* is inlined here so this module parses on its own. It fixes the process *)
(* count to 3, defines the process index range 0..(ConstN-1), and states  *)
(* the mutual exclusion safety property over the state variables Procs    *)
(* and pc.                                                                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N

(* Concrete constants for model checking *)
ConstN == 3
ConstProcs == 0..(ConstN - 1)

VARIABLES
    Procs,   \* the set of participating process indices
    pc,      \* program counter of each process
    level,   \* current level of each process (-1 = not competing)
    last,    \* last[k] = the process that most recently entered level k
    l        \* local level counter of each process

vars == << Procs, pc, level, last, l >>

Levels == 0..(ConstN - 2)

Labels == {"ncs", "setlevel", "setlast", "wait", "cs"}

TypeOK ==
    /\ Procs = ConstProcs
    /\ pc \in [ConstProcs -> Labels]
    /\ level \in [ConstProcs -> (-1)..(ConstN - 2)]
    /\ last \in [Levels -> ConstProcs]
    /\ l \in [ConstProcs -> 0..(ConstN - 1)]

Init ==
    /\ Procs = ConstProcs
    /\ pc = [i \in ConstProcs |-> "ncs"]
    /\ level = [i \in ConstProcs |-> -1]
    /\ last = [k \in Levels |-> 0]
    /\ l = [i \in ConstProcs |-> 0]

(* Leave the non-critical section and start competing *)
Enter(i) ==
    /\ pc[i] = "ncs"
    /\ l' = [l EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "setlevel"]
    /\ UNCHANGED << Procs, level, last >>

(* Either announce the next level or, having passed all levels, enter CS *)
SetLevel(i) ==
    /\ pc[i] = "setlevel"
    /\ IF l[i] < ConstN - 1
          THEN /\ level' = [level EXCEPT ![i] = l[i]]
               /\ pc' = [pc EXCEPT ![i] = "setlast"]
          ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
               /\ UNCHANGED level
    /\ UNCHANGED << Procs, last, l >>

(* Become the victim at the current level *)
SetLast(i) ==
    /\ pc[i] = "setlast"
    /\ last' = [last EXCEPT ![l[i]] = i]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED << Procs, level, l >>

(* Wait until no longer the victim, or no other process is at >= this level *)
Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ last[l[i]] # i
       \/ \A k \in Procs \ {i} : level[k] < l[i]
    /\ l' = [l EXCEPT ![i] = l[i] + 1]
    /\ pc' = [pc EXCEPT ![i] = "setlevel"]
    /\ UNCHANGED << Procs, level, last >>

(* Leave the critical section *)
Exit(i) ==
    /\ pc[i] = "cs"
    /\ level' = [level EXCEPT ![i] = -1]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED << Procs, last, l >>

Proc(i) ==
    \/ Enter(i)
    \/ SetLevel(i)
    \/ SetLast(i)
    \/ Wait(i)
    \/ Exit(i)

Next == \E i \in ConstProcs : Proc(i)

(* Processes may stay in the non-critical section forever, but they make
   progress once they compete or are in the critical section. *)
Fairness ==
    \A i \in ConstProcs :
        /\ WF_vars(SetLevel(i))
        /\ WF_vars(SetLast(i))
        /\ WF_vars(Wait(i))
        /\ WF_vars(Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety: no two distinct processes are in the critical section at once. *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness: every process that starts competing eventually enters the CS *)
StarvationFreedom ==
    \A i \in ConstProcs : (pc[i] = "setlevel") ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
====================================================================================