---------------------------- MODULE PetersonN ----------------------------
(***************************************************************************)
(* Peterson's mutual exclusion algorithm for N processes (filter lock).   *)
(* For verification, instantiate with N = 3.                              *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 2

Procs  == 0..(N-1)
Levels == 1..(N-1)

VARIABLES
    level,   \* level[i]: level process i currently occupies (0 = not competing)
    victim,  \* victim[L]: last process to arrive at level L
    pc,      \* program counter of each process
    lv       \* lv[i]: the level process i is currently working on

vars == << level, victim, pc, lv >>

PCs == {"ncs", "setlevel", "setvictim", "wait", "cs", "exit"}

TypeOK ==
    /\ level  \in [Procs -> 0..(N-1)]
    /\ victim \in [Levels -> Procs]
    /\ pc     \in [Procs -> PCs]
    /\ lv     \in [Procs -> 0..(N-1)]

Init ==
    /\ level  = [i \in Procs |-> 0]
    /\ victim = [L \in Levels |-> 0]
    /\ pc     = [i \in Procs |-> "ncs"]
    /\ lv     = [i \in Procs |-> 0]

\* Leave the non-critical section and start the entry protocol at level 1.
\* (No fairness: a process may stay in its non-critical section forever.)
TryEnter(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "setlevel"]
    /\ lv' = [lv EXCEPT ![i] = 1]
    /\ UNCHANGED << level, victim >>

\* level[i] := L
SetLevel(i) ==
    /\ pc[i] = "setlevel"
    /\ level' = [level EXCEPT ![i] = lv[i]]
    /\ pc' = [pc EXCEPT ![i] = "setvictim"]
    /\ UNCHANGED << victim, lv >>

\* victim[L] := i
SetVictim(i) ==
    /\ pc[i] = "setvictim"
    /\ victim' = [victim EXCEPT ![lv[i]] = i]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED << level, lv >>

\* await (\A k # i : level[k] < L) \/ victim[L] # i
Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ \A k \in Procs \ {i} : level[k] < lv[i]
       \/ victim[lv[i]] # i
    /\ IF lv[i] < N - 1
         THEN /\ lv' = [lv EXCEPT ![i] = lv[i] + 1]
              /\ pc' = [pc EXCEPT ![i] = "setlevel"]
         ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
              /\ UNCHANGED lv
    /\ UNCHANGED << level, victim >>

\* Leave the critical section.
LeaveCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED << level, victim, lv >>

\* Exit protocol: level[i] := 0
Exit(i) ==
    /\ pc[i] = "exit"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ lv' = [lv EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED victim

Proc(i) ==
    \/ TryEnter(i)
    \/ SetLevel(i)
    \/ SetVictim(i)
    \/ Wait(i)
    \/ LeaveCS(i)
    \/ Exit(i)

Next == \E i \in Procs : Proc(i)

Fairness ==
    \A i \in Procs :
        /\ WF_vars(SetLevel(i))
        /\ WF_vars(SetVictim(i))
        /\ SF_vars(Wait(i))
        /\ WF_vars(LeaveCS(i))
        /\ WF_vars(Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness *)

Trying(i) == pc[i] \in {"setlevel", "setvictim", "wait"}

StarvationFreedom ==
    \A i \in Procs : Trying(i) ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=============================================================================