------------------------------ MODULE FilterMutex ------------------------------
(***************************************************************************)
(* N-process mutual exclusion using Peterson's filter algorithm.            *)
(* Each process moves through N-1 waiting levels before entering the       *)
(* critical section. At each level it announces intent through level[i],   *)
(* volunteers as that level's victim, and waits until either no other      *)
(* process is at the same or a higher level, or until another process has  *)
(* replaced it as victim. Each step reads or writes simple shared          *)
(* variables, and the model abstracts away timing.                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs  == 1..N
Levels == 1..(N-1)          \* waiting levels (empty when N = 1)
None   == 0                 \* neutral value for victim slots

VARIABLES
    pc,        \* pc[i]     : control stage of process i
    lvl,       \* lvl[i]    : local current level that process i is working on
    level,     \* level[i]  : shared, announced level of process i (0 = not competing)
    victim     \* victim[l] : shared, last process to arrive at level l

vars == << pc, lvl, level, victim >>

Stages  == {"ncs", "setLevel", "setVictim", "wait", "cs", "exit"}
Trying  == {"setLevel", "setVictim", "wait"}

-----------------------------------------------------------------------------
TypeOK ==
    /\ pc     \in [Procs -> Stages]
    /\ lvl    \in [Procs -> 0..(N-1)]
    /\ level  \in [Procs -> 0..(N-1)]
    /\ victim \in [Levels -> Procs \cup {None}]

Init ==
    /\ pc     = [i \in Procs  |-> "ncs"]
    /\ lvl    = [i \in Procs  |-> 0]
    /\ level  = [i \in Procs  |-> 0]
    /\ victim = [l \in Levels |-> None]

-----------------------------------------------------------------------------
(* Leave noncritical work and start the entry protocol. *)
Request(i) ==
    /\ pc[i] = "ncs"
    /\ IF N = 1
         THEN /\ pc'  = [pc  EXCEPT ![i] = "cs"]
              /\ lvl' = lvl
         ELSE /\ pc'  = [pc  EXCEPT ![i] = "setLevel"]
              /\ lvl' = [lvl EXCEPT ![i] = 1]
    /\ UNCHANGED << level, victim >>

(* Announce intent: write level[i]. *)
SetLevel(i) ==
    /\ pc[i] = "setLevel"
    /\ level' = [level EXCEPT ![i] = lvl[i]]
    /\ pc'    = [pc    EXCEPT ![i] = "setVictim"]
    /\ UNCHANGED << lvl, victim >>

(* Defer to others: write victim[lvl[i]] := i. *)
SetVictim(i) ==
    /\ pc[i] = "setVictim"
    /\ victim' = [victim EXCEPT ![lvl[i]] = i]
    /\ pc'     = [pc     EXCEPT ![i] = "wait"]
    /\ UNCHANGED << lvl, level >>

CanAdvance(i) ==
    \/ \A k \in Procs \ {i} : level[k] < lvl[i]
    \/ victim[lvl[i]] # i

(* Busy-wait until the guard holds, then move to the next level or the CS. *)
Wait(i) ==
    /\ pc[i] = "wait"
    /\ CanAdvance(i)
    /\ IF lvl[i] = N - 1
         THEN /\ pc'  = [pc  EXCEPT ![i] = "cs"]
              /\ lvl' = lvl
         ELSE /\ pc'  = [pc  EXCEPT ![i] = "setLevel"]
              /\ lvl' = [lvl EXCEPT ![i] = lvl[i] + 1]
    /\ UNCHANGED << level, victim >>

(* Leave the critical section. *)
LeaveCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED << lvl, level, victim >>

(* Exit protocol: reset the announced level to the neutral state. *)
Exit(i) ==
    /\ pc[i] = "exit"
    /\ level' = [level EXCEPT ![i] = 0]
    /\ lvl'   = [lvl   EXCEPT ![i] = 0]
    /\ pc'    = [pc    EXCEPT ![i] = "ncs"]
    /\ UNCHANGED victim

Proc(i) ==
    \/ Request(i)
    \/ SetLevel(i)
    \/ SetVictim(i)
    \/ Wait(i)
    \/ LeaveCS(i)
    \/ Exit(i)

Next == \E i \in Procs : Proc(i)

(***************************************************************************)
(* Fairness: a process may stay in noncritical work forever, so Request    *)
(* has no fairness. All protocol steps are weakly fair, so processes do    *)
(* not block indefinitely in the CS or the exit code. The guarded Wait     *)
(* step is strongly fair because its guard may be enabled only             *)
(* intermittently.                                                         *)
(***************************************************************************)
Fairness ==
    \A i \in Procs :
        /\ WF_vars(SetLevel(i))
        /\ WF_vars(SetVictim(i))
        /\ SF_vars(Wait(i))
        /\ WF_vars(LeaveCS(i))
        /\ WF_vars(Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Shared-variable well-formedness. *)
NeutralWhenIdle ==
    \A i \in Procs : pc[i] = "ncs" => (level[i] = 0 /\ lvl[i] = 0)

LevelConsistent ==
    \A i \in Procs :
        /\ pc[i] \in {"setVictim", "wait"} => level[i] = lvl[i]
        /\ pc[i] = "setLevel" => level[i] = lvl[i] - 1
        /\ (pc[i] \in {"cs", "exit"} /\ N > 1) => level[i] = N - 1
        /\ pc[i] \in Trying => lvl[i] \in Levels

VictimValid ==
    \A l \in Levels : victim[l] \in Procs \cup {None}

(* Filter property: at most N - l processes have passed past level l. *)
FilterProperty ==
    \A l \in Levels :
        Cardinality({ i \in Procs :
                        \/ pc[i] \in {"cs", "exit"}
                        \/ (pc[i] # "ncs" /\ lvl[i] > l) }) <= N - l

Safety == TypeOK /\ MutualExclusion /\ NeutralWhenIdle
          /\ LevelConsistent /\ VictimValid /\ FilterProperty

-----------------------------------------------------------------------------
(* Liveness *)

(* No starvation: every process that starts the entry protocol eventually enters the CS. *)
StarvationFreedom ==
    \A i \in Procs : (pc[i] \in Trying) ~> (pc[i] = "cs")

(* Deadlock freedom: if some process is trying, some process eventually enters the CS. *)
DeadlockFreedom ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E j \in Procs : pc[j] = "cs")

(* A process in the CS eventually returns to the neutral noncritical state. *)
ExitProgress ==
    \A i \in Procs : (pc[i] = "cs") ~> (pc[i] = "ncs")

Liveness == StarvationFreedom /\ DeadlockFreedom /\ ExitProgress

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================