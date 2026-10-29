---------------------------- MODULE MCSession9peterson ----------------------------
(***************************************************************************)
(* Model-checking wrapper for a Peterson-style (filter lock) mutual       *)
(* exclusion algorithm for N processes. The underlying algorithm is       *)
(* normally imported from Session9peterson. It is defined inline here so  *)
(* that the module is self-contained and parses on its own.               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N >= 2

(* Concrete values used when model checking *)
MC_N == 3

(* The process identifier range *)
P == 1..N

(* Filter levels *)
Levels == 1..(N-1)

VARIABLES pc, level, victim, cur

vars == <<pc, level, victim, cur>>

Locs == {"ncs", "enter", "setlevel", "setvictim", "wait", "cs", "exit"}

TypeOK ==
    /\ pc \in [P -> Locs]
    /\ level \in [P -> 0..(N-1)]
    /\ victim \in [Levels -> P]
    /\ cur \in [P -> 1..(N-1)]

Init ==
    /\ pc = [p \in P |-> "ncs"]
    /\ level = [p \in P |-> 0]
    /\ victim = [l \in Levels |-> CHOOSE q \in P : TRUE]
    /\ cur = [p \in P |-> 1]

(* Non-critical section: a process may decide to try to enter *)
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "enter"]
    /\ UNCHANGED <<level, victim, cur>>

(* Entry point of the trying protocol *)
Enter(p) ==
    /\ pc[p] = "enter"
    /\ cur' = [cur EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ UNCHANGED <<level, victim>>

(* level[p] := cur[p] *)
SetLevel(p) ==
    /\ pc[p] = "setlevel"
    /\ level' = [level EXCEPT ![p] = cur[p]]
    /\ pc' = [pc EXCEPT ![p] = "setvictim"]
    /\ UNCHANGED <<victim, cur>>

(* victim[cur[p]] := p *)
SetVictim(p) ==
    /\ pc[p] = "setvictim"
    /\ victim' = [victim EXCEPT ![cur[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED <<level, cur>>

(* await ~(\E k # p : level[k] >= cur[p]) \/ victim[cur[p]] # p *)
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ victim[cur[p]] # p
       \/ \A k \in P \ {p} : level[k] < cur[p]
    /\ IF cur[p] = N - 1
          THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED cur
          ELSE /\ cur' = [cur EXCEPT ![p] = cur[p] + 1]
               /\ pc' = [pc EXCEPT ![p] = "setlevel"]
    /\ UNCHANGED <<level, victim>>

(* Critical section *)
CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<level, victim, cur>>

(* Exit protocol: level[p] := 0 *)
Exit(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED <<victim, cur>>

(* All steps except the non-critical step, which need not be fair *)
Proc(p) ==
    \/ Enter(p)
    \/ SetLevel(p)
    \/ SetVictim(p)
    \/ Wait(p)
    \/ CS(p)
    \/ Exit(p)

Next == \E p \in P : NCS(p) \/ Proc(p)

Fairness == \A p \in P : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

(* Mutual exclusion: no two distinct processes are in the critical section *)
MutualExclusion ==
    \A p, q \in P : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Starvation freedom: any process at "enter" eventually reaches "cs" *)
StarvationFreedom ==
    \A p \in P : (pc[p] = "enter") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
=============================================================================