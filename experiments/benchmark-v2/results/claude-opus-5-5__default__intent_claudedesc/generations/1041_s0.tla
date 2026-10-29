------------------------------ MODULE DijkstraMutex ------------------------------
(***************************************************************************)
(* Dijkstra's 1965 mutual exclusion algorithm for N processes, from       *)
(* "Solution of a Problem in Concurrent Programming Control".             *)
(*                                                                         *)
(* Shared variables:                                                       *)
(*   b[i] : FALSE iff process i wants to enter (or is in) the CS.         *)
(*   c[i] : FALSE iff process i is at the final stage of its entry        *)
(*          protocol (has tentatively claimed the CS).                     *)
(*   k    : the process that currently "has the turn".                    *)
(*                                                                         *)
(* Each process i executes:                                                *)
(*   Li0: b[i] := false;                                                   *)
(*   Li1: if k # i then                                                    *)
(*   Li2:    begin c[i] := true;                                           *)
(*   Li3:       if b[k] then k := i;                                       *)
(*              goto Li1                                                   *)
(*           end                                                           *)
(*        else                                                             *)
(*   Li4:    begin c[i] := false;                                          *)
(*              for j := 1 step 1 until N do                               *)
(*                 if j # i and not c[j] then goto Li1                     *)
(*           end;                                                          *)
(*        critical section;                                                *)
(*        c[i] := true; b[i] := true;                                      *)
(*        remainder of the cycle (noncritical section); goto Li0           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Proc            \* The set of processes, e.g. {p1, p2, p3}

ASSUME Proc # {}

VARIABLES
    b,      \* b[i] \in BOOLEAN
    c,      \* c[i] \in BOOLEAN
    k,      \* k \in Proc
    pc,     \* control location of each process
    temp    \* temp[i]: processes still to be checked in the Li4 loop

vars == << b, c, k, pc, temp >>

Labels == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b",
           "cs", "Li5", "Li6", "ncs"}

TypeOK ==
    /\ b \in [Proc -> BOOLEAN]
    /\ c \in [Proc -> BOOLEAN]
    /\ k \in Proc
    /\ pc \in [Proc -> Labels]
    /\ temp \in [Proc -> SUBSET Proc]

Init ==
    /\ b = [i \in Proc |-> TRUE]
    /\ c = [i \in Proc |-> TRUE]
    /\ k \in Proc
    /\ pc = [i \in Proc |-> "Li0"]
    /\ temp = [i \in Proc |-> {}]

-----------------------------------------------------------------------------
(* Actions of process self *)

Li0(self) ==
    /\ pc[self] = "Li0"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << c, k, temp >>

Li1(self) ==
    /\ pc[self] = "Li1"
    /\ IF k # self
         THEN pc' = [pc EXCEPT ![self] = "Li2"]
         ELSE pc' = [pc EXCEPT ![self] = "Li4a"]
    /\ UNCHANGED << b, c, k, temp >>

Li2(self) ==
    /\ pc[self] = "Li2"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li3a"]
    /\ UNCHANGED << b, k, temp >>

Li3a(self) ==
    /\ pc[self] = "Li3a"
    /\ IF b[k]
         THEN pc' = [pc EXCEPT ![self] = "Li3b"]
         ELSE pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << b, c, k, temp >>

Li3b(self) ==
    /\ pc[self] = "Li3b"
    /\ k' = self
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << b, c, temp >>

Li4a(self) ==
    /\ pc[self] = "Li4a"
    /\ c' = [c EXCEPT ![self] = FALSE]
    /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "Li4b"]
    /\ UNCHANGED << b, k >>

Li4b(self) ==
    /\ pc[self] = "Li4b"
    /\ IF temp[self] # {}
         THEN \E j \in temp[self] :
                /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
                /\ IF ~c[j]
                     THEN pc' = [pc EXCEPT ![self] = "Li1"]
                     ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED temp
    /\ UNCHANGED << b, c, k >>

CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "Li5"]
    /\ UNCHANGED << b, c, k, temp >>

Li5(self) ==
    /\ pc[self] = "Li5"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li6"]
    /\ UNCHANGED << b, k, temp >>

Li6(self) ==
    /\ pc[self] = "Li6"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << c, k, temp >>

(* Noncritical section: a process may remain here forever (no fairness). *)
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "Li0"]
    /\ UNCHANGED << b, c, k, temp >>

(* All steps of a process except leaving the noncritical section. *)
FairStep(self) ==
    \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
    \/ Li4a(self) \/ Li4b(self) \/ CS(self) \/ Li5(self) \/ Li6(self)

P(self) == FairStep(self) \/ NCS(self)

Next == \E self \in Proc : P(self)

Fairness == \A self \in Proc : WF_vars(FairStep(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

(* Safety: at most one process is in its critical section. *)
MutualExclusion ==
    \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Processes trying to enter the critical section. *)
Trying(i) == pc[i] \in {"Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b"}

(* Liveness: if some process is trying to enter, some process eventually *)
(* enters the critical section.                                          *)
DeadlockFreedom ==
    (\E i \in Proc : Trying(i)) ~> (\E i \in Proc : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom
=============================================================================