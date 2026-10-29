---------------------------- MODULE DijkstraMutex ----------------------------
(***************************************************************************)
(* Dijkstra's mutual exclusion algorithm (CACM 1965).                     *)
(*                                                                         *)
(* b[i] = FALSE : process i has signalled that it wants to enter.         *)
(* c[i] = FALSE : process i is in the final stage of the entry protocol.  *)
(* k            : the shared "turn" indicator.                            *)
(*                                                                         *)
(* The algorithm is written in a PlusCal-like style, with one action per  *)
(* label. Process i checks the other processes in a nondeterministic      *)
(* order at label Li4b.                                                    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Proc

ASSUME Proc # {}

VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

Labels == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li3c", "Li3d",
           "Li4a", "Li4b", "cs", "Li5", "Li6", "ncs"}

TypeOK ==
    /\ b \in [Proc -> BOOLEAN]
    /\ c \in [Proc -> BOOLEAN]
    /\ k \in Proc
    /\ pc \in [Proc -> Labels]
    /\ \A i \in Proc : temp[i] \in Proc \/ temp[i] \in SUBSET Proc

Init ==
    /\ b = [i \in Proc |-> TRUE]
    /\ c = [i \in Proc |-> TRUE]
    /\ k \in Proc
    /\ temp = [i \in Proc |-> {}]
    /\ pc = [i \in Proc |-> "Li0"]

(* Signal intent to enter. *)
Li0(self) ==
    /\ pc[self] = "Li0"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << c, k, temp >>

(* Check whether we hold the turn. *)
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
    /\ temp' = [temp EXCEPT ![self] = k]
    /\ pc' = [pc EXCEPT ![self] = "Li3b"]
    /\ UNCHANGED << b, c, k >>

(* If the turn holder is not interested, try to claim the turn. *)
Li3b(self) ==
    /\ pc[self] = "Li3b"
    /\ IF b[temp[self]]
         THEN pc' = [pc EXCEPT ![self] = "Li3c"]
         ELSE pc' = [pc EXCEPT ![self] = "Li3d"]
    /\ UNCHANGED << b, c, k, temp >>

Li3c(self) ==
    /\ pc[self] = "Li3c"
    /\ k' = self
    /\ pc' = [pc EXCEPT ![self] = "Li3d"]
    /\ UNCHANGED << b, c, temp >>

Li3d(self) ==
    /\ pc[self] = "Li3d"
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << b, c, k, temp >>

(* Announce final stage and prepare to check all other processes. *)
Li4a(self) ==
    /\ pc[self] = "Li4a"
    /\ c' = [c EXCEPT ![self] = FALSE]
    /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "Li4b"]
    /\ UNCHANGED << b, k >>

(* Check the other processes in nondeterministic order; restart if some  *)
(* other process is also in its final stage.                              *)
Li4b(self) ==
    /\ pc[self] = "Li4b"
    /\ IF temp[self] # {}
         THEN \E j \in temp[self] :
                /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
                /\ IF ~ c[j]
                     THEN pc' = [pc EXCEPT ![self] = "Li1"]
                     ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED temp
    /\ UNCHANGED << b, c, k >>

(* Critical section. *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "Li5"]
    /\ UNCHANGED << b, c, k, temp >>

(* Exit protocol. *)
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

(* Non-critical section: the process may stay here forever (no fairness). *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "Li0"]
    /\ UNCHANGED << b, c, k, temp >>

P(self) ==
    \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
    \/ Li3c(self) \/ Li3d(self) \/ Li4a(self) \/ Li4b(self) \/ cs(self)
    \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == \E self \in Proc : P(self)

(* Weak fairness on every process step except leaving the non-critical  *)
(* section.                                                               *)
Fairness ==
    \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

InCS(i) == pc[i] = "cs"

Trying(i) == pc[i] \notin {"Li5", "Li6", "ncs"}

MutualExclusion ==
    \A i, j \in Proc : (i # j) => ~ (InCS(i) /\ InCS(j))

DeadlockFree ==
    (\E i \in Proc : Trying(i)) ~> (\E j \in Proc : InCS(j))

(* Expected to FAIL: TLC produces a starvation counterexample. *)
StarvationFree ==
    \A i \in Proc : Trying(i) ~> InCS(i)

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree
=============================================================================