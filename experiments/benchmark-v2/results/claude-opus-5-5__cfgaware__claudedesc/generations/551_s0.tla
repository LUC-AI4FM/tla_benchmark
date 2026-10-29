------------------------------ MODULE MCSession9onebit ------------------------------
(***************************************************************************)
(* Model-checking configuration for the one-bit mutual exclusion          *)
(* algorithm (Burns-Lamport style).  The algorithm normally lives in the  *)
(* base module Session9onebit.  It is reproduced here so that this module *)
(* is self-contained and parses on its own.                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS N, Procs

VARIABLES x, unchecked, other, pc

vars == << x, unchecked, other, pc >>

(***************************************************************************)
(* Constant overrides for the model-checking configuration                *)
(***************************************************************************)
ConstN == 3
ConstProcs == {0, 1, 2}

-----------------------------------------------------------------------------
(***************************************************************************)
(* The one-bit algorithm                                                   *)
(***************************************************************************)

TypeOK ==
    /\ x \in [Procs -> BOOLEAN]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ other \in [Procs -> Procs]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "e5", "e6", "cs", "f"}]

Init ==
    /\ x = [i \in Procs |-> FALSE]
    /\ unchecked = [i \in Procs |-> {}]
    /\ other \in [Procs -> Procs]
    /\ pc = [i \in Procs |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, unchecked, other >>

e1(self) ==
    /\ pc[self] = "e1"
    /\ x' = [x EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = {j \in Procs : j < self}]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED other

\* Check all lower-numbered processes; back off if one is interested.
e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ other' = [other EXCEPT ![self] = i]
                /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                /\ pc' = [pc EXCEPT ![self] = "e3"]
         ELSE /\ unchecked' = [unchecked EXCEPT ![self] = {j \in Procs : j > self}]
              /\ pc' = [pc EXCEPT ![self] = "e5"]
              /\ UNCHANGED other
    /\ UNCHANGED x

e3(self) ==
    /\ pc[self] = "e3"
    /\ IF x[other[self]]
         THEN /\ x' = [x EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "e4"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "e2"]
              /\ UNCHANGED x
    /\ UNCHANGED << unchecked, other >>

e4(self) ==
    /\ pc[self] = "e4"
    /\ ~x[other[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, unchecked, other >>

\* Wait for all higher-numbered processes to be uninterested.
e5(self) ==
    /\ pc[self] = "e5"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ other' = [other EXCEPT ![self] = i]
                /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                /\ pc' = [pc EXCEPT ![self] = "e6"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED << unchecked, other >>
    /\ UNCHANGED x

e6(self) ==
    /\ pc[self] = "e6"
    /\ ~x[other[self]]
    /\ pc' = [pc EXCEPT ![self] = "e5"]
    /\ UNCHANGED << x, unchecked, other >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "f"]
    /\ UNCHANGED << x, unchecked, other >>

f(self) ==
    /\ pc[self] = "f"
    /\ x' = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << unchecked, other >>

\* All steps except leaving the noncritical section are subject to fairness.
FairStep(self) ==
    e1(self) \/ e2(self) \/ e3(self) \/ e4(self) \/ e5(self)
      \/ e6(self) \/ cs(self) \/ f(self)

P(self) == ncs(self) \/ FairStep(self)

Next == \E self \in Procs : P(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : WF_vars(FairStep(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "e5", "e6"}

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

DeadAndLivelockFree ==
    (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : pc[i] = "cs")

NoStarveProc0 == Trying(0) ~> (pc[0] = "cs")

\* Not satisfied by the one-bit algorithm (process 1 may starve).
NoStarveProc1 == Trying(1) ~> (pc[1] = "cs")

=============================================================================