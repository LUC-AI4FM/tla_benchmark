---------------------------- MODULE TLCSailfish1 ----------------------------
(***************************************************************************)
(* Model-checking configuration wrapper for the Sailfish consensus         *)
(* protocol: 3 nodes, one Byzantine node (n1), rounds 1..5, GST = 3.       *)
(***************************************************************************)

EXTENDS FiniteSets, Integers, Sequences

CONSTANTS n1, n2, n3

N == {n1, n2, n3}

\* The single Byzantine node
F == {n1}

\* Bounded rounds
R == 1..5

MaxRound == 5

\* Quorums: any set of at least two nodes that includes n3, or the full set
Quorum == {Q \in SUBSET N : (Cardinality(Q) >= 2 /\ n3 \in Q) \/ Q = N}

\* Blocking sets: any set containing n3
Blocking == {B \in SUBSET N : n3 \in B}

\* Leader schedule cycles through the three nodes in order
Leader(r) ==
    CASE r % 3 = 1 -> n1
      [] r % 3 = 2 -> n2
      [] r % 3 = 0 -> n3

\* Global stabilization time (round after which the network is synchronous)
GST == 3

VARIABLES vs, es, round, log

vars == <<vs, es, round, log>>

INSTANCE Sailfish

\* Correct nodes
Correct == N \ F

(***************************************************************************)
(* Terminating specification: allow stuttering once all correct nodes have *)
(* reached the maximum round, so that TLC terminates cleanly.              *)
(***************************************************************************)
Terminating ==
    /\ \A n \in Correct : round[n] = MaxRound
    /\ UNCHANGED vars

TerminatingSpec ==
    Init /\ [][Next \/ Terminating]_vars

(***************************************************************************)
(* State constraint: correct nodes' rounds stay within the bounded range.  *)
(***************************************************************************)
StateConstraint ==
    \A n \in Correct : round[n] \in R

(***************************************************************************)
(* Invariants checked (imported from Sailfish): TypeOK, Agreement,         *)
(* Liveness.                                                               *)
(***************************************************************************)
CheckedInvariants ==
    /\ TypeOK
    /\ Agreement
    /\ Liveness

(***************************************************************************)
(* Falsy properties: intended to be violated, used as false invariants to  *)
(* extract interesting counterexample traces.                              *)
(***************************************************************************)

\* Violated when all correct nodes reach the final round
Falsy1 ==
    ~(\A n \in Correct : round[n] = MaxRound)

\* Violated when some correct node has a log longer than one entry
Falsy2 ==
    ~(\E n \in Correct : Len(log[n]) > 1)

\* Violated when the round-2 leader vertex is committed by a correct node
Falsy3 ==
    ~(\E n \in Correct :
        \E i \in 1..Len(log[n]) : log[n][i] = <<Leader(2), 2>>)

=============================================================================