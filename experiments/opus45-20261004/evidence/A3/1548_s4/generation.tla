--------------------------- MODULE OneStepByzantine ---------------------------
(* 
 * TLA+ specification of the folklore one-step consensus algorithm with 
 * Byzantine faults, as described by Dobre and Suri (DSN 2006).
 * 
 * The algorithm allows processes to reach consensus in a single communication
 * step, tolerating up to F Byzantine faults among N processes.
 *)

EXTENDS Integers, FiniteSets

CONSTANTS 
    N,          \* Total number of processes
    F,          \* Maximum number of Byzantine faults tolerated
    T           \* Threshold parameter for decision

VARIABLES
    pc,         \* Program counter for each process: "init", "proposed", "decided", "faulty"
    proposal,   \* Initial proposal value for each process (0 or 1)
    decision,   \* Decision value for each process (0, 1, or -1 for undecided)
    sent0,      \* Number of 0-messages sent by correct processes
    sent1,      \* Number of 1-messages sent by correct processes
    rcvd0,      \* For each process, number of 0-messages received
    rcvd1,      \* For each process, number of 1-messages received
    faulty      \* Set of faulty processes

Procs == 1..N
Values == {0, 1}

vars == <<pc, proposal, decision, sent0, sent1, rcvd0, rcvd1, faulty>>

-----------------------------------------------------------------------------
(* Type invariant *)
TypeOK ==
    /\ pc \in [Procs -> {"init", "proposed", "decided", "faulty"}]
    /\ proposal \in [Procs -> Values]
    /\ decision \in [Procs -> {-1, 0, 1}]
    /\ sent0 \in 0..N
    /\ sent1 \in 0..N
    /\ rcvd0 \in [Procs -> 0..N]
    /\ rcvd1 \in [Procs -> 0..N]
    /\ faulty \subseteq Procs
    /\ Cardinality(faulty) <= F

-----------------------------------------------------------------------------
(* Initial state predicates *)

\* Generic initial state
Init ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal \in [Procs -> Values]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

\* All processes propose 0
InitAll0 ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal = [p \in Procs |-> 0]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

\* All processes propose 1
InitAll1 ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal = [p \in Procs |-> 1]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

-----------------------------------------------------------------------------
(* Actions *)

\* A correct process proposes its value (broadcasts message)
Propose(p) ==
    /\ pc[p] = "init"
    /\ p \notin faulty
    /\ pc' = [pc EXCEPT ![p] = "proposed"]
    /\ IF proposal[p] = 0
       THEN /\ sent0' = sent0 + 1
            /\ sent1' = sent1
       ELSE /\ sent1' = sent1 + 1
            /\ sent0' = sent0
    /\ UNCHANGED <<proposal, decision, rcvd0, rcvd1, faulty>>

\* A correct process receives messages from other processes
\* Models non-deterministic message reception including potentially fake messages from Byzantine processes
Receive(p) ==
    /\ pc[p] = "proposed"
    /\ p \notin faulty
    \* Can receive any number of 0s and 1s, bounded by what's been sent plus Byzantine messages
    /\ \E r0 \in rcvd0[p]..N, r1 \in rcvd1[p]..N :
        \* At least receive what correct processes sent, Byzantine can add fake messages
        /\ r0 >= sent0 - Cardinality({q \in faulty : proposal[q] = 0 /\ pc[q] # "init"})
        /\ r1 >= sent1 - Cardinality({q \in faulty : proposal[q] = 1 /\ pc[q] # "init"})
        \* Total received bounded by N
        /\ r0 + r1 <= N
        /\ rcvd0' = [rcvd0 EXCEPT ![p] = r0]
        /\ rcvd1' = [rcvd1 EXCEPT ![p] = r1]
    /\ UNCHANGED <<pc, proposal, decision, sent0, sent1, faulty>>

\* A correct process decides based on received messages
Decide(p) ==
    /\ pc[p] = "proposed"
    /\ p \notin faulty
    \* Must have received enough messages to decide
    /\ rcvd0[p] + rcvd1[p] >= N - F
    /\ pc' = [pc EXCEPT ![p] = "decided"]
    /\ \/ /\ rcvd0[p] >= T
          /\ rcvd1[p] < N - T - F
          /\ decision' = [decision EXCEPT ![p] = 0]
       \/ /\ rcvd1[p] >= T
          /\ rcvd0[p] < N - T - F
          /\ decision' = [decision EXCEPT ![p] = 1]
       \/ /\ ~(rcvd0[p] >= T /\ rcvd1[p] < N - T - F)
          /\ ~(rcvd1[p] >= T /\ rcvd0[p] < N - T - F)
          /\ decision' = [decision EXCEPT ![p] = proposal[p]]  \* Default to own proposal
    /\ UNCHANGED <<proposal, sent0, sent1, rcvd0, rcvd1, faulty>>

\* A process becomes faulty (Byzantine)
BecomeFaulty(p) ==
    /\ Cardinality(faulty) < F
    /\ p \notin faulty
    /\ pc[p] # "faulty"
    /\ faulty' = faulty \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "faulty"]
    /\ UNCHANGED <<proposal, decision, sent0, sent1, rcvd0, rcvd1>>

\* A faulty process can send arbitrary messages
FaultySend(p) ==
    /\ p \in faulty
    /\ \/ /\ sent0' = sent0 + 1
          /\ sent1' = sent1
       \/ /\ sent1' = sent1 + 1
          /\ sent0' = sent0
    /\ UNCHANGED <<pc, proposal, decision, rcvd0, rcvd1, faulty>>

-----------------------------------------------------------------------------
(* Next state relation *)

Step ==
    \E p \in Procs :
        \/ Propose(p)
        \/ Receive(p)
        \/ Decide(p)
        \/ BecomeFaulty(p)
        \/ FaultySend(p)

Next == Step \/ UNCHANGED vars

-----------------------------------------------------------------------------
(* Fairness and specification *)

Fairness == WF_vars(Step)

Spec == Init /\ [][Next]_vars /\ Fairness

SpecAll0 == InitAll0 /\ [][Next]_vars /\ Fairness

SpecAll1 == InitAll1 /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

\* Set of correct processes that have decided
CorrectDecided == {p \in Procs : p \notin faulty /\ pc[p] = "decided"}

\* Agreement: No two correct processes decide differently
Agreement ==
    \A p, q \in CorrectDecided :
        decision[p] = decision[q]

\* Validity: If all correct processes propose v, then any correct process that decides, decides v
Validity0 ==
    (\A p \in Procs : p \notin faulty => proposal[p] = 0) =>
    (\A p \in CorrectDecided : decision[p] = 0)

Validity1 ==
    (\A p \in Procs : p \notin faulty => proposal[p] = 1) =>
    (\A p \in CorrectDecided : decision[p] = 1)

Validity == Validity0 /\ Validity1

\* Combined safety invariant
Safety == Agreement /\ Validity

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Termination: Every correct process eventually decides
Termination ==
    \A p \in Procs : 
        (p \notin faulty) ~> (pc[p] = "decided" \/ p \in faulty)

\* All correct processes eventually decide
AllCorrectDecide ==
    <>(\A p \in Procs : p \in faulty \/ pc[p] = "decided")

-----------------------------------------------------------------------------
(* Auxiliary invariants for model checking *)

\* Number of faulty processes never exceeds F
FaultyBound == Cardinality(faulty) <= F

\* Decision values are valid
ValidDecisions ==
    \A p \in Procs : decision[p] \in {-1, 0, 1}

\* Invariant combining all safety properties
Invariant == TypeOK /\ FaultyBound /\ Agreement

=============================================================================