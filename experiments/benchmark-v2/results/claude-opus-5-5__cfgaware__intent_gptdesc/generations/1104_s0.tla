------------------------------ MODULE CrashConsensus ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs  == 1..N
Values == {"Yes", "No"}
None   == "None"

\* Maximum number of crash failures tolerated (always F < N)
F == (N - 1) \div 2

ASSUME FAssumption == F < N

\* Number of communication rounds needed in a synchronous crash-tolerant protocol
MaxRound == F + 1

VARIABLES
    round,        \* current round number (MaxRound + 1 = decision phase)
    input,        \* initial binary vote of each process
    est,          \* current estimate (vote) of each process
    alive,        \* set of processes that have not crashed
    decision,     \* decided value or None
    sentYes,      \* number of Yes messages sent by each process
    sentNo,       \* number of No messages sent by each process
    rcvdYes,      \* number of Yes messages received by each process
    rcvdNo,       \* number of No messages received by each process
    failDetected  \* processes each process has detected as failed (missing messages)

vars == << round, input, est, alive, decision,
           sentYes, sentNo, rcvdYes, rcvdNo, failDetected >>

TypeOK ==
    /\ round \in 1..(MaxRound + 1)
    /\ input \in [Procs -> Values]
    /\ est \in [Procs -> Values]
    /\ alive \subseteq Procs
    /\ decision \in [Procs -> Values \cup {None}]
    /\ sentYes \in [Procs -> Nat]
    /\ sentNo \in [Procs -> Nat]
    /\ rcvdYes \in [Procs -> Nat]
    /\ rcvdNo \in [Procs -> Nat]
    /\ failDetected \in [Procs -> SUBSET Procs]

Crashed == Procs \ alive

Init ==
    /\ round = 1
    /\ input \in [Procs -> Values]
    /\ est = input
    /\ alive = Procs
    /\ decision = [p \in Procs |-> None]
    /\ sentYes = [p \in Procs |-> 0]
    /\ sentNo = [p \in Procs |-> 0]
    /\ rcvdYes = [p \in Procs |-> 0]
    /\ rcvdNo = [p \in Procs |-> 0]
    /\ failDetected = [p \in Procs |-> {}]

(***************************************************************************)
(* One synchronous round. A set C of currently alive processes crashes     *)
(* during the round; each crashing process delivers its vote only to an    *)
(* arbitrary subset reach[p] of the processes. Non-crashing processes      *)
(* deliver their vote reliably to every other process. The total number   *)
(* of crashes never exceeds F.                                             *)
(***************************************************************************)
RoundStep ==
    /\ round <= MaxRound
    /\ \E C \in SUBSET alive :
         /\ Cardinality(Crashed \cup C) <= F
         /\ \E reach \in [C -> SUBSET Procs] :
              LET Recip(p)   == IF p \in C THEN reach[p] \ {p} ELSE Procs \ {p}
                  Senders(q) == {p \in alive \ {q} : q \in Recip(p)}
                  newAlive   == alive \ C
                  YesFrom(q) == {p \in Senders(q) : est[p] = "Yes"}
                  NoFrom(q)  == {p \in Senders(q) : est[p] = "No"}
              IN
              /\ alive' = newAlive
              /\ sentYes' = [p \in Procs |->
                               IF p \in alive /\ est[p] = "Yes"
                                 THEN sentYes[p] + Cardinality(Recip(p))
                                 ELSE sentYes[p]]
              /\ sentNo' = [p \in Procs |->
                               IF p \in alive /\ est[p] = "No"
                                 THEN sentNo[p] + Cardinality(Recip(p))
                                 ELSE sentNo[p]]
              /\ rcvdYes' = [q \in Procs |->
                               IF q \in newAlive
                                 THEN rcvdYes[q] + Cardinality(YesFrom(q))
                                 ELSE rcvdYes[q]]
              /\ rcvdNo' = [q \in Procs |->
                               IF q \in newAlive
                                 THEN rcvdNo[q] + Cardinality(NoFrom(q))
                                 ELSE rcvdNo[q]]
              /\ failDetected' = [q \in Procs |->
                               IF q \in newAlive
                                 THEN failDetected[q] \cup
                                        ((Procs \ {q}) \ Senders(q))
                                 ELSE failDetected[q]]
              /\ est' = [q \in Procs |->
                               IF q \in newAlive /\ NoFrom(q) # {}
                                 THEN "No"
                                 ELSE est[q]]
    /\ round' = round + 1
    /\ UNCHANGED << input, decision >>

(***************************************************************************)
(* After MaxRound = F+1 rounds, each non-faulty process decides its        *)
(* current estimate.                                                        *)
(***************************************************************************)
Decide(p) ==
    /\ round = MaxRound + 1
    /\ p \in alive
    /\ decision[p] = None
    /\ decision' = [decision EXCEPT ![p] = est[p]]
    /\ UNCHANGED << round, input, est, alive, sentYes, sentNo,
                    rcvdYes, rcvdNo, failDetected >>

Terminated ==
    /\ round = MaxRound + 1
    /\ \A p \in alive : decision[p] # None
    /\ UNCHANGED vars

Next ==
    \/ RoundStep
    \/ \E p \in Procs : Decide(p)
    \/ Terminated

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(RoundStep)
    /\ \A p \in Procs : WF_vars(Decide(p))

-----------------------------------------------------------------------------
(* Safety properties *)

Agreement ==
    \A p, q \in alive :
        (decision[p] # None /\ decision[q] # None) => decision[p] = decision[q]

\* Once any non-faulty process has chosen a value, no other non-faulty
\* process decides the opposite value.
NoOppositeDecision ==
    \A p \in alive : \A v \in Values :
        decision[p] = v =>
            \A q \in alive : decision[q] \in {v, None}

Validity ==
    \A v \in Values :
        (\A p \in Procs : input[p] = v) =>
            \A q \in Procs : decision[q] \in {v, None}

CrashBound == Cardinality(Crashed) <= F

CounterConsistency ==
    \A p \in Procs : failDetected[p] \subseteq Procs \ {p}

Inv ==
    /\ TypeOK
    /\ Agreement
    /\ NoOppositeDecision
    /\ Validity
    /\ CrashBound
    /\ CounterConsistency

-----------------------------------------------------------------------------
(* Liveness properties *)

Termination ==
    <>[](\A p \in alive : decision[p] # None)

\* If enough processes are non-faulty, all non-faulty processes decide.
Progress ==
    (N > 2 * F) => <>(\A p \in alive : decision[p] # None)

=============================================================================