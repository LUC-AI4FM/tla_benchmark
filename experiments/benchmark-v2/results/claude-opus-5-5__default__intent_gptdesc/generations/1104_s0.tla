------------------------- MODULE SyncCrashConsensus -------------------------
(***************************************************************************)
(* Synchronous round-based binary agreement (Yes/No) for N processes      *)
(* tolerating up to F crash failures (F < N).                             *)
(*                                                                         *)
(* Abstraction:                                                            *)
(*  - Each round is one atomic step. Every live process broadcasts its     *)
(*    current vote to all other processes. Messages are delivered          *)
(*    reliably within the round.                                           *)
(*  - In any round, some live processes may crash. A process that crashes  *)
(*    in a round delivers its vote only to an arbitrary subset of          *)
(*    receivers (send omission). After that it never takes part again.    *)
(*  - The total number of crashed processes never exceeds F.               *)
(*  - Each process keeps counters of Yes/No votes sent and received, a     *)
(*    counter of missing messages (detected failures), and the set of      *)
(*    processes it suspects.                                               *)
(*  - A process's vote is "No" once it has seen any "No" (min-flooding).   *)
(*    After F+1 rounds every live process decides its current vote. Some   *)
(*    round among F+1 rounds has no crash, so all live processes get the   *)
(*    same vote there. That gives agreement.                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,     \* the set of N processes
          F         \* maximum number of crash failures

ASSUME ProcAssump  == IsFiniteSet(Proc) /\ Proc # {}
ASSUME FaultAssump == F \in Nat /\ F < Cardinality(Proc)

N       == Cardinality(Proc)
Values  == {"Yes", "No"}
None    == "None"
MaxRound == F + 1          \* number of rounds executed before deciding

VARIABLES
  round,        \* current round number (1 .. MaxRound+1)
  alive,        \* set of processes that have not crashed
  input,        \* initial binary input of each process
  seenNo,       \* TRUE iff process has seen (or holds) a No vote
  decision,     \* decision of each process, or None
  sentYes,      \* number of Yes messages sent by each process
  sentNo,       \* number of No messages sent by each process
  rcvdYes,      \* number of Yes messages received by each process
  rcvdNo,       \* number of No messages received by each process
  failCount,    \* number of expected messages missing (detected failures)
  suspected     \* set of processes each process has detected as failed

vars == << round, alive, input, seenNo, decision,
           sentYes, sentNo, rcvdYes, rcvdNo, failCount, suspected >>

Faulty == Proc \ alive

Vote(p) == IF seenNo[p] THEN "No" ELSE "Yes"

-----------------------------------------------------------------------------
TypeOK ==
  /\ round \in 1..(MaxRound + 1)
  /\ alive \subseteq Proc
  /\ input \in [Proc -> Values]
  /\ seenNo \in [Proc -> BOOLEAN]
  /\ decision \in [Proc -> Values \cup {None}]
  /\ sentYes \in [Proc -> Nat]
  /\ sentNo \in [Proc -> Nat]
  /\ rcvdYes \in [Proc -> Nat]
  /\ rcvdNo \in [Proc -> Nat]
  /\ failCount \in [Proc -> Nat]
  /\ suspected \in [Proc -> SUBSET Proc]

Init ==
  /\ round = 1
  /\ alive = Proc
  /\ input \in [Proc -> Values]
  /\ seenNo = [p \in Proc |-> input[p] = "No"]
  /\ decision = [p \in Proc |-> None]
  /\ sentYes = [p \in Proc |-> 0]
  /\ sentNo = [p \in Proc |-> 0]
  /\ rcvdYes = [p \in Proc |-> 0]
  /\ rcvdNo = [p \in Proc |-> 0]
  /\ failCount = [p \in Proc |-> 0]
  /\ suspected = [p \in Proc |-> {}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* One synchronous round.                                                  *)
(*   C : set of live processes that crash during this round                *)
(*   D : for each crashing process, the receivers that still get its vote  *)
(***************************************************************************)
RoundStep(C, D) ==
  LET survivors == alive \ C
      \* recipients actually reached by sender p in this round
      Recips(p) == IF p \in C THEN D[p] \ {p} ELSE Proc \ {p}
      \* senders whose messages reach q in this round
      Senders(q) == {p \in alive \ {q} : q \in Recips(p)}
      YesFrom(q) == {p \in Senders(q) : Vote(p) = "Yes"}
      NoFrom(q)  == {p \in Senders(q) : Vote(p) = "No"}
      Missing(q) == (Proc \ {q}) \ Senders(q)
      newSeenNo(q) == seenNo[q] \/ NoFrom(q) # {}
      lastRound == (round = MaxRound)
  IN
  /\ round <= MaxRound
  /\ Cardinality(Faulty \cup C) <= F
  /\ alive' = survivors
  /\ round' = round + 1
  /\ sentYes' = [p \in Proc |->
                   IF p \in alive /\ Vote(p) = "Yes"
                     THEN sentYes[p] + Cardinality(Recips(p))
                     ELSE sentYes[p]]
  /\ sentNo' = [p \in Proc |->
                   IF p \in alive /\ Vote(p) = "No"
                     THEN sentNo[p] + Cardinality(Recips(p))
                     ELSE sentNo[p]]
  /\ rcvdYes' = [q \in Proc |->
                   IF q \in survivors
                     THEN rcvdYes[q] + Cardinality(YesFrom(q))
                     ELSE rcvdYes[q]]
  /\ rcvdNo' = [q \in Proc |->
                   IF q \in survivors
                     THEN rcvdNo[q] + Cardinality(NoFrom(q))
                     ELSE rcvdNo[q]]
  /\ failCount' = [q \in Proc |->
                   IF q \in survivors
                     THEN failCount[q] + Cardinality(Missing(q))
                     ELSE failCount[q]]
  /\ suspected' = [q \in Proc |->
                   IF q \in survivors
                     THEN suspected[q] \cup Missing(q)
                     ELSE suspected[q]]
  /\ seenNo' = [q \in Proc |->
                   IF q \in survivors THEN newSeenNo(q) ELSE seenNo[q]]
  /\ decision' = [q \in Proc |->
                   IF lastRound /\ q \in survivors
                     THEN IF newSeenNo(q) THEN "No" ELSE "Yes"
                     ELSE decision[q]]
  /\ UNCHANGED input

Round ==
  \E C \in SUBSET alive :
    \E D \in [C -> SUBSET Proc] :
      RoundStep(C, D)

\* Protocol finished; allow stuttering so behaviors are not deadlocked.
Terminated ==
  /\ round > MaxRound
  /\ UNCHANGED vars

Next == Round \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Round)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

CrashBound == Cardinality(Faulty) <= F

\* No two non-faulty processes decide differently.
Agreement ==
  \A p, q \in alive :
    (decision[p] # None /\ decision[q] # None) => decision[p] = decision[q]

\* Once a non-faulty process has decided v, no non-faulty process holds the
\* opposite decision.
NoOppositeDecision ==
  \A v \in Values :
    (\E p \in alive : decision[p] = v) =>
      \A q \in alive : decision[q] \in {v, None}

\* If all processes start with the same input, any decision equals it.
\* Under crash failures this is the validity condition the protocol can
\* guarantee.
Validity ==
  \A v \in Values :
    (\A p \in Proc : input[p] = v) =>
      \A q \in Proc : decision[q] \in {v, None}

\* Every decided value is the input of some process.
WeakValidity ==
  \A q \in Proc :
    decision[q] # None => \E p \in Proc : input[p] = decision[q]

\* Counter consistency: missing messages are only attributed to faulty
\* processes, and a non-faulty process is never suspected.
FailureDetectionSound ==
  \A q \in alive : suspected[q] \subseteq Faulty

Invariants ==
  /\ TypeOK
  /\ CrashBound
  /\ Agreement
  /\ NoOppositeDecision
  /\ Validity
  /\ WeakValidity
  /\ FailureDetectionSound

\* Decisions are irrevocable.
DecisionStable ==
  [][\A p \in Proc :
       decision[p] # None => decision'[p] = decision[p]]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

AllCorrectDecided == \A p \in alive : decision[p] # None

\* All non-faulty processes eventually decide despite up to F crashes.
Termination == <>[](AllCorrectDecided)

\* Progress with a threshold: if the number of guaranteed non-faulty
\* processes exceeds 2F, all non-faulty processes eventually decide.
Progress ==
  ((N - F) > 2 * F) => <>(AllCorrectDecided)

=============================================================================