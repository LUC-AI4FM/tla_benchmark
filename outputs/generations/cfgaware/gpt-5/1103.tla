---- MODULE NBAC ----
EXTENDS Naturals

CONSTANT N

(*
  Processes are 1..N
*)
Proc == 1..N

(*
  Basic atoms
*)
VOTE == "VOTE"
DECIDE == "DECIDE"

YES == "YES"
NO == "NO"
Votes == {YES, NO}

COMMIT == "COMMIT"
ABORT == "ABORT"
Decisions == {COMMIT, ABORT}

UNKNOWN == "UNKNOWN"
UNDECIDED == "UNDECIDED"
VoteOrUnknown == Votes \cup {UNKNOWN}
DecOrUndec == Decisions \cup {UNDECIDED}

(*
  Messages
*)
Msg ==
  { [type |-> VOTE,   from |-> i, to |-> j, val |-> v] : i \in Proc, j \in Proc, v \in Votes } \cup
  { [type |-> DECIDE, from |-> i, to |-> j, val |-> d] : i \in Proc, j \in Proc, d \in Decisions }

(*
  State variables
    - vote[p]       fixed initial vote of process p
    - started[p]    whether p has broadcast its vote
    - decided[p]    p's decision (UNDECIDED, COMMIT, ABORT)
    - votesSeen[p][q]  last vote of q known by p (or UNKNOWN)
    - FD[p]         p's current suspicion set (arbitrary, nondeterministic)
    - crashed       set of crashed processes
    - Net           set of in-flight messages (as records from Msg)
*)
VARIABLES vote, started, decided, votesSeen, FD, crashed, Net

vars == << vote, started, decided, votesSeen, FD, crashed, Net >>

(*
  Initialization
*)
Init ==
  /\ vote \in [Proc -> Votes]
  /\ started = [p \in Proc |-> FALSE]
  /\ decided = [p \in Proc |-> UNDECIDED]
  /\ votesSeen = [p \in Proc |-> [q \in Proc |-> UNKNOWN]]
  /\ FD \in [Proc -> SUBSET Proc]
  /\ crashed = {}
  /\ Net = {}

(*
  Helper predicates on a snapshot (used in guards)
*)
DecidedValue(p, d) == d[p] \in Decisions

(*
  One atomic step by a non-crashed process p:
    - optionally receive at most one message addressed to p
    - update its failure detector arbitrarily
    - perform local transitions (start by broadcasting its vote; decide and broadcast a decision)
*)
Step(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ \E F \in SUBSET Proc,
       doRecv \in BOOLEAN,
       m \in Msg:
       /\ (doRecv => m \in Net /\ m.to = p /\ m.type \in {VOTE, DECIDE})
       /\ LET
            vsAfterRecv ==
              IF doRecv /\ m.type = VOTE
                 THEN [votesSeen EXCEPT ![p][m.from] = m.val]
                 ELSE votesSeen
            decAfterRecv ==
              IF doRecv /\ m.type = DECIDE
                 THEN [decided EXCEPT ![p] = m.val]
                 ELSE decided
            netAfterRecv ==
              IF doRecv THEN Net \ {m} ELSE Net

            started2 ==
              IF ~started[p]
                THEN [started EXCEPT ![p] = TRUE]
                ELSE started

            netAfterStart ==
              IF ~started[p]
                THEN netAfterRecv \cup { [type |-> VOTE, from |-> p, to |-> j, val |-> vote[p]] : j \in Proc }
                ELSE netAfterRecv

            canAbort ==
              ~DecidedValue(p, decAfterRecv) /\ (\E q \in Proc : vsAfterRecv[p][q] = NO)

            canCommit ==
              ~DecidedValue(p, decAfterRecv) /\
              (\A q \in Proc : vsAfterRecv[p][q] = YES)

            decAfterLocal ==
              IF canAbort
                THEN [decAfterRecv EXCEPT ![p] = ABORT]
              ELSE IF canCommit
                THEN [decAfterRecv EXCEPT ![p] = COMMIT]
              ELSE decAfterRecv

            netAfterDecide ==
              IF ~DecidedValue(p, decAfterRecv) /\ DecidedValue(p, decAfterLocal)
                THEN netAfterStart \cup { [type |-> DECIDE, from |-> p, to |-> j, val |-> decAfterLocal[p]] : j \in Proc }
                ELSE netAfterStart
          IN
            /\ FD' = [FD EXCEPT ![p] = F]
            /\ votesSeen' = vsAfterRecv
            /\ decided' = decAfterLocal
            /\ started' = started2
            /\ Net' = netAfterDecide
  /\ UNCHANGED << vote, crashed >>

(*
  Crash of a process
*)
Crash(p) ==
  /\ p \in Proc
  /\ p \notin crashed
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED << vote, started, decided, votesSeen, FD, Net >>

(*
  Next-state relation
*)
Next ==
  \E p \in Proc :
    Step(p) \/ Crash(p)

(*
  Type correctness invariant
*)
TypeOK ==
  /\ Proc = 1..N
  /\ vote \in [Proc -> Votes]
  /\ started \in [Proc -> BOOLEAN]
  /\ decided \in [Proc -> DecOrUndec]
  /\ votesSeen \in [Proc -> [Proc -> VoteOrUnknown]]
  /\ FD \in [Proc -> SUBSET Proc]
  /\ crashed \subseteq Proc
  /\ Net \subseteq Msg

(*
  Agreement (no two processes decide differently)
*)
Agreement ==
  \A p, q \in Proc :
    decided[p] \in Decisions /\ decided[q] \in Decisions => decided[p] = decided[q]

(*
  Validity (safety): if some process commits then all votes were YES
*)
CommitImpliesAllYes ==
  (\E p \in Proc : decided[p] = COMMIT) =>
  (\A q \in Proc : vote[q] = YES)

(*
  Validity (possibility): if all votes are YES, a commit is possible on some behavior
  (temporal liveness schema that can be checked separately if desired)
*)
AllYes == \A p \in Proc : vote[p] = YES
SomeCommit == \E p \in Proc : decided[p] = COMMIT
ValidityPossibleCommit == AllYes => <> SomeCommit

(*
  Specification
*)
Spec == Init /\ [][Next]_vars

====