```
MODULE AsynchronousAtomicCommitment
EXTENDS Integers, Sequences, TLC

CONSTANTS ProcSet, QuorumSet
VARIABLES votes, suspected, messages, decided, crashed

Init ==
  /\ votes \in [ProcSet -> {YES, NO}]
  /\ suspected \in [ProcSet -> BOOLEAN]
  /\ messages \in [ProcSet -> Seq(ProcSet)]
  /\ decided \in [ProcSet -> {ABORT, COMMIT}]
  /\ crashed \in [ProcSet -> BOOLEAN]
  /\ (\/ p \in ProcSet : votes[p] = YES) \/ (\/ p \in ProcSet : votes[p] = NO)

Next ==
  /\ IF /\ ~ ENABLED(<Send>_)
        /\ ~ ENABLED(<Receive>_)
        /\ ~ ENABLED(<Fail>_)
      THEN UNCHANGED <<votes, suspected, messages, decided, crashed>>
  ELSE
    \/ <Send>_ 
    \/ <Receive>_
    \/ <Fail>_
    \/ <Crash>_

Send(p) ==
  /\ p \in ProcSet
  /\ votes[p] = YES
  /\ ~ suspected[p]
  /\ ~ crashed[p]
  /\ messages' = [messages EXCEPT ![p] = Append(messages[p], p)]
  /\ UNCHANGED <<votes, suspected, decided, crashed>>

Receive(p) ==
  /\ p \in ProcSet
  /\ ~ suspected[p]
  /\ ~ crashed[p]
  /\ messages' = [messages EXCEPT ![p] = Tail(messages[p])]
  /\ IF Head(messages[p]) = YES THEN votes'[p] = YES ELSE votes'[p] = NO
  /\ UNCHANGED <<suspected, decided, crashed>>

Fail(p) ==
  /\ p \in ProcSet
  /\ ~ suspected[p]
  /\ ~ crashed[p]
  /\ suspected' = [suspected EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<votes, messages, decided, crashed>>

Crash(p) ==
  /\ p \in ProcSet
  /\ ~ crashed[p]
  /\ crashed' = [crashed EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<votes, suspected, messages, decided>>

DecideABORT(p) ==
  /\ p \in ProcSet
  /\ votes[p] = NO
  /\ ~ suspected[p]
  /\ ~ crashed[p]
  /\ decided' = [decided EXCEPT ![p] = ABORT]
  /\ UNCHANGED <<votes, suspected, messages, crashed>>

DecideCOMMIT(p) ==
  /\ p \in ProcSet
  /\ votes[p] = YES
  /\ ~ suspected[p]
  /\ ~ crashed[p]
  /\ decided' = [decided EXCEPT ![p] = COMMIT]
  /\ UNCHANGED <<votes, suspected, messages, crashed>>

TypeInvariant ==
  /\ votes \in [ProcSet -> {YES, NO}]
  /\ suspected \in [ProcSet -> BOOLEAN]
  /\ messages \in [ProcSet -> Seq(ProcSet)]
  /\ decided \in [ProcSet -> {ABORT, COMMIT}]
  /\ crashed \in [ProcSet -> BOOLEAN]

Agreement ==
  []<>(\E p \in ProcSet : decided[p] = ABORT) => []<>(\A p \in ProcSet : ~ suspected[p] => decided[p] = ABORT)
  []<>(\E p \in ProcSet : decided[p] = COMMIT) => []<>(\A p \in ProcSet : ~ suspected[p] => decided[p] = COMMIT)

AbortValidity ==
  []<>(\E p \in ProcSet : decided[p] = ABORT) => <>(\E p \in ProcSet : votes[p] = NO)

CommitValidity ==
  []<>(\E p \in ProcSet : decided[p] = COMMIT) => (\A p \in ProcSet : votes[p] = YES)

Termination ==
  []<>(\A p \in ProcSet : ~ suspected[p] => decided[p] \in {ABORT, COMMIT})

EventualCommit ==
  []<>(\A p \in ProcSet : ~ suspected[p] /\ votes[p] = YES) => <>(\E p \in ProcSet : decided[p] = COMMIT)

Fairness ==
  WF_vars({Send}, <<votes, suspected, messages, decided, crashed>>)
  WF_vars({Receive}, <<votes, suspected, messages, decided, crashed>>)
  WF_vars({Fail}, <<votes, suspected, messages, decided, crashed>>)
  SF_vars({Crash}, <<votes, suspected, messages, decided, crashed>>)

Spec ==
  /\ Init
  /\ [][Next]_<<votes, suspected, messages, decided, crashed>>
  /\ TypeInvariant
  /\ Agreement
  /\ AbortValidity
  /\ CommitValidity
  /\ Termination
  /\ EventualCommit
  /\ Fairness

THEOREM Spec => []TypeInvariant
```