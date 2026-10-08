```
MODULE AsynchronousAtomicCommit
EXTENDS Integers, Sequences, TLC

CONSTANTS P, Quorum
VARIABLES state, votes, suspected, messages, decided

Init ==
  /\ state \in [P -> {"initial", "voted_yes", "voted_no", "aborted", "committed"}]
  /\ votes \in [P -> {"yes" | "no"}]
  /\ suspected \in [P -> BOOLEAN]
  /\ messages \in [P -> Seq(BOOLEAN)]
  /\ decided \in {"abort" | "commit" | "undecided"}
  /\ \A p \in P : state[p] = "initial"
  /\ (\A p \in P : votes[p] = "yes") \/ (\A p \in P : votes[p] = "no")

Next ==
  /\ \E p \in P :
    (state[p] = "initial" /\ votes[p] = "yes" /\ state' = [state EXCEPT ![p] = "voted_yes"])
      \/ (state[p] = "initial" /\ votes[p] = "no" /\ state' = [state EXCEPT ![p] = "voted_no"])
      \/ (state[p] \in {"voted_yes", "voted_no"} /\ suspected'[p] = TRUE /\ state' = [state EXCEPT ![p] = "aborted"])
      \/ (state[p] \in {"voted_yes", "voted_no"} /\ messages'[p] = Append(messages[p], TRUE) /\ state' = [state EXCEPT ![p] = "committed"])
  /\ suspected' = suspected
  /\ messages' = messages
  /\ decided' = IF (\E p \in P : state[p] = "aborted") THEN "abort" ELSE IF (\E p \in P : state[p] = "committed") THEN "commit" ELSE "undecided"

Spec ==
  Init /\ [][Next]_state

TypeInvariant ==
  /\ state \in [P -> {"initial", "voted_yes", "voted_no", "aborted", "committed"}]
  /\ votes \in [P -> {"yes" | "no"}]
  /\ suspected \in [P -> BOOLEAN]
  /\ messages \in [P -> Seq(BOOLEAN)]
  /\ decided \in {"abort" | "commit" | "undecided"}

Agreement ==
  []<>(\A p, q \in P : (decided = "commit") => (state[p] = state[q]))

AbortValidity ==
  []<>(\A p \in P : (decided = "abort") => (\E q \in P : votes[q] = "no"))

CommitValidity ==
  []<>(\A p \in P : (decided = "commit") => (\A q \in P : votes[q] = "yes"))

Termination ==
  <>[]<>(decided \in {"abort", "commit"})

EventualCommit ==
  []<>(\A p \in P : decided = "commit")

THEOREM Spec => []TypeInvariant
THEOREM Spec => Agreement
THEOREM Spec => AbortValidity
THEOREM Spec => CommitValidity
THEOREM Spec => Termination
THEOREM Spec => EventualCommit

Fairness ==
  WF_vars(Next, state)

```