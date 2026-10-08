```
MODULE NBAC
EXTENDS Integers, TLC

CONSTANTS ProcSet, Quorum
VARIABLES state, vote, messages, failures, fd

Init ==
  /\ state \in [ProcSet -> {"init", "yes", "no"}]
  /\ vote = [p \in ProcSet |-> "undecided"]
  /\ messages = <<>>
  /\ failures = {}
  /\ fd = [p \in ProcSet |-> {}]

Next ==
  /\ IF \E p \in ProcSet :
        /\ state[p] = "init"
        /\ vote[p] = "undecided"
        /\ messages' = Append(messages, <<p, "yes">>)
        /\ state' = [state EXCEPT ![p] = "yes"]
        /\ vote' = [vote EXCEPT ![p] = "yes"]
        /\ failures' = failures
        /\ fd' = fd
    OR 
        /\ state[p] = "init"
        /\ vote[p] = "undecided"
        /\ messages' = Append(messages, <<p, "no">>)
        /\ state' = [state EXCEPT ![p] = "no"]
        /\ vote' = [vote EXCEPT ![p] = "no"]
        /\ failures' = failures
        /\ fd' = fd
    OR 
        /\ \E m \in messages :
           /\ state[p] = "yes"
           /\ m = <<q, "yes">>
           /\ messages' = Append(messages, <<p, "ack">>)
           /\ state' = [state EXCEPT ![p] = "ack"]
           /\ vote' = vote
           /\ failures' = failures
           /\ fd' = fd
    OR 
        /\ \E m \in messages :
           /\ state[p] = "no"
           /\ m = <<q, "no">>
           /\ messages' = Append(messages, <<p, "nak">>)
           /\ state' = [state EXCEPT ![p] = "nak"]
           /\ vote' = vote
           /\ failures' = failures
           /\ fd' = fd
    OR 
        /\ p \in ProcSet
        /\ failures' = failures \cup {p}
        /\ messages' = messages
        /\ state' = [state EXCEPT ![p] = "crashed"]
        /\ vote' = vote
        /\ fd' = [fd EXCEPT ![p] = {}]
    OR 
        /\ p \in ProcSet
        /\ failures' = failures
        /\ messages' = messages
        /\ state' = state
        /\ vote' = vote
        /\ fd' = [fd EXCEPT ![p] = fd[p] \cup {q \in ProcSet}]
  ELSE 
    /\ messages' = messages
    /\ state' = state
    /\ vote' = vote
    /\ failures' = failures
    /\ fd' = fd

Spec == Init /\ [][Next]_state /\ [][Next]_vote /\ [][Next]_messages /\ [][Next]_failures /\ [][Next]_fd

TypeInvariant ==
  state \in [ProcSet -> {"init", "yes", "no", "ack", "nak", "crashed"}]
  /\ vote \in [ProcSet -> {"undecided", "yes", "no"}]
  /\ messages \in Seq(ProcSet \X {"yes" , "no", "ack", "nak"})
  /\ failures \subseteq ProcSet
  /\ fd \in [ProcSet -> SUBSET ProcSet]

ValidityInvariant ==
  \A p \in ProcSet : state[p] = "commit" => \A q \in ProcSet : vote[q] = "yes"

Fairness == SF_vars(failures)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []ValidityInvariant
```