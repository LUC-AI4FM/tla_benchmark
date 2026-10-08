```
MODULE NBAC
EXTENDS Integers, TLC

CONSTANTS NumProcs, Message
VARIABLES procState, messages, fd, outcome

Init ==
  /\ procState \in [1..NumProcs -> {"init"}]
  /\ messages = {}
  /\ fd \in [1..NumProcs -> {FALSE}]
  /\ outcome = "unknown"

Next ==
  \/ \E p \in 1..NumProcs :
    /\ procState[p] = "init"
    /\ procState' = [procState EXCEPT ![p] = "yes-vote"]
    /\ messages' = messages
    /\ fd' = fd
    /\ outcome' = outcome
  \/ \E p \in 1..NumProcs :
    /\ procState[p] = "init"
    /\ procState' = [procState EXCEPT ![p] = "no-vote"]
    /\ messages' = messages
    /\ fd' = fd
    /\ outcome' = outcome
  \/ \E p \in 1..NumProcs :
    /\ procState[p] = "yes-vote"
    /\ messages' = messages \cup {<<p, "yes">>}
    /\ fd' = fd
    /\ outcome' = outcome
  \/ \E p \in 1..NumProcs :
    /\ procState[p] = "no-vote"
    /\ messages' = messages \cup {<<p, "no">>}
    /\ fd' = fd
    /\ outcome' = outcome
  \/ \E p \in 1..NumProcs :
    /\ procState[p] # "init"
    /\ fd'[p] = TRUE
    /\ procState' = procState
    /\ messages' = messages
    /\ outcome' = outcome
  \/ \E p \in 1..NumProcs :
    /\ procState[p] # "init"
    /\ \E m \in messages :
      /\ fst(m) = p
      /\ snd(m) = "yes"
      /\ outcome' = "commit"
    /\ procState' = procState
    /\ messages' = messages
    /\ fd' = fd

Spec ==
  Init /\ [][Next]_<<procState, messages, fd, outcome>>

TypeInvariant ==
  procState \in [1..NumProcs -> {"init", "yes-vote", "no-vote"}]
  /\ messages \subseteq {[1..NumProcs] \X {("yes"), ("no")}}
  /\ fd \in [1..NumProcs -> {TRUE, FALSE}]
  /\ outcome \in {"unknown", "commit"}

ValidityCondition ==
  <>(\A p \in 1..NumProcs : procState[p] = "yes-vote") => <>outcome = "commit"

THEOREM Spec => []TypeInvariant
THEOREM Spec => ValidityCondition

Fairness == SF_VARIABLES (procState, messages, fd, outcome)
```
Note: SF_VARIABLES is used to specify the fairness condition for all variables. In a real-world scenario, you would need to fine-tune this to ensure that the specification accurately reflects the desired behavior.