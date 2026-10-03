------------------------------ MODULE AtomicCommit ------------------------------
EXTENDS Naturals, Sequences

CONSTANT N \* number of processes

VARIABLES vote, status, inbox, suspicion

(* Type invariant *)
TypeOK == /\ vote \in [1..N -> {"YES","NO"}]
          /\ status \in [1..N -> {"Alive", "Crashed", "CommitDecided", "AbortDecided"}]
          /\ inbox \in [1..N -> SUBSET {"YES","NO"}]
          /\ suspicion \in [1..N -> SUBSET 1..N]

(* Initial conditions: all vote YES or all vote NO *)
AllYes == \A i ∈ 1..N : vote[i] = "YES"
AllNo  == \A i ∈ 1..N : vote[i] = "NO"

Init ==
    /\ N >= 1
    /\ vote \in [1..N -> {"YES","NO"}]
    /\ (AllYes \/ AllNo)
    /\ status = [i \in 1..N |-> "Alive"]
    /\ inbox = [i \in 1..N |-> {}]
    /\ suspicion = [i \in 1..N |-> {}]

(* Actions *)

SendVote ==
    \E i ∈ 1..N :
        /\ status[i] = "Alive"
        /\ inbox' = [k ∈ 1..N |
                        IF k = i THEN inbox[k]
                        ELSE inbox[k] ∪ {vote[i]}]
        /\ UNCHANGED << vote, status, suspicion >>

Decision ==
    \E i ∈ 1..N :
        /\ status[i] = "Alive"
        /\ IF "NO" ∈ inbox[i] THEN
                status' = [status EXCEPT ![i] = "AbortDecided"]
           ELSEIF (\A k ∈ 1..N \ suspicion[i] :
                       vote[k] = "YES" /\ vote[k] ∈ inbox[i]) THEN
                status' = [status EXCEPT ![i] = "CommitDecided"]
           ELSE
                status' = status
        /\ UNCHANGED << vote, inbox, suspicion >>

Crash ==
    \E i ∈ 1..N :
        /\ status[i] = "Alive"
        /\ status' = [status EXCEPT ![i] = "Crashed"]
        /\ UNCHANGED << vote, inbox, suspicion >>

Suspect ==
    \E i,j ∈ 1..N :
        /\ i ≠ j
        /\ status[i] = "Alive"
        /\ j ∉ suspicion[i]
        /\ suspicion' = [suspicion EXCEPT ![i] = suspicion[i] ∪ {j}]
        /\ UNCHANGED << vote, status, inbox >>

NonStutter == SendVote \/ Decision \/ Crash \/ Suspect

Spec ==
    Init
    /\ [][NonStutter]_vars
    /\ WF_vars(NonStutter)

(* Temporal properties *)

AgrrLtl ==
    [] (\A i,j ∈ 1..N :
            (status[i] ∈ {"CommitDecided","AbortDecided"} /\
             status[j] ∈ {"CommitDecided","AbortDecided"}) =>
            status[i] = status[j])

AbortValidityLtl ==
    [] ((\E i ∈ 1..N : vote[i] = "NO") => <> (\E j ∈ 1..N : status[j] = "AbortDecided"))

CommitValidityLtl ==
    [] ((\A i ∈ 1..N : vote[i] = "YES" /\ status[i] = "Alive")
        => <> (\A i ∈ 1..N : status[i] = "CommitDecided"))

TerminationLtl ==
    [] (\A i ∈ 1..N :
            status[i] = "Alive"
            => <> (status[i] = "CommitDecided" \/ status[i] = "AbortDecided"))
=============================================================================