------------------------------- MODULE Paxos -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Replicas, Values, Ballots, Quorums

VARIABLES ballot_counter, proposals, promises, accepted_ballot_value, decided_value

Init == /\ ballot_counter = 0
        /\ proposals = [r \in Replicas |-> {}]
        /\ promises = [b \in Ballots |-> [r \in Replicas |-> <<0, NULL>>]]
        /\ accepted_ballot_value = [r \in Replicas |-> <<0, NULL>>]
        /\ decided_value = NULL

Prepare(r) == 
    /\ ballot_counter' = ballot_counter + 1
    /\ proposals' = [proposals EXCEPT ![r] = proposals[r] \cup {ballot_counter}]
    /\ UNCHANGED <<promises, accepted_ballot_value, decided_value>>

Promise(r, b, highest_b, v) ==
    \/ /\ b > highest_b
       /\ promises' = [promises EXCEPT ![b][r] = <<highest_b, v>>]
       /\ UNCHANGED <<ballot_counter, proposals, accepted_ballot_value, decided_value>>
    \/ /\ b <= highest_b
       /\ UNCHANGED <<ballot_counter, proposals, promises, accepted_ballot_value, decided_value>>

Accept(r, b, v) ==
    LET quorum = CHOOSE q \in Quorums : TRUE
        chosen_v = IF \E r' \in quorum : fst(promises[b][r']) > 0 THEN 
                       CHOOSE v' \in Values : \A r'' \in quorum : (fst(promises[b][r'']) = 0 \/ snd(promises[b][r'']) = v')
                   ELSE
                       v
    IN /\ accepted_ballot_value' = [accepted_ballot_value EXCEPT ![r] = <<b, chosen_v>>]
       /\ UNCHANGED <<ballot_counter, proposals, promises, decided_value>>

Accepted(r, b) ==
    LET quorum = CHOOSE q \in Quorums : TRUE
        v = snd(accepted_ballot_value[r])
    IN /\ IF (\A r' \in quorum : accepted_ballot_value[r'] = <<b, v>>)
           THEN decided_value' = v
           ELSE UNCHANGED decided_value
       /\ UNCHANGED <<ballot_counter, proposals, promises, accepted_ballot_value>>

Next ==
    \/ \E r \in Replicas : Prepare(r)
    \/ \E r \in Replicas, b \in Ballots, highest_b \in Ballots, v \in Values : Promise(r, b, highest_b, v)
    \/ \E r \in Replicas, b \in Ballots, v \in Values : Accept(r, b, v)
    \/ \E r \in Replicas, b \in Ballots : Accepted(r, b)

Spec ==
    /\ Init
    /\ [][Next]_<<ballot_counter, proposals, promises, accepted_ballot_value, decided_value>>
    /\ WF_next(<<ballot_counter, proposals, promises, accepted_ballot_value, decided_value>>)

NonTriviality == \A v \in Values : v = decided_value => \E r \in Replicas, b \in Ballots : <<b, v>> \in proposals[r]

Consistency == \A v1, v2 \in Values : v1 /= v2 => \/ v1 # decided_value
                                               \/ v2 # decided_value

SafetyProperties == /\ NonTriviality
                    /\ Consistency

SpecWithSafety ==
    /\ Spec
    /\ SafetyProperties

WF_next(vars) == WF_vars(Next, vars)

=============================================================================