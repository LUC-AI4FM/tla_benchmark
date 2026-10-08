---------------------------- MODULE PaxosSpec ----------------------------

CONSTANTS Replicas, Values, Ballots, Quorums

ASSUME Cardinality(Replicas) > 1
ASSUME \A q \in Quorums : q \subseteq Replicas /\ Cardinality(q) > Cardinality(Replicas) / 2
ASSUME \A q1, q2 \in Quorums : q1 \cap q2 # {}

VARIABLES acceptedBallots, acceptedValues, decidedValue

(* --algorithm Paxos
variables 
    acceptedBallots = [r \in Replicas |-> <<0, "">>],  (* ballot, value *)
    acceptedValues = [v \in Values |-> {}],
    decidedValue = ""

process (Replica \in Replicas) \in
1. while TRUE do
2.   with ballot \in Ballots \ {b \in Ballots | \E r \in Replicas : b <= acceptedBallots[r][1]} do
3.     broadcast <<Prepare, Replica, ballot>> to all replicas;
4.     await quorum of replies from replicas such that
5.       /\ \A r \in (Replies) : Replies[r] = <<Promise, r, acceptedBallots[r][1], acceptedBallots[r][2]>>;
6.     with highestAcceptedBallot \in Ballots,
7.          highestAcceptedValue \in Values \cup {""} do
8.       assert \A r \in (Replies) : Replies[r][2] <= highestAcceptedBallot;
9.       assert \A b \in Ballots, v \in Values : 
10.         /\ (b < highestAcceptedBallot => acceptedValues[v] = {})
11.         \/ (b = highestAcceptedBallot => acceptedValues[v] = {r \in Replicas | Replies[r][2] = b /\ Replies[r][3] = v});
12.       with value \in IF highestAcceptedValue # "" THEN {highestAcceptedValue} ELSE Values do
13.         broadcast <<Accept, Replica, ballot, value>> to all replicas;
14.         await quorum of replies from replicas such that
15.           /\ \A r \in (Replies) : Replies[r] = <<Accepted, r, ballot>>;
16.         if decidedValue = "" then
17.           decidedValue := CHOOSE v \in value;
18.         end if;
19.     end with;
20.   end with;
21. end while;

end process;

fairness 1

PaxosTypeOK == /\ acceptedBallots \in [Replicas -> Ballots \X (Values \cup {""})]
               /\ acceptedValues \in [Values -> SUBSET Replicas]
               /\ decidedValue \in Values \cup {""}

PaxosNontriviality == \A v \in Values : v = decidedValue => \E r \in Replicas, b \in Ballots : <<Accept, r, b, v>> \in (Recieved)

PaxosConsistency == \/ decidedValue = ""
                    \/ \A v \in Values : v # decidedValue => /\ acceptedValues[v] = {}
                                                           /\ \A r \in Replicas : acceptedBallots[r][2] # v

end algorithm *)

Spec == /\ PaxosTypeOK
        /\ []PaxosNontriviality
        /\ []PaxosConsistency
        /\ SF_<<decidedValue, "">>

=============================================================================