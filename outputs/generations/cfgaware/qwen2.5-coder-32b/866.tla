---------------------------- MODULE FastPaxos ----------------------------

CONSTANTS 
    \* The set of all processes (proposers and acceptors)
    Procs,
    
    \* The set of all possible values that can be proposed
    Values
    
VARIABLES 
    \* The current round number for each process
    Round,
    
    \* The highest accepted round number for each process
    HighRound,
    
    \* The value accepted in the highest round for each process
    AcceptedValue,
    
    \* The set of acceptors that have accepted a proposal in a given round
    Accepts,
    
    \* The proposed value in a given round by a proposer
    ProposedValue

\* Type Invariants
FastTypeOK == 
    /\ Round \in [Procs -> Nat]
    /\ HighRound \in [Procs -> Nat]
    /\ AcceptedValue \in [Procs -> (Values \cup {<<>>})]
    /\ Accepts \in [Nat -> SUBSET Procs]
    /\ ProposedValue \in [Nat -> (Values \cup {<<>>})]

\* Initial predicate
Init == 
    /\ Round = [p \in Procs |-> 0]
    /\ HighRound = [p \in Procs |-> 0]
    /\ AcceptedValue = [p \in Procs |-> <<>>]
    /\ Accepts = [r \in Nat |-> {}]
    /\ ProposedValue = [r \in Nat |-> <<>>]

\* Next-state action for proposing a value
Propose(v) == 
    \/ \E p \in Procs : 
        LET r == Round[p] + 1 IN
            /\ Round' = [Round EXCEPT ![p] = r]
            /\ ProposedValue' = [ProposedValue EXCEPT ![r] = v]

\* Next-state action for accepting a proposal
Accept(p, r) ==
    \/ \E q \in Procs : 
        LET v == ProposedValue[r] IN
            /\ HighRound[q]' = Max(HighRound[q], r)
            /\ AcceptedValue[q]' = IF r >= HighRound[q] THEN v ELSE AcceptedValue[q]
            /\ Accepts' = [Accepts EXCEPT ![r] = Accepts[r] \cup {q}]

\* Next-state action for learning a decision
Learn(p, r) ==
    \/ \E q \in Procs : 
        LET S == Accepts[r] IN
            /\ IF Cardinality(S) > (Cardinality(Procs) DIV 2) THEN
                /\ HighRound[p]' = Max(HighRound[p], r)
                /\ AcceptedValue[p]' = AcceptedValue[q]
            ELSE
                UNCHANGED <<HighRound, AcceptedValue>>

\* Next-state relation
Next == 
    \/ \E v \in Values : Propose(v)
    \/ \E p \in Procs, r \in Nat : Accept(p, r)
    \/ \E p \in Procs, r \in Nat : Learn(p, r)

\* Specification of the system
Spec == Init /\ [][Next]_<<Round, HighRound, AcceptedValue, Accepts, ProposedValue>>

\* Non-triviality safety property: Some process must eventually accept a value
FastNontriviality ==
    \E p \in Procs : <>[](AcceptedValue[p] /= <<>>)

\* Consistency safety property: All processes that have accepted a value must agree on it
PaxosConsistency ==
    \A v1, v2 \in Values :
        /\ \E r1, r2 \in Nat, p1, p2 \in Procs : 
            /\ HighRound[p1] >= r1
            /\ AcceptedValue[p1] = v1
            /\ HighRound[p2] >= r2
            /\ AcceptedValue[p2] = v2
        => v1 = v2

\* Full specification with invariants and properties
FastSpec == Spec /\ []FastTypeOK /\ FastNontriviality /\ PaxosConsistency

=============================================================================