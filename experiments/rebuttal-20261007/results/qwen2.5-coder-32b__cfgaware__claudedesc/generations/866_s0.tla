------------------------------- MODULE FastPaxos -------------------------------

CONSTANTS Replicas, Values, Ballots, ClassicQuorums, FastQuorums

VARIABLES ballot, value, decidedValue, cValue, p2bMessages

(* --algorithm fast_paxos

variables 
    ballot = [r \in Replicas |-> <<0, "">>],  \* <ballot_number, value>
    value = [r \in Replicas |-> ""],
    decidedValue = "",
    cValue = "",
    p2bMessages = [q \in ClassicQuorums \cup FastQuorums, r \in Replicas |-> <<0, "">>];

fair process (Replica \in Replicas) 
vars
    proposed_value,
    received_ballot,
    received_value
begin
    while TRUE do
        await ballot[Replica] /= <<0, "">>;
        received_ballot := ballot[Replica];
        if received_ballot[1] % 2 = 1 then \* Fast round
            proposed_value := CHOOSE v \in Values: TRUE;
            value[Replica] := proposed_value;
            foreach q \in FastQuorums do
                p2bMessages[q, Replica] := <<received_ballot, proposed_value>>;
            end foreach;
        else \* Classic round
            received_value := "";
            foreach q \in ClassicQuorums do
                if p2bMessages[q, Replica][1] = received_ballot then
                    received_value := IF received_value = "" THEN p2bMessages[q, Replica][2]
                                      ELSE IF received_value = p2bMessages[q, Replica][2] THEN received_value
                                      ELSE "COLLISION";
                end if;
            end foreach;
            if received_value /= "COLLISION" then
                value[Replica] := received_value;
                decidedValue := received_value;
            else \* Collision detected
                cValue := CHOOSE v \in Values: TRUE; \* Coordinator chooses a value
                ballot[Replica] := <<ballot[Replica][1] + 1, cValue>>;
            end if;
        end if;
    end while;
end process;

fair process (Coordinator \in Replicas) 
vars
    chosen_value,
    responses,
    majority_count,
    max_ballot,
    max_value
begin
    while TRUE do
        await ballot[Coordinator][1] % 2 = 0; \* Classic round
        chosen_value := "";
        responses := [q \in ClassicQuorums |-> ""];
        foreach q \in ClassicQuorums do
            majority_count := 0;
            max_ballot := 0;
            max_value := "";
            foreach r \in Replicas do
                if p2bMessages[q, r][1] = ballot[Coordinator] then
                    if p2bMessages[q, r][2] /= "" then
                        responses[q] := p2bMessages[q, r][2];
                        if responses[q] = max_value then
                            majority_count := majority_count + 1;
                        elsif majority_count = 0 then
                            max_value := responses[q];
                            majority_count := 1;
                        end if;
                    end if;
                end if;
            end foreach;
            if majority_count > 1 then
                chosen_value := max_value;
            else
                chosen_value := CHOOSE v \in Values: TRUE; \* Any proposed value
            end if;
        end foreach;
        decidedValue := chosen_value;
        ballot[Coordinator] := <<ballot[Coordinator][1] + 2, "">>;
    end while;
end process;

FastSpec == Init /\ [][Next]_<<ballot, value, decidedValue, cValue, p2bMessages>> /\ SF_FastDecide /\ SF_ClassicDecide

Init == /\ ballot = [r \in Replicas |-> <<0, "">>]
       /\ value = [r \in Replicas |-> ""]
       /\ decidedValue = ""
       /\ cValue = ""
       /\ p2bMessages = [q \in ClassicQuorums \cup FastQuorums, r \in Replicas |-> <<0, "">>]

Next == \/ \E Replica \in Replicas: ReplicaNext(Replica)
        \/ CoordinatorNext

ReplicaNext(Replica) ==
    /\ ballot[Replica] /= <<0, "">>
    /\ LET received_ballot == ballot[Replica]
       IN IF received_ballot[1] % 2 = 1 THEN
            \E proposed_value \in Values:
                /\ value' = [value EXCEPT ![Replica] = proposed_value]
                /\ p2bMessages' = [p2bMessages EXCEPT ![q \in FastQuorums][Replica] = <<received_ballot, proposed_value>>]
        ELSE
            LET received_value == CHOOSE v \in Values: TRUE
                IN /\ value' = [value EXCEPT ![Replica] = received_value]
                   /\ decidedValue' = received_value

CoordinatorNext ==
    /\ ballot[Coordinator][1] % 2 = 0
    /\ LET chosen_value == CHOOSE v \in Values: TRUE
       IN /\ decidedValue' = chosen_value
          /\ ballot' = [ballot EXCEPT ![Coordinator] = <<ballot[Coordinator][1] + 2, "">>]

FastTypeOK ==
    /\ \A r \in Replicas: ballot[r] \in Ballots
    /\ \A r \in Replicas: value[r] \in Values \/ value[r] = ""
    /\ decidedValue \in Values \/ decidedValue = ""
    /\ cValue \in Values \/ cValue = ""
    /\ \A q \in ClassicQuorums \cup FastQuorums, r \in Replicas: p2bMessages[q][r] \in Ballots

FastNontriviality ==
    /\ \A v \in Values: value[v] \in Values
    /\ decidedValue = "" \/ \E r \in Replicas: decidedValue = value[r]

PaxosConsistency ==
    \/ decidedValue = ""
    \/ \A r1, r2 \in Replicas: decidedValue = value[r1] => decidedValue = value[r2]

SF_FastDecide == <<\A q \in FastQuorums: \E v \in Values: \A r \in q: p2bMessages[q][r][2] = v>>_<<ballot, value, decidedValue, cValue, p2bMessages>>

SF_ClassicDecide == <<\A q \in ClassicQuorums: \E v \in Values: \A r \in q: p2bMessages[q][r][2] = v>>_<<ballot, value, decidedValue, cValue, p2bMessages>>

end algorithm *)
=============================================================================