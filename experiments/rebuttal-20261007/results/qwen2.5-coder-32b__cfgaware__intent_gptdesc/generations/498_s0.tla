---------------------------- MODULE MultiInstanceConsensus ----------------------------

CONSTANTS Values, Slots

VARIABLES proposals, decisions

(*--algorithm multi_instance_consensus

variables 
    proposals = [s \in Slots | {}],  \* Proposed values per slot
    decisions = [s \in Slots | <<>>]; \* Chosen value per slot (empty sequence if no decision)

fair process proposer \in 1..[<<Slots>>] do
    while TRUE do
        with v \in Values do
            proposals' = [proposals EXCEPT ![self] = proposals[self] \cup {v}];
            await decisions[self] = <<>>;
        end with;
    end while;
end process;

fair process chooser \in Slots do
    while decisions[self] = <<>> do
        if proposals[self] /= {} then
            with v \in proposals[self] do
                decisions' = [decisions EXCEPT ![self] = <<v>>];
            end with;
        end if;
    end while;
end process;

\* Type invariants
TypeOK == /\ proposals \in [Slots -> SUBSET Values]
          /\ decisions \in [Slots -> {<<>>, <<v>> : v \in Values}]

\* Safety properties
Safety == /\ \A s \in Slots: decisions[s] = <<>> \/ decisions[s][1] \in proposals[s]
          /\ \A s \in Slots: Len(decisions[s]) <= 1

\* Liveness property
LiveSpec == \A s \in Slots: <>[] decisions[s] /= <<>>

end algorithm *)

=============================================================================