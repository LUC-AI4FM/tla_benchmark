---------------------------- MODULE Consensus ----------------------------

CONSTANTS Values

VARIABLES chosen, proposedValues

(*--algorithm consensus
variables chosen = <<>>, proposedValues = {};
begin
    while TRUE do
        with proposal \in Values do
            if chosen = <<>> then
                proposedValues := proposedValues \cup {proposal};
                if CHOOSE p \in proposedValues : TRUE not in proposedValues \ {p} then
                    chosen := <<CHOOSE p \in proposedValues : TRUE>>;
                end if;
            end if;
        end with;
    end while;
end algorithm*)

Init == /\ chosen = <<>>
        /\ proposedValues = {}

Next ==
    \/ /\ chosen = <<>>
       /\ \/ \E proposal \in Values :
              /\ proposedValues' = proposedValues \cup {proposal}
              /\ (/\ CHOOSE p \in proposedValues : TRUE not in proposedValues \ {p}
                  -> chosen' = <<CHOOSE p \in proposedValues : TRUE>>)
              /\ chosen' = chosen
       \/ /\ chosen' = chosen
          /\ proposedValues' = proposedValues

Spec == Init /\ [][Next]_<<chosen, proposedValues>>

TypeOK ==
    /\ chosen \in {<<>>, <<v>>: v \in Values}
    /\ proposedValues \subseteq Values

Validity == \/ chosen = <<>>
              \/ \/ \E v \in Values : chosen = <<v>>

Agreement == \/ chosen = <<>>
             \/ \/ \A v1, v2 \in Values :
                    (chosen = <<v1>> => v1 = v2)

Integrity ==
    /\ []<>(chosen = <<>>)
    /\ [](chosen' = chosen \/ chosen' = <<CHOOSE p \in proposedValues : TRUE>>)

EventualChoice ==
    <>(\E v \in Values : chosen = <<v>>)

Nontriviality ==
    <>[](\A proposal \in Values : proposal \notin proposedValues) => chosen = <<>>

LiveSpec == Spec /\ TypeOK /\ Validity /\ Agreement /\ Integrity /\ EventualChoice /\ Nontriviality

=============================================================================