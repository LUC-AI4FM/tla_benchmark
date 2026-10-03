```tla
------------------------------- MODULE SingleValueConsensus -------------------------------

CONSTANTS Values

VARIABLES chosen

(*--algorithm SingleValueConsensus
variables chosen = {};

begin
    while TRUE do
        if chosen = {} then
            with v \in Values do
                chosen := {v};
            end with;
        end if;
    end while;
end algorithm;*)

Init == chosen = {}

Next ==
    \/ /\ chosen = {}
       /\ \E v \in Values : chosen' = {v}
    \/ /\ chosen /= {}
       /\ chosen' = chosen

Spec == Init /\ [][Next]_<<chosen>>

\* Safety: At most one value is ever chosen
Safety == \A s \in StateSpace : Len(chosen) <= 1

\* Liveness: Eventually some value is chosen
LiveSpec == Spec /\ WF_next(Next)

StateSpace == {s \in [][Nat -> [chosen: SUBSET Values]] : Init /\ \A i \in Nat : Next[s[i], s[i+1]]}

WF_next(next) ==
    \A S \subseteq StateSpace :
        (\E s \in S : \A t \in S : <<s, t>> \notin next)
        -> (\E s \in S : \E t \in StateSpace : <<s, t>> \in next)

THEOREM Spec => []Safety

THEOREM LiveSpec => <>[](\E v \in Values : chosen = {v})

END SingleValueConsensus
```