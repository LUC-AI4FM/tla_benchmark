```tla
------------------------------- MODULE TerminationDetection -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node

VARIABLES state, detected

(* --algorithm TerminationDetection
variables 
    state = [n \in Node |-> FALSE],  \* FALSE means inactive, TRUE means active
    detected = FALSE;                \* Global termination detection flag

process Node \in Node
vars nextNode
begin
    nextNode := CHOOSE n \in Node : n /= self;
    while TRUE do
        if state[self] then
            either
                await state[nextNode];
                state[nextNode] := TRUE;
            or
                state[self] := FALSE;
            end either;
        else
            detected := FALSE;
        end if;
        await \A n \in Node : ~state[n] => detected;
    od;
end process;

fairness 1 \A s \in SUBSET Node: 
    \E self \in s: /\ state[self]
                  /\ \A n \notin s \/ n = self: ~state[n]
                  -> <>[<>UNCHANGED <<detected>> /\ state' = [state EXCEPT ![self] = FALSE]]

fairness 2
    \A s \in SUBSET Node:
        /\ \A n \in s: ~state[n]
        => <><<detected' = TRUE>>

Init == /\ state \in [Node -> BOOLEAN]
        /\ detected = FALSE

Next == \/ \E self \in Node: 
                (/\ state[self] 
                 /\ \/ (\E nextNode \in Node : nextNode /= self /\ state[nextNode] 
                          /\ state' = [state EXCEPT ![nextNode] = TRUE])
                    \/ (state' = [state EXCEPT ![self] = FALSE]))
          \/ detected = FALSE
          \/ (/\ \A n \in Node: ~state[n]
              /\ detected')

Spec == Init /\ []Next /\ WF_<<1>> /\ SF_<<2>>

quiescence == <>[](\A n \in Node : ~state[n])

correctness == quiescence => <>[]detected

liveness == quiescence => <>[](<>[]detected)

==*)
END MODULE
```