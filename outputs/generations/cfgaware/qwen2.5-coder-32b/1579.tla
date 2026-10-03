------------------------------- MODULE DijkstraTokenRing -------------------------------
CONSTANTS N, K

ASSUME K > N /\ N > 0

VARIABLES values

(*--algorithm DijkstraTokenRing
variables values = [i \in 0..N-1 -> 0];

begin
    while TRUE do
        with
            for i \in 0..N-1 do
                if i = 0 then
                    if values[i] = values[N-1] then
                        values[i] := (values[i] + 1) % K;
                    end if;
                else
                    if values[i] /= values[(i-1) \% N] then
                        values[i] := values[(i-1) \% N];
                    end if;
                end if;
            end for;
        end with;
    end while;
end algorithm;*)

Spec == 
    /\ Init
    /\ [][Next]_<<values>>
    /\ WF_next(<<values>>)

Init == values \in [0..N-1 -> 0..K-1]

Next ==
    \/ /\ UNCHANGED values
       \/ \E i \in 0..N-1 :
            (i = 0 /\ values' = [values EXCEPT ![i] = (IF values[i] = values[N-1] THEN (values[i] + 1) % K ELSE values[i])])
             \/ (i /= 0 /\ values' = [values EXCEPT ![i] = (IF values[i] # values[(i-1) \% N] THEN values[(i-1) \% N] ELSE values[i])])

WF_next == WF_vars(<<values>>, Next)

SomeoneHoldsToken ==
    \E i \in 0..N-1 : values[i] # values[(i+1) \% N]

EventuallyJustOneHoldsToken ==
    <>[] (\A i, j \in 0..N-1 : (i = j \/ values[i] # values[j]))

THEOREM Spec => []<>SomeoneHoldsToken

THEOREM Spec => <><>EventuallyJustOneHoldsToken
=============================================================================