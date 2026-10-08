--------------------------- MODULE TokenRing ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, K
ASSUME N > 0 /\ K > N

VARIABLE vals

(* Type invariant *)
ValsType == \A i \in 0..N-1 : 0 <= vals[i] /\ vals[i] < K

Init == ValsType

next(i) == (i + 1) \mod N
prev(i) == (i - 1 + N) \mod N

Token(i) == vals[i] != vals[prev(i)]

(* Atomic actions *)
Proc0 ==
    /\ vals[0] = vals[N-1]
    /\ LET newVal == (vals[0] + 1) \mod K IN
         vals' = [i \in 0..N-1 |-> IF i=0 THEN newVal ELSE vals[i]]

Other(p) ==
    /\ p \in 1..N-1
    /\ vals[p] != vals[p-1]
    /\ LET newVals == [i \in 0..N-1 |-> IF i=p THEN vals[p-1] ELSE vals[i]] IN
         vals' = newVals

Next ==
    \/ Proc0
    \/ \E p \in 1..N-1 : Other(p)

(* Safety invariant: some process always holds a token *)
SomeToken == \E i \in 0..N-1 : Token(i)

(* Liveness property: eventually exactly one token holder remains *)
ExactlyOneToken ==
    \E i \in 0..N-1 :
        /\ Token(i)
        /\ \A j \in 0..N-1 \ {i} : ~Token(j)

Spec == Init /\ [][Next]_vals /\ WF(Next)

THEOREM Spec => []SomeToken
THEOREM Spec => <>ExactlyOneToken

=============================================================================