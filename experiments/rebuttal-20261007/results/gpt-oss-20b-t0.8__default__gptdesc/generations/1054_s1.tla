MODULE TokenRing
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, M

Assumptions == N >= 1 /\ M >= 1 /\ N <= M + 1

VARIABLE v

Init ==
    /\ v \in [0..N-1 -> 0..M-1]

Update(i) ==
    IF i = 0
       THEN /\ v[0] # ((v[N-1] + 1) MOD M)
            /\ v' = [v EXCEPT ![0] = ((v[N-1] + 1) MOD M)]
       ELSE /\ v[i] # v[i-1]
            /\ v' = [v EXCEPT ![i] = v[i-1]]

Next == \E i \in 0..N-1 : Update(i)

TypeInvariant ==
    /\ v \in [0..N-1 -> 0..M-1]

CountVal(val) ==
    # { i | v[i] = val }

UniqueToken ==
    \E i \in 0..N-1 : CountVal(v[i]) = 1

SafetyInvariant == []TypeInvariant
LivenessProperty == <>[]UniqueToken

Spec == Assumptions /\ Init /\ [][Next]_v /\ WF_vars(Next)

END MODULE