```
MODULE FastMutex
EXTENDS Integers, Sequences

CONSTANTS M, N

VARIABLES x, y, b, pc1, pc2, cs

Init == (* Initial conditions *)
        /\ x = 0
        /\ y = 0
        /\ b = FALSE
        /\ pc1 = [i \in 1..M |-> "init"]
        /\ pc2 = [i \in (M+1)..N |-> "init"]
        /\ cs = {}

Next == (* Next state relation *)
        \/ \E i \in 1..M : 
            (pc1[i] = "init" /\ x' = i /\ pc1' = [pc1 EXCEPT ![i] = "try"])
            \/ (pc1[i] = "try" /\ y' = i /\ pc1' = [pc1 EXCEPT ![i] = "wait"])
            \/ (pc1[i] = "wait" /\ b' = TRUE /\ x' = 0 /\ pc1' = [pc1 EXCEPT ![i] = "cs"])
            \/ (pc1[i] = "cs" /\ cs' = cs \cup {i} /\ pc1' = [pc1 EXCEPT ![i] = "exit"])
            \/ (pc1[i] = "exit" /\ cs' = cs \ {i} /\ pc1' = [pc1 EXCEPT ![i] = "init"])
        \/ \E i \in (M+1)..N : 
            (pc2[i] = "init" /\ x' = i /\ pc2' = [pc2 EXCEPT ![i] = "try"])
            \/ (pc2[i] = "try" /\ y' = i /\ pc2' = [pc2 EXCEPT ![i] = "wait"])
            \/ (pc2[i] = "wait" /\ b' = TRUE /\ x' = 0 /\ pc2' = [pc2 EXCEPT ![i] = "cs"])
            \/ (pc2[i] = "cs" /\ cs' = cs \cup {i} /\ pc2' = [pc2 EXCEPT ![i] = "exit"])
            \/ (pc2[i] = "exit" /\ cs' = cs \ {i} /\ pc2' = [pc2 EXCEPT ![i] = "init"])

Spec == Init /\ [][Next]_<<x, y, b, pc1, pc2, cs>>
WF1(i) == <>[]<>(pc1[i] = "cs")
WF2(i) == <>[]<>(pc2[i] = "cs")

THEOREM Spec => []<>((\E i \in 1..N : (pc1[i] = "cs" \/ pc2[i] = "cs")))
THEOREM Spec => [][](Cardinality(cs) <= 1)
THEOREM Spec => WF1(1) /\ ... /\ WF1(M)
THEOREM Spec => WF2(M+1) /\ ... /\ WF2(N)
```