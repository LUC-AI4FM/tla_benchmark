---------------------------- MODULE Fingerprint ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

S == {1}
T == {2, 3, 4}

R == [a : {1, 2}, b : {1, 2}]

Init ==
  /\ PrintT("Number of distinct states should equal number of distinct initial states")
  /\ x \in [S -> [S -> SUBSET T]]
  /\ y \in [S -> [S -> SUBSET R]]

Next ==
  \/ UNCHANGED <<x, y>>
  \/ /\ x' = [i \in S |-> [j \in S |-> {2, 3, 2, 3}]]
     /\ UNCHANGED y
  \/ /\ y' = [i \in S |-> [j \in S |-> {[a |-> 1, b |-> 2],
                                        [b |-> 2, a |-> 1],
                                        [a |-> 1, b |-> 2]}]]
     /\ UNCHANGED x
  \/ /\ y' = [y EXCEPT ![1][1] = {[a |-> 1, b |-> 1]}]
     /\ UNCHANGED x
  \/ /\ y' = [y EXCEPT ![1][1] = {[b |-> 2, a |-> 2]}]
     /\ UNCHANGED x

Inv ==
  Assert(
    /\ {2, 3, 3, 2} = {3, 2}
    /\ {[a |-> 1, b |-> 2], [b |-> 2, a |-> 1]} = {[a |-> 1, b |-> 2]}
    /\ [i \in S |-> {[a |-> 1, b |-> 1], [a |-> 1, b |-> 1]}]
         = [i \in S |-> {[b |-> 1, a |-> 1]}]
    /\ [i \in S |-> [j \in S |-> {4, 2, 4}]]
         = [i \in S |-> [j \in S |-> {2, 4}]],
    "Fingerprint test failed: equivalent expressions differ")

=============================================================================