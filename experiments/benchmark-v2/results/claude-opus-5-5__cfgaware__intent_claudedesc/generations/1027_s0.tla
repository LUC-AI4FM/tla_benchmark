---- MODULE ChangRoberts ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, Id

NVal == 6
IdVal == <<27, 4, 42, 15, 63, 9>>

Node == 1 .. N

succ(n) == IF n = N THEN 1 ELSE n + 1

IdSet == { Id[n] : n \in Node }

ASSUME /\ N \in Nat \ {0}
       /\ \A n \in Node : Id[n] \in Nat
       /\ \A m, n \in Node : m # n => Id[m] # Id[n]

VARIABLES initiator, state, msgs

vars == << initiator, state, msgs >>

TypeOK ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cho", "lost", "won"}]
  /\ msgs \in [Node -> SUBSET IdSet]

Init ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ state = [n \in Node |-> IF initiator[n] THEN "cho" ELSE "lost"]
  /\ msgs = [n \in Node |->
               { Id[m] : m \in { k \in Node : initiator[k] /\ succ(k) = n } }]

Receive(n) ==
  \E id \in msgs[n] :
    LET rest == [msgs EXCEPT ![n] = @ \ {id}]
        fwd  == [rest EXCEPT ![succ(n)] = @ \cup {id}]
    IN
    /\ initiator' = initiator
    /\ IF state[n] = "lost"
         THEN /\ msgs' = fwd
              /\ state' = state
         ELSE IF id < Id[n]
                THEN /\ state' = [state EXCEPT ![n] = "lost"]
                     /\ msgs' = fwd
                ELSE /\ msgs' = rest
                     /\ IF id = Id[n]
                          THEN state' = [state EXCEPT ![n] = "won"]
                          ELSE state' = state

Next == \E n \in Node : Receive(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Node : WF_vars(Receive(n))

UniqueLeader ==
  \A m, n \in Node : (state[m] = "won" /\ state[n] = "won") => m = n

Correctness ==
  /\ UniqueLeader
  /\ \A n \in Node :
       state[n] = "won" =>
         /\ initiator[n]
         /\ \A m \in Node : (initiator[m] /\ m # n) => Id[n] < Id[m]

Liveness ==
  (\E n \in Node : initiator[n]) => <>(\E n \in Node : state[n] = "won")

====