-------------------------- MODULE DijkstraTokenRing --------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, M

ASSUME  /\ N \in 1..Nat
        /\ M \in 1..Nat
        /\ N <= M + 1

VARIABLES x

--------------------------------- ALGORITHM ----------------------------------

Nodes == 0..N-1
Values == 0..M-1

(* The predecessor of node i in the ring *)
Pred(i) == (i - 1 + N) % N

vars == <<x>>

(* The state is well-typed if x is a function from nodes to values. *)
TypeOK == x \in [Nodes -> Values]

(* The system can start in any state, as it is self-stabilizing. *)
Init == TypeOK

(* The "bottom" process (node 0) is special. When its value is the same as its
   predecessor's, it increments its value modulo M. This creates a "token". *)
BottomAction ==
    /\ x[0] = x[Pred(0)]
    /\ x' = [x EXCEPT ![0] = (x[Pred(0)] + 1) % M]

(* A "normal" process (node i > 0) copies its predecessor's value when its
   own value is different. This "passes" the token. *)
NormalAction(i) ==
    /\ i \in 1..N-1
    /\ x[i] # x[Pred(i)]
    /\ x' = [x EXCEPT ![i] = x[Pred(i)]]

(* A next state is reached by either the bottom process moving or one of the
   normal processes moving. *)
Next ==
    \/ BottomAction
    \/ \E i \in 1..N-1 : NormalAction(i)

(* The main safety specification. *)
Spec == Init /\ [][Next]_vars

-------------------------------- PROPERTIES ----------------------------------

(* Fairness: Each process that is continuously enabled must eventually take a step. *)
Fairness ==
    /\ WF_vars(BottomAction)
    /\ \A i \in 1..N-1 : WF_vars(NormalAction(i))

(* A token is defined to exist at process i if its value differs from its predecessor's. *)
IsToken(i) == x[i] # x[Pred(i)]

(* The set of all processes that hold a token. *)
TokenSet == {i \in Nodes : IsToken(i)}

(* The desired legitimate state is one where there is exactly one token in the ring. *)
UniqueToken == Cardinality(TokenSet) = 1

(* The stabilization property: eventually, the system reaches a state with
   exactly one token, and remains in such states thereafter. *)
Stabilization == <>[]UniqueToken

=============================================================================