---------------------------- MODULE MC_ChangRoberts ----------------------------
(***************************************************************************)
(* Apalache-oriented model of the Chang-Roberts ring leader election      *)
(* algorithm for N processes. The algorithm is inlined here so the module *)
(* is self-contained. Fairness is omitted because Apalache does not check *)
(* liveness properties.                                                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Seq(Int);
    Id

\* Concrete values used for the constants in the model
NVal == 3
IdVal == <<3, 1, 2>>

VARIABLES
    \* @type: Int -> Set(Int);
    msgs,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    initiator,
    \* @type: Int -> Str;
    state

vars == << msgs, pc, initiator, state >>

Node == 1 .. N

succ(n) == IF n = N THEN 1 ELSE n + 1

\* @type: Set(Int) => Int;
max(S) == CHOOSE x \in S : \A y \in S : y <= x

Init ==
    /\ msgs = [n \in Node |-> {}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
    /\ pc = [self \in Node |-> "n0"]

\* A process that is an initiator sends its own identifier to its successor
n0(self) ==
    /\ pc[self] = "n0"
    /\ IF initiator[self]
          THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
          ELSE msgs' = msgs
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED << initiator, state >>

\* A process receives an identifier and reacts to it
n1(self) ==
    /\ pc[self] = "n1"
    /\ \E id \in msgs[self] :
          LET rest == [msgs EXCEPT ![self] = @ \ {id}]
          IN  IF state[self] = "lost"
                 THEN /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                      /\ state' = state
              ELSE IF id < Id[self]
                 THEN /\ msgs' = rest
                      /\ state' = state
              ELSE IF id = Id[self]
                 THEN /\ msgs' = rest
                      /\ state' = [state EXCEPT ![self] = "won"]
              ELSE /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                   /\ state' = [state EXCEPT ![self] = "lost"]
    /\ pc' = pc
    /\ initiator' = initiator

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
    /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
    /\ pc \in [Node -> {"n0", "n1"}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state \in [Node -> {"cand", "lost", "won"}]

Correctness ==
    \A n \in Node :
        state[n] = "won" =>
            /\ initiator[n]
            /\ Id[n] = max({Id[m] : m \in {p \in Node : initiator[p]}})

=============================================================================