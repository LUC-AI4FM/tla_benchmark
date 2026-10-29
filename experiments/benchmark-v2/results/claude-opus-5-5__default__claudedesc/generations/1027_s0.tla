------------------------------- MODULE ApaChangRoberts -------------------------------
(***************************************************************************)
(* Apalache-typed version of the Chang-Roberts ring-based leader election  *)
(* algorithm for N processes. Each process carries a unique identifier and *)
(* the process holding the highest identifier among the initiators is      *)
(* elected leader. Type annotations follow Apalache's comment syntax.      *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Seq(Int);
    Id

\* Apalache constant initialization: N = 3, Id = permutation <<3, 1, 2>>
ConstInit ==
    /\ N = 3
    /\ Id = <<3, 1, 2>>

Node == 1 .. N

ASSUME
    /\ N \in Nat \ {0}
    /\ Id \in Seq(Nat)
    /\ Len(Id) = N
    /\ \A m, n \in Node : m # n => Id[m] # Id[n]

\* successor of a node on the ring
succ(n) == IF n = N THEN 1 ELSE n + 1

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

Init ==
    /\ msgs = [n \in Node |-> {}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state = [n \in Node |-> "cand"]
    /\ pc = [n \in Node |-> "n0"]

\* Initiators send their own identifier to their successor.
n0(self) ==
    /\ pc[self] = "n0"
    /\ IF initiator[self]
          THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \union {Id[self]}]
          ELSE msgs' = msgs
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED << initiator, state >>

\* Receive a message: win if own id returns, forward and lose if a larger
\* id is received, discard smaller ids.
n1(self) ==
    /\ pc[self] = "n1"
    /\ \E id \in msgs[self] :
         IF id = Id[self]
            THEN /\ state' = [state EXCEPT ![self] = "won"]
                 /\ msgs' = [msgs EXCEPT ![self] = @ \ {id}]
            ELSE IF id > Id[self]
                    THEN /\ state' = [state EXCEPT ![self] = "lost"]
                         /\ msgs' = [msgs EXCEPT ![self] = @ \ {id},
                                                 ![succ(self)] = @ \union {id}]
                    ELSE /\ msgs' = [msgs EXCEPT ![self] = @ \ {id}]
                         /\ state' = state
    /\ pc' = pc
    /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

\* Fairness conditions are omitted: Apalache does not check liveness.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
    /\ pc \in [Node -> {"n0", "n1"}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state \in [Node -> {"cand", "lost", "won"}]

\* Safety: a winner is an initiator, is unique, and has the largest
\* identifier among all initiators.
Correctness ==
    \A n \in Node :
        state[n] = "won" =>
            /\ initiator[n]
            /\ \A m \in Node \ {n} :
                  /\ state[m] # "won"
                  /\ (initiator[m] => Id[m] < Id[n])

THEOREM Spec => [](TypeOK /\ Correctness)
=============================================================================