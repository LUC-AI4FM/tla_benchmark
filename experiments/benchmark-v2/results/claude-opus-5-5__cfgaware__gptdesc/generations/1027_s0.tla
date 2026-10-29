---------------------------- MODULE MC_apalache ----------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the Chang-Roberts leader election         *)
(* algorithm. It holds the type annotations for the constants and          *)
(* variables, and concrete values for the ring size (NVal) and the         *)
(* identifier sequence (IdVal).                                            *)
(*                                                                         *)
(* The original design imports the behavior with "INSTANCE ChangRoberts".  *)
(* That would fail to parse unless ChangRoberts.tla is present. So that    *)
(* this module parses on its own, the ChangRoberts definitions are         *)
(* reproduced below.                                                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Seq(Int);
    Id

VARIABLES
    \* @type: Int -> Set(Int);
    msgs,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Bool;
    initiator,
    \* @type: Int -> Str;
    state

(***************************************************************************)
(* Concrete values used by the model-checking configuration.               *)
(***************************************************************************)
NVal == 3

IdVal == <<3, 1, 2>>

(***************************************************************************)
(* Chang-Roberts behavior (as in module ChangRoberts).                     *)
(***************************************************************************)
Node == 1 .. N

succ(n) == IF n = N THEN 1 ELSE n + 1

vars == << msgs, pc, initiator, state >>

ProcSet == Node

Init ==
    /\ msgs = [n \in Node |-> {}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
    /\ pc = [self \in ProcSet |-> "n0"]

\* Initiators send their own identifier to their successor.
n0(self) ==
    /\ pc[self] = "n0"
    /\ IF initiator[self]
          THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \union {Id[self]}]
          ELSE msgs' = msgs
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED << initiator, state >>

\* Receive an identifier: win on own id, forward smaller ids (and
\* everything when not an initiator), and swallow larger ones.
n1(self) ==
    /\ pc[self] = "n1"
    /\ \E id \in msgs[self] :
          IF id = Id[self]
             THEN /\ state' = [state EXCEPT ![self] = "won"]
                  /\ msgs' = [msgs EXCEPT ![self] = @ \ {id}]
             ELSE IF id < Id[self] \/ ~initiator[self]
                     THEN /\ state' = [state EXCEPT ![self] = "lost"]
                          /\ msgs' = [msgs EXCEPT ![self] = @ \ {id},
                                                  ![succ(self)] = @ \union {id}]
                     ELSE /\ msgs' = [msgs EXCEPT ![self] = @ \ {id}]
                          /\ state' = state
    /\ pc' = pc
    /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

\* Stutter once no messages remain in transit, so the model has no deadlock.
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "n1"
    /\ \A n \in Node : msgs[n] = {}
    /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties.                                                             *)
(***************************************************************************)
TypeOK ==
    /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
    /\ pc \in [Node -> {"n0", "n1"}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state \in [Node -> {"cand", "lost", "won"}]

\* A node that wins must be an initiator holding the smallest identifier
\* among the initiators. This also implies there is at most one winner.
Correctness ==
    \A i \in Node :
        state[i] = "won" =>
            /\ initiator[i]
            /\ \A j \in Node : initiator[j] => Id[i] <= Id[j]

=============================================================================