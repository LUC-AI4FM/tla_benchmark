---------------------------- MODULE APAChangRoberts ----------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the Chang-Roberts leader election         *)
(* algorithm. It gives type annotations for the constants and variables,   *)
(* and concrete values (NVal, IdVal) for the parameters.                   *)
(*                                                                         *)
(* The original design imports the behavior with INSTANCE ChangRoberts.    *)
(* That would make SANY depend on a separate ChangRoberts.tla file. So     *)
(* that this module parses on its own, the ChangRoberts behavior is        *)
(* written out inline below instead.                                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

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
(* Concrete values for the constants (Apalache / TLC substitution).        *)
(***************************************************************************)
NVal == 3

IdVal == <<3, 1, 2>>

(***************************************************************************)
(* Chang-Roberts behavior (inlined from the ChangRoberts module).          *)
(***************************************************************************)
vars == <<msgs, pc, initiator, state>>

Node == 1 .. N

succ(n) == IF n = N THEN 1 ELSE n + 1

ASSUME
  /\ N \in Nat \ {0}
  /\ Id \in Seq(Nat)
  /\ Len(Id) = N
  /\ \A m, n \in Node : m # n => Id[m] # Id[n]

Init ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ msgs = [n \in Node |-> {}]
  /\ state = [n \in Node |-> "cand"]
  /\ pc = [n \in Node |-> "n0"]

\* An initiator sends its own identifier to its successor.
n0(self) ==
  /\ pc[self] = "n0"
  /\ IF initiator[self]
       THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
       ELSE UNCHANGED msgs
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED <<initiator, state>>

\* A node receives an identifier and either wins, discards it, or
\* forwards it and loses.
n1(self) ==
  /\ pc[self] = "n1"
  /\ \E id \in msgs[self] :
       LET rest == [msgs EXCEPT ![self] = @ \ {id}] IN
       IF id = Id[self]
         THEN /\ state' = [state EXCEPT ![self] = "won"]
              /\ msgs' = rest
         ELSE IF initiator[self] /\ id > Id[self]
                THEN /\ msgs' = rest
                     /\ UNCHANGED state
                ELSE /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                     /\ state' = [state EXCEPT ![self] = "lost"]
  /\ UNCHANGED <<pc, initiator>>

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Node : WF_vars(node(self))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ pc \in [Node -> {"n0", "n1"}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

Correctness ==
  \A n \in Node :
    state[n] = "won" =>
      /\ initiator[n]
      /\ \A m \in Node : m # n => state[m] = "lost"

Liveness == (\E n \in Node : initiator[n]) ~> (\E n \in Node : state[n] = "won")

=============================================================================