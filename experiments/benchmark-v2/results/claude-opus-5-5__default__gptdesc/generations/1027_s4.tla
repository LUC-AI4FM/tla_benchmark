------------------------------ MODULE MC_ChangRoberts ------------------------------
(***************************************************************************)
(* Apalache-oriented wrapper for the Chang-Roberts leader election         *)
(* specification. Type annotations and concrete constant values live here. *)
(* The behavior is imported from the ChangRoberts module through INSTANCE  *)
(* and is not redefined. ChangRoberts is given below as a nested module so *)
(* that this file is self-contained.                                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences

    ------------------------------ MODULE ChangRoberts ------------------------------
    (***********************************************************************)
    (* Chang-Roberts leader election on a unidirectional ring. The node    *)
    (* with the smallest identifier is elected leader.                     *)
    (***********************************************************************)
    EXTENDS Naturals, Sequences

    CONSTANTS N, Id

    Node == 1 .. N

    ASSUME
      /\ N \in Nat \ {0}
      /\ Id \in Seq(Nat)
      /\ Len(Id) = N
      /\ \A m, n \in Node : m # n => Id[m] # Id[n]

    succ(n) == IF n = N THEN 1 ELSE n + 1

    VARIABLES msgs, pc, initiator, state

    vars == << msgs, pc, initiator, state >>

    ProcSet == Node

    Init ==
      /\ initiator \in [Node -> BOOLEAN]
      /\ msgs = [n \in Node |-> {}]
      /\ state = [self \in Node |-> "cand"]
      /\ pc = [self \in ProcSet |-> "n0"]

    n0(self) ==
      /\ pc[self] = "n0"
      /\ IF initiator[self]
            THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
            ELSE msgs' = msgs
      /\ pc' = [pc EXCEPT ![self] = "n1"]
      /\ UNCHANGED << initiator, state >>

    n1(self) ==
      /\ pc[self] = "n1"
      /\ \E id \in msgs[self] :
           LET rest == [msgs EXCEPT ![self] = @ \ {id}] IN
           IF state[self] = "lost"
              THEN /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                   /\ state' = state
              ELSE IF id < Id[self]
                      THEN /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                           /\ state' = [state EXCEPT ![self] = "lost"]
                      ELSE IF id = Id[self]
                              THEN /\ msgs' = rest
                                   /\ state' = [state EXCEPT ![self] = "won"]
                              ELSE /\ IF state[self] = "cand" /\ ~initiator[self]
                                         THEN msgs' = [rest EXCEPT ![succ(self)] = @ \cup {Id[self]}]
                                         ELSE msgs' = rest
                                   /\ state' = state
      /\ pc' = [pc EXCEPT ![self] = "n1"]
      /\ UNCHANGED initiator

    node(self) == n0(self) \/ n1(self)

    Next == \E self \in Node : node(self)

    Spec == /\ Init
            /\ [][Next]_vars
            /\ \A self \in Node : WF_vars(node(self))

    TypeOK ==
      /\ initiator \in [Node -> BOOLEAN]
      /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
      /\ pc \in [Node -> {"n0", "n1"}]
      /\ state \in [Node -> {"cand", "lost", "won"}]

    Correctness ==
      \A n \in Node : state[n] = "won" =>
         /\ \A m \in Node \ {n} : state[m] = "lost" /\ Id[n] < Id[m]

    Liveness == (\E n \in Node : initiator[n]) => <>(\E n \in Node : state[n] = "won")
    ==================================================================================