------------------------------ MODULE MCChangRoberts ------------------------------
EXTENDS Naturals

  ---------------------------- MODULE ChangRoberts ----------------------------
  CONSTANTS N, Id

  Node == 1 .. N

  ASSUME /\ N \in Nat
         /\ Id \in [Node -> Nat]
         /\ \A m, n \in Node : m # n => Id[m] # Id[n]

  succ(n) == IF n = N THEN 1 ELSE n + 1

  send(ch, to, id) == [ch EXCEPT ![to] = @ \cup {id}]

  VARIABLES msgs, pc, initiator, state

  vars == << msgs, pc, initiator, state >>

  Init ==
    /\ msgs = [n \in Node |-> {}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
    /\ pc = [self \in Node |-> "n0"]

  n0(self) ==
    /\ pc[self] = "n0"
    /\ IF initiator[self]
          THEN msgs' = send(msgs, succ(self), Id[self])
          ELSE msgs' = msgs
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED << initiator, state >>

  n1(self) ==
    /\ pc[self] = "n1"
    /\ \E id \in msgs[self] :
         LET rmsgs == [msgs EXCEPT ![self] = @ \ {id}]
         IN  IF state[self] = "lost"
                THEN /\ msgs' = send(rmsgs, succ(self), id)
                     /\ state' = state
             ELSE IF id < Id[self]
                THEN /\ msgs' = rmsgs
                     /\ state' = state
             ELSE IF id = Id[self]
                THEN /\ msgs' = rmsgs
                     /\ state' = [state EXCEPT ![self] = "won"]
             ELSE /\ msgs' = send(rmsgs, succ(self), id)
                  /\ state' = [state EXCEPT ![self] = "lost"]
    /\ pc' = pc
    /\ UNCHANGED initiator

  node(self) == n0(self) \/ n1(self)

  Next == \E self \in Node : node(self)

  Spec == /\ Init
          /\ [][Next]_vars
          /\ \A self \in Node : WF_vars(node(self))

  TypeOK ==
    /\ msgs \in [Node -> SUBSET Nat]
    /\ pc \in [Node -> {"n0", "n1"}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state \in [Node -> {"cand", "lost", "won"}]

  Correctness ==
    \A n \in Node : state[n] = "won" =>
       /\ initiator[n]
       /\ \A m \in Node \ {n} : state[m] = "lost"
       /\ \A m \in Node : initiator[m] => Id[n] <= Id[m]

  Liveness ==
    (\E n \in Node : initiator[n]) ~> (\E n \in Node : state[n] = "won")
  =============================================================================