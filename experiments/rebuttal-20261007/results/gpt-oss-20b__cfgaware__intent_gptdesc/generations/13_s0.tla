------------------------------ MODULE RollingUpdate ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS
  SERVERS,
  Updating,
  Old,
  New

VARIABLES
  serverState,
  lbSet

(* Type invariant *)
TypeInvariant ==
  /\ serverState \in [SERVERS -> {Old, Updating, New}]
  /\ lbSet \subseteq SERVERS

Init ==
  /\ serverState = [s \in SERVERS |-> Old]
  /\ lbSet = SERVERS
  /\ TypeInvariant

ServerStartUpdate(s) ==
  /\ s \in lbSet
  /\ serverState[s] = Old
  /\ serverState' = [serverState EXCEPT ![s] = Updating]

ServerFinishUpdate(s) ==
  /\ s \in SERVERS
  /\ serverState[s] = Updating
  /\ serverState' = [serverState EXCEPT ![s] = New]
  /\ UNCHANGED lbSet

OrchestratorRemoveAndStart(S') ==
  /\ S' \subseteq lbSet
  /\ S' /= {}
  /\ \A s \in S': serverState[s] = Old
  /\ lbSet' = lbSet \ S'
  /\ serverState' = [serverState EXCEPT ![s] = Updating : s \in S']

OrchestratorAddBack(S') ==
  /\ S' \subseteq SERVERS
  /\ S' /= {}
  /\ \A s \in S': serverState[s] = New
  /\ lbSet' = lbSet ∪ S'
  /\ UNCHANGED serverState

Next ==
  \/ \E s \in SERVERS : ServerStartUpdate(s)
  \/ \E s \in SERVERS : ServerFinishUpdate(s)
  \/ \E S' \subseteq SERVERS : OrchestratorRemoveAndStart(S')
  \/ \E S' \subseteq SERVERS : OrchestratorAddBack(S')

Spec == Init /\ [][Next]_{serverState, lbSet}

(* Invariants *)

LoadBalancedHomogeneous ==
  \A s1,s2 \in lbSet : serverState[s1] = serverState[s2]

ZeroDowntime ==
  /\ lbSet /= {}
  /\ \A s \in lbSet : serverState[s] \in {Old, New}

Progress ==
  []<> (\A s \in SERVERS : serverState[s] = New)

===============================================================================