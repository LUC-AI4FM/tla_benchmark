------------------------------ MODULE LiveSpec ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Values, ProcSet

VARIABLES chosen, proposals

\* Special value representing no proposal or no choice
None == [ ]

Init ==
  /\ chosen = None
  /\ proposals \in [ProcSet -> Values ∪ {None}]
  /\ \A p \in ProcSet : proposals[p] = None

Propose(p, v) ==
  /\ p \in ProcSet
  /\ v \in Values
  /\ proposals[p] = None
  /\ proposals' = [proposals EXCEPT ![p] = v]
  /\ chosen' = chosen

Learn(v) ==
  /\ chosen = None
  /\ v \in Values
  /\ \E p \in ProcSet : proposals[p] = v
  /\ chosen' = v
  /\ proposals' = proposals

Next ==
  (\E p \in ProcSet, v \in Values : Propose(p, v))
  \/ (\E v \in Values : Learn(v))

Spec == Init /\ [][Next]_{chosen, proposals}

Validity ==
  chosen = None \/ chosen \in Values

Integrity ==
  [] (chosen ≠ None => chosen' = chosen)

EventualChoice ==
  []<>(chosen ≠ None)

THEOREM Validity_I == Spec => []Validity
THEOREM Integrity_I == Spec => Integrity
THEOREM EventualChoice_L == (Spec ∧ WF_Learn) => EventualChoice

END MODULE