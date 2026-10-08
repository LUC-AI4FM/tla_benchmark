------------------------------- MODULE LockProtocol -------------------------------

EXTENDS Integers, TLC, FiniteSets

CONSTANTS N \* Number of processes

VARIABLES turn, h_turn, s, request, critical

Init == 
  /\ turn = 0
  /\ h_turn = << >>
  /\ s = FALSE
  /\ request = [p \in 1..N -> FALSE]
  /\ critical = [p \in 1..N -> FALSE]

Next ==
  \/ \E p \in 1..N \LAMBDA <<turn', h_turn', s', request', critical' >> :
     /\ turn' = turn
     /\ h_turn' = h_turn
     /\ s' = TRUE
     /\ request' = [request EXCEPT ![p] = TRUE]
     /\ critical' = critical
  \/ \E p \in 1..N \LAMBDA <<turn', h_turn', s', request', critical' >> :
     /\ turn' = p
     /\ h_turn' = Append(h_turn, p)
     /\ s' = FALSE
     /\ request' = request
     /\ critical' = [critical EXCEPT ![p] = TRUE]
  \/ \E p \in 1..N \LAMBDA <<turn', h_turn', s', request', critical' >> :
     /\ turn' = (IF turn = p THEN CHOOSE q \in {1..N} \ {p} : request[q] ELSE turn)
     /\ h_turn' = Append(h_turn, turn')
     /\ s' = FALSE
     /\ request' = [request EXCEPT ![p] = FALSE]
     /\ critical' = [critical EXCEPT ![p] = FALSE]

Spec ==
  INIT Init
  /\ \A state \in Seq(Init) : \E trace \in StateTrace(state) :
    \A i \in Indices(trace) :
      \/ s[trace[i]] => /\ Next[trace[i], trace[i+1]]
                       /\ critical[trace[i]] = critical[trace[i+1]]
      \/ ~s[trace[i]] => /\ Next[trace[i], trace[i+1]]
                         /\ request[trace[i]] = request[trace[i+1]]

Invariant ==
  /\ \A p \in 1..N : critical[p] => turn = p
  /\ \A p, q \in 1..N \ {p} : critical[p] => ~critical[q]
  /\ \A p \in 1..N : h_turn = << >> \/ Last(h_turn) \in 1..N

Liveness ==
  WF_next(\A p \in 1..N: request[p])

Fairness ==
  SF_\E(p \in 1..N)(request[p] => critical[p])

=============================================================================